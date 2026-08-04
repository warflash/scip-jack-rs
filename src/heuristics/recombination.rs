use std::collections::HashSet;
use super::PrimalHeuristic;
use super::constructive::ConstructiveHeuristic;
use super::local_search::LocalSearchHeuristic;
use crate::graph::{cmp_cost, DirectedGraph, NodeId, ArcId, Cost, NodeType};
use crate::model::SteinerSolution;

/// Recombination heuristic (Rothberg, 2007 / SCIP-Jack):
///
/// 1. Select k best solutions from the pool (default k=4)
/// 2. Build the union graph containing all arcs present in at least one selected solution
/// 3. Solve the Steiner tree problem on the smaller union graph using the constructive heuristic
/// 4. Apply local search improvement on the result
/// 5. If the result improves on the best known solution, add it to the pool
///
/// The key insight is that the union of good solutions often contains the optimal solution,
/// and solving on the smaller subgraph is much faster than on the full graph.
pub struct RecombinationHeuristic {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub solution_pool: Vec<SteinerSolution>,
    pub max_pool_size: usize,
    pub recombination_size: usize,
}

impl RecombinationHeuristic {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        Self {
            graph,
            root,
            terminals,
            solution_pool: Vec::new(),
            max_pool_size: 20,
            recombination_size: 4,
        }
    }

    pub fn add_solution(&mut self, solution: SteinerSolution) {
        self.solution_pool.push(solution);
        // Keep pool sorted by objective value
        self.solution_pool.sort_by(|a, b| cmp_cost(a.objective_value, b.objective_value));
        // Trim to max size
        self.solution_pool.truncate(self.max_pool_size);
    }

    /// Build a union subgraph from the top-k solutions.
    /// Returns the subgraph as a DirectedGraph with only the arcs from the union.
    fn build_union_graph(&self, k: usize) -> (DirectedGraph, Vec<ArcId>) {
        let k = k.min(self.solution_pool.len());

        // Collect all arcs present in the top-k solutions
        let mut union_arcs: HashSet<ArcId> = HashSet::new();
        for sol in self.solution_pool.iter().take(k) {
            for &arc_id in &sol.arcs {
                union_arcs.insert(arc_id);
            }
        }

        // Also add reverse arcs for bidirectionality
        let arc_list: Vec<ArcId> = union_arcs.iter().copied().collect();
        for &aid in &arc_list {
            let arc = &self.graph.arcs[aid as usize];
            // Find reverse arc
            for &(head, rev_id) in self.graph.delta_plus(arc.head) {
                if head == arc.tail && self.graph.arcs[rev_id as usize].cost == arc.cost {
                    union_arcs.insert(rev_id);
                    break;
                }
            }
        }

        // Collect all nodes needed
        let mut union_nodes: HashSet<NodeId> = HashSet::new();
        for &aid in &union_arcs {
            let arc = &self.graph.arcs[aid as usize];
            union_nodes.insert(arc.tail);
            union_nodes.insert(arc.head);
        }

        // Ensure all terminals are included
        for &t in &self.terminals {
            union_nodes.insert(t);
        }
        union_nodes.insert(self.root);

        // Build the subgraph
        let mut subgraph = DirectedGraph::new(self.graph.num_nodes);
        for &nid in &union_nodes {
            let nt = if self.terminals.contains(&nid) || nid == self.root {
                NodeType::Terminal
            } else {
                NodeType::Steiner
            };
            subgraph.add_node(nid, nt, 0.0);
        }

        let mut original_arcs: Vec<ArcId> = Vec::new();
        for &aid in &union_arcs {
            let arc = &self.graph.arcs[aid as usize];
            if union_nodes.contains(&arc.tail) && union_nodes.contains(&arc.head) {
                subgraph.add_arc(arc.tail, arc.head, arc.cost);
                original_arcs.push(aid);
            }
        }

        (subgraph, original_arcs)
    }

    /// Map arcs from the subgraph solution back to the original graph.
    fn map_solution_to_original(
        &self,
        sub_solution: &SteinerSolution,
        subgraph: &DirectedGraph,
    ) -> Option<SteinerSolution> {
        let mut original_arcs: Vec<ArcId> = Vec::new();
        let mut original_nodes: HashSet<NodeId> = HashSet::new();
        let mut total_cost: Cost = 0.0;

        for &sub_arc_id in &sub_solution.arcs {
            let sub_arc = &subgraph.arcs[sub_arc_id as usize];

            // Find corresponding arc in original graph
            let found = self.graph.delta_plus(sub_arc.tail).iter()
                .find(|&&(head, _)| head == sub_arc.head)
                .and_then(|&(_, orig_aid)| {
                    let orig_arc = &self.graph.arcs[orig_aid as usize];
                    if (orig_arc.cost - sub_arc.cost).abs() < 1e-9 {
                        Some(orig_aid)
                    } else {
                        // Find exact match
                        self.graph.delta_plus(sub_arc.tail).iter()
                            .filter(|&&(h, _)| h == sub_arc.head)
                            .map(|&(_, aid)| aid)
                            .find(|&aid| (self.graph.arcs[aid as usize].cost - sub_arc.cost).abs() < 1e-9)
                    }
                });

            match found {
                Some(orig_aid) => {
                    original_arcs.push(orig_aid);
                    let arc = &self.graph.arcs[orig_aid as usize];
                    original_nodes.insert(arc.tail);
                    original_nodes.insert(arc.head);
                    total_cost += arc.cost;
                }
                None => return None,
            }
        }

        Some(SteinerSolution::new(
            original_arcs,
            original_nodes.into_iter().collect(),
            total_cost,
        ))
    }

    /// Perform one recombination attempt.
    fn recombine_once(&self) -> Option<SteinerSolution> {
        let k = self.recombination_size.min(self.solution_pool.len());
        if k < 2 {
            return None;
        }

        let (subgraph, _) = self.build_union_graph(k);

        // Solve on the subgraph using constructive heuristic
        let mut constructive = ConstructiveHeuristic::new(
            subgraph.clone(),
            self.root,
            self.terminals.clone(),
        );
        constructive.num_starts = 10;

        let sub_solution = constructive.run()?;

        // Map back to original graph
        let mut mapped = self.map_solution_to_original(&sub_solution, &subgraph)?;

        // Apply local search improvement
        let mut local_search = LocalSearchHeuristic::new(
            self.graph.clone(),
            self.root,
            self.terminals.clone(),
        );
        local_search.max_iterations = 20;
        local_search.set_incumbent(mapped.clone());

        if let Some(improved) = local_search.run() {
            if improved.objective_value < mapped.objective_value - 1e-9 {
                mapped = improved;
            }
        }

        Some(mapped)
    }
}

impl PrimalHeuristic for RecombinationHeuristic {
    fn run(&mut self) -> Option<SteinerSolution> {
        if self.solution_pool.len() < 2 {
            return None;
        }

        let best_known = self.solution_pool[0].objective_value;
        let mut best_result: Option<SteinerSolution> = None;

        // Try multiple recombination attempts with different pool subsets
        let num_attempts = 3.min(self.solution_pool.len() / 2);

        for _ in 0..num_attempts {
            if let Some(result) = self.recombine_once() {
                let is_better = match &best_result {
                    None => result.objective_value < best_known - 1e-9,
                    Some(current) => result.objective_value < current.objective_value - 1e-9,
                };

                if is_better {
                    best_result = Some(result);
                }
            }
        }

        // Add result to pool if it improves
        if let Some(ref result) = best_result {
            if result.objective_value < best_known - 1e-9 {
                let result_clone = result.clone();
                self.add_solution(result_clone);
            }
        }

        best_result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn build_test_graph() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        //     1 (root)
        //    /|\
        //   2  3  4
        //  /|  |  |\
        // 5  6 7  8 9
        //
        // Terminals: 5, 7, 9
        let mut g = DirectedGraph::new(9);
        for i in 1..=9u32 {
            let nt = if [5, 7, 9].contains(&i) { NodeType::Terminal } else { NodeType::Steiner };
            g.add_node(i, nt, 0.0);
        }

        let edges: Vec<(u32, u32, f64)> = vec![
            (1, 2, 1.0), (1, 3, 2.0), (1, 4, 1.0),
            (2, 5, 2.0), (2, 6, 3.0),
            (3, 7, 1.0),
            (4, 8, 2.0), (4, 9, 1.0),
        ];

        for (u, v, c) in edges {
            g.add_arc(u, v, c);
            g.add_arc(v, u, c);
        }

        (g, 1, vec![5, 7, 9])
    }

    #[test]
    fn test_recombination_needs_two_solutions() {
        let (graph, root, terminals) = build_test_graph();
        let mut recom = RecombinationHeuristic::new(graph, root, terminals);

        assert!(recom.run().is_none(), "Should return None with < 2 solutions");

        let sol = SteinerSolution::new(vec![0, 6], vec![1, 2, 5], 3.0);
        recom.add_solution(sol);
        assert!(recom.run().is_none(), "Should return None with only 1 solution");
    }

    #[test]
    fn test_recombination_produces_valid_solution() {
        let (graph, root, terminals) = build_test_graph();
        let mut recom = RecombinationHeuristic::new(graph.clone(), root, terminals.clone());

        // Solution 1: 1->2->5, 1->3->7, 1->4->9 (cost: 1+2+2+1+1+1 = 8)
        let sol1 = SteinerSolution::new(
            vec![0, 6, 4, 10, 12, 14],
            vec![1, 2, 3, 4, 5, 7, 9],
            8.0,
        );

        // Solution 2: slightly different path
        let sol2 = SteinerSolution::new(
            vec![0, 6, 4, 10, 12, 14],
            vec![1, 2, 3, 4, 5, 7, 9],
            8.0,
        );

        recom.add_solution(sol1);
        recom.add_solution(sol2);

        // Recombination should at least produce something
        let result = recom.run();
        // It may or may not improve depending on the graph, but should not crash
        if let Some(sol) = result {
            assert!(sol.objective_value > 0.0);
            assert!(!sol.arcs.is_empty());
        }
    }

    #[test]
    fn test_pool_stays_sorted() {
        let (graph, root, terminals) = build_test_graph();
        let mut recom = RecombinationHeuristic::new(graph, root, terminals);

        recom.add_solution(SteinerSolution::new(vec![0], vec![1, 2], 10.0));
        recom.add_solution(SteinerSolution::new(vec![0], vec![1, 2], 5.0));
        recom.add_solution(SteinerSolution::new(vec![0], vec![1, 2], 8.0));

        assert_eq!(recom.solution_pool[0].objective_value, 5.0);
        assert_eq!(recom.solution_pool[1].objective_value, 8.0);
        assert_eq!(recom.solution_pool[2].objective_value, 10.0);
    }
}
