use std::collections::HashSet;
use super::PrimalHeuristic;
use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use crate::graph::algorithms::ShortestPathResult;
use crate::model::SteinerSolution;

/// Shortest-path-based constructive heuristic (Takahashi & Matsuyama, 1980).
///
/// Algorithm:
/// 1. Start with one vertex (preferably a terminal)
/// 2. In each step, find the nearest unspanned terminal to the current tree
/// 3. Add the shortest path from the tree to that terminal
/// 4. Repeat until all terminals are spanned
/// 5. Pruning: remove degree-1 non-terminal nodes iteratively
///
/// Enhancements from SCIP-Jack:
/// - During branch-and-cut, uses altered arc costs: (1 - y_a) * c(a)
///   to bias towards arcs in the LP solution
/// - Started from multiple vertices (100 initial, 10 after each LP)
/// - Terminals preferred as starting points
pub struct ConstructiveHeuristic {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub num_starts: u32,
    pub lp_weights: Option<Vec<f64>>,
}

impl ConstructiveHeuristic {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        Self {
            graph,
            root,
            terminals,
            num_starts: 100,
            lp_weights: None,
        }
    }

    pub fn with_lp_weights(mut self, weights: Vec<f64>) -> Self {
        self.lp_weights = Some(weights);
        self.num_starts = 10;
        self
    }

    pub fn with_num_starts(mut self, n: u32) -> Self {
        self.num_starts = n;
        self
    }

    /// Compute effective arc costs, optionally incorporating LP solution bias.
    fn effective_costs(&self) -> Vec<Cost> {
        match &self.lp_weights {
            Some(y) => {
                self.graph.arcs.iter().enumerate().map(|(i, arc)| {
                    (1.0 - y[i]).max(1e-6) * arc.cost
                }).collect()
            }
            None => self.graph.arcs.iter().map(|a| a.cost).collect(),
        }
    }

    /// Run a single constructive heuristic iteration from a given start node.
    ///
    /// The algorithm grows a tree from the start node, greedily connecting
    /// the nearest unspanned terminal at each step via the shortest path.
    fn construct_from(&self, start: NodeId, costs: &[Cost]) -> Option<SteinerSolution> {
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();

        if terminal_set.is_empty() {
            return None;
        }

        // Track which terminals are already spanned
        let mut unspanned: HashSet<NodeId> = terminal_set.clone();
        // Nodes currently in the tree
        let mut tree_nodes: HashSet<NodeId> = HashSet::new();
        // Arcs in the solution
        let mut tree_arcs: HashSet<ArcId> = HashSet::new();

        // Initialize: start node is in the tree
        tree_nodes.insert(start);
        unspanned.remove(&start);

        // Grow tree until all terminals are spanned
        while !unspanned.is_empty() {
            let mut best_terminal: Option<NodeId> = None;
            let mut best_distance = f64::INFINITY;
            let mut best_path: Option<Vec<ArcId>> = None;

            // For each node in the current tree, compute shortest paths to find
            // the nearest unspanned terminal.
            // Optimization: compute shortest paths from all tree nodes simultaneously
            // by using a multi-source Dijkstra (insert all tree nodes with distance 0).
            let sp_result = multi_source_dijkstra(&self.graph, &tree_nodes, costs);

            for &terminal in &unspanned {
                let dist = sp_result.distances[terminal as usize];
                if dist < best_distance {
                    best_distance = dist;
                    best_terminal = Some(terminal);
                    best_path = sp_result.path_to(terminal);
                }
            }

            match (best_terminal, best_path) {
                (Some(terminal), Some(path)) => {
                    // Add all arcs and nodes on the path to the tree
                    for &arc_id in &path {
                        let arc = &self.graph.arcs[arc_id as usize];
                        tree_arcs.insert(arc_id);
                        tree_nodes.insert(arc.tail);
                        tree_nodes.insert(arc.head);
                    }
                    unspanned.remove(&terminal);

                    // Also remove any other terminals that happen to be on the path
                    let path_nodes: HashSet<NodeId> = path.iter()
                        .flat_map(|&aid| {
                            let arc = &self.graph.arcs[aid as usize];
                            vec![arc.tail, arc.head]
                        })
                        .collect();
                    for node in &path_nodes {
                        unspanned.remove(node);
                    }
                }
                _ => {
                    // Cannot reach remaining terminals — infeasible from this start
                    return None;
                }
            }
        }

        // Pruning: remove degree-1 Steiner nodes iteratively
        let (pruned_arcs, pruned_nodes) = self.prune_tree(&tree_arcs, &terminal_set);

        // Compute objective value
        let obj: Cost = pruned_arcs.iter()
            .map(|&aid| self.graph.arcs[aid as usize].cost)
            .sum();

        Some(SteinerSolution::new(
            pruned_arcs.into_iter().collect(),
            pruned_nodes.into_iter().collect(),
            obj,
        ))
    }

    /// Remove degree-1 Steiner (non-terminal) nodes from the tree iteratively.
    fn prune_tree(
        &self,
        tree_arcs: &HashSet<ArcId>,
        terminals: &HashSet<NodeId>,
    ) -> (HashSet<ArcId>, HashSet<NodeId>) {
        let mut arcs: HashSet<ArcId> = tree_arcs.clone();
        let mut nodes: HashSet<NodeId> = HashSet::new();

        // Collect all nodes in the tree
        for &arc_id in &arcs {
            let arc = &self.graph.arcs[arc_id as usize];
            nodes.insert(arc.tail);
            nodes.insert(arc.head);
        }

        let mut changed = true;
        while changed {
            changed = false;
            let current_nodes: Vec<NodeId> = nodes.iter().copied().collect();

            for &node in &current_nodes {
                if terminals.contains(&node) || node == self.root {
                    continue;
                }

                // Count arcs incident to this node in the current tree
                let incident: Vec<ArcId> = arcs.iter()
                    .copied()
                    .filter(|&aid| {
                        let arc = &self.graph.arcs[aid as usize];
                        arc.tail == node || arc.head == node
                    })
                    .collect();

                // Degree-1 Steiner node: remove it and its incident arc
                if incident.len() <= 1 {
                    nodes.remove(&node);
                    for aid in incident {
                        arcs.remove(&aid);
                    }
                    changed = true;
                }
            }
        }

        (arcs, nodes)
    }
}

impl PrimalHeuristic for ConstructiveHeuristic {
    fn run(&mut self) -> Option<SteinerSolution> {
        let costs = self.effective_costs();
        let mut best: Option<SteinerSolution> = None;

        // Build list of starting nodes: prefer terminals, then use root
        let mut start_nodes: Vec<NodeId> = self.terminals.clone();
        if !start_nodes.contains(&self.root) {
            start_nodes.insert(0, self.root);
        }

        // Limit to num_starts
        start_nodes.truncate(self.num_starts as usize);

        for start in start_nodes {
            if let Some(sol) = self.construct_from(start, &costs) {
                match &best {
                    None => best = Some(sol),
                    Some(current_best) if sol.objective_value < current_best.objective_value => {
                        best = Some(sol);
                    }
                    _ => {}
                }
            }
        }

        best
    }
}

/// Multi-source Dijkstra: computes shortest distances from a SET of source nodes.
/// All source nodes start with distance 0.
use std::cmp::Ordering;
use std::collections::BinaryHeap;

#[derive(Clone, PartialEq)]
struct State {
    cost: Cost,
    node: NodeId,
}

impl Eq for State {}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.partial_cmp(&self.cost)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn multi_source_dijkstra(
    graph: &DirectedGraph,
    sources: &HashSet<NodeId>,
    costs: &[Cost],
) -> ShortestPathResult {
    let n = graph.num_nodes as usize;
    let mut distances = vec![f64::INFINITY; n + 1];
    let mut predecessors: Vec<Option<(NodeId, ArcId)>> = vec![None; n + 1];
    let mut heap = BinaryHeap::new();

    // Initialize all source nodes with distance 0
    for &source in sources {
        distances[source as usize] = 0.0;
        heap.push(State { cost: 0.0, node: source });
    }

    while let Some(State { cost, node }) = heap.pop() {
        if cost > distances[node as usize] {
            continue;
        }

        for &(head, arc_id) in graph.delta_plus(node) {
            let arc_cost = costs[arc_id as usize];
            let next_cost = cost + arc_cost;

            if next_cost < distances[head as usize] {
                distances[head as usize] = next_cost;
                predecessors[head as usize] = Some((node, arc_id));
                heap.push(State { cost: next_cost, node: head });
            }
        }
    }

    ShortestPathResult { distances, predecessors }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn build_test_instance() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        //     1
        //    / \
        //   2   5
        //  / \   \
        // 3   4   6
        //
        // Terminals: 3, 4, 6
        // Edges (bidirectional): 1-2(1), 2-3(2), 2-4(3), 1-5(2), 5-6(1)
        let mut g = DirectedGraph::new(6);
        for i in 1..=6u32 {
            let nt = if [3, 4, 6].contains(&i) { NodeType::Terminal } else { NodeType::Steiner };
            g.add_node(i, nt, 0.0);
        }

        // Bidirectional arcs
        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(2, 3, 2.0); // 2
        g.add_arc(3, 2, 2.0); // 3
        g.add_arc(2, 4, 3.0); // 4
        g.add_arc(4, 2, 3.0); // 5
        g.add_arc(1, 5, 2.0); // 6
        g.add_arc(5, 1, 2.0); // 7
        g.add_arc(5, 6, 1.0); // 8
        g.add_arc(6, 5, 1.0); // 9

        let root = 1;
        let terminals = vec![3, 4, 6];
        (g, root, terminals)
    }

    #[test]
    fn test_constructive_finds_solution() {
        let (graph, root, terminals) = build_test_instance();
        let mut heuristic = ConstructiveHeuristic::new(graph, root, terminals);
        heuristic.num_starts = 3;

        let solution = heuristic.run();
        assert!(solution.is_some());

        let sol = solution.unwrap();
        assert!(sol.is_feasible());
        // Optimal: 1->2(1), 2->3(2), 2->4(3), 1->5(2), 5->6(1) = cost 9
        // Heuristic should find something reasonable
        assert!(sol.objective_value <= 9.0 + 1e-6);
    }

    #[test]
    fn test_constructive_all_terminals_spanned() {
        let (graph, root, terminals) = build_test_instance();
        let mut heuristic = ConstructiveHeuristic::new(graph.clone(), root, terminals.clone());
        heuristic.num_starts = 1;

        let solution = heuristic.run().unwrap();
        let sol_nodes: HashSet<NodeId> = solution.nodes.iter().copied().collect();

        // All terminals must be in the solution
        for &t in &terminals {
            assert!(sol_nodes.contains(&t), "Terminal {} not in solution", t);
        }
    }
}
