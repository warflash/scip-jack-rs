use std::collections::HashSet;
use std::time::Instant;

use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use crate::model::{LpRelaxation, SteinerSolution};
use crate::separation::FlowCutSeparator;
use crate::heuristics::{ConstructiveHeuristic, LocalSearchHeuristic, PrimalHeuristic};

use super::tree::{BranchAndBoundTree, BbNode, SolveStatus};
use super::branching::{BranchingRule, PseudoCosts};
use super::node_selection::NodeSelector;

/// Configuration for the branch-and-cut solver.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    pub time_limit_secs: f64,
    pub node_limit: u64,
    pub gap_tolerance: f64,
    pub cut_rounds_per_node: u32,
    pub heuristic_frequency: u32,
    pub verbose: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            time_limit_secs: 3600.0,
            node_limit: 1_000_000,
            gap_tolerance: 1e-6,
            cut_rounds_per_node: 10,
            heuristic_frequency: 5,
            verbose: true,
        }
    }
}

/// Statistics from the solve process.
#[derive(Debug, Clone)]
pub struct SolverStats {
    pub nodes_processed: u64,
    pub cuts_added: u64,
    pub lp_solves: u64,
    pub primal_bound: f64,
    pub dual_bound: f64,
    pub gap: f64,
    pub time_secs: f64,
    pub status: SolveStatus,
}

/// The main branch-and-cut solver for the Steiner tree problem.
///
/// Algorithm overview (directed cut formulation):
/// 1. Root node: solve LP relaxation of min c^T y s.t. flow conservation
/// 2. Cutting plane loop: separate violated Steiner cuts, add to LP, re-solve
/// 3. Run primal heuristics to find feasible integer solutions
/// 4. If LP solution is integer → feasible solution found
/// 5. If gap > 0 and no more cuts → branch on most fractional variable
/// 6. Repeat until optimality proven (gap = 0) or limits reached
pub struct BranchAndCutSolver {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub steiner_nodes: Vec<NodeId>,
    pub config: SolverConfig,
    tree: BranchAndBoundTree,
    node_selector: NodeSelector,
    branching_rule: BranchingRule,
    pseudo_costs: PseudoCosts,
}

impl BranchAndCutSolver {
    pub fn new(
        graph: DirectedGraph,
        root: NodeId,
        terminals: Vec<NodeId>,
    ) -> Self {
        let terminal_set: HashSet<NodeId> = terminals.iter().copied().collect();
        let steiner_nodes: Vec<NodeId> = graph.nodes.iter()
            .map(|n| n.id)
            .filter(|id| !terminal_set.contains(id) && *id != root)
            .collect();

        let num_arcs = graph.num_arcs();

        Self {
            graph,
            root,
            terminals,
            steiner_nodes,
            config: SolverConfig::default(),
            tree: BranchAndBoundTree::new(),
            node_selector: NodeSelector::default_best_estimate(),
            branching_rule: BranchingRule::default_reliability(),
            pseudo_costs: PseudoCosts::new(num_arcs),
        }
    }

    pub fn with_config(mut self, config: SolverConfig) -> Self {
        self.config = config;
        self
    }

    /// Solve the Steiner tree problem to proven optimality.
    pub fn solve(&mut self) -> (Option<SteinerSolution>, SolverStats) {
        let start_time = Instant::now();

        // Phase 1: Run initial heuristic to get a primal bound
        self.run_initial_heuristic();

        if self.config.verbose {
            eprintln!("[B&C] Initial primal bound: {:.6}", self.tree.global_primal_bound);
        }

        // Phase 2: Create root node
        let root_node = BbNode {
            id: 0,
            parent: None,
            depth: 0,
            dual_bound: f64::NEG_INFINITY,
            primal_bound: self.tree.global_primal_bound,
            fixings: Vec::new(),
        };
        self.tree.nodes.push(root_node);
        self.tree.open_nodes.push(0);

        // Phase 3: Main branch-and-cut loop
        loop {
            // Check limits
            let elapsed = start_time.elapsed().as_secs_f64();
            if elapsed > self.config.time_limit_secs {
                self.tree.status = SolveStatus::TimeLimit;
                break;
            }
            if self.tree.nodes_processed >= self.config.node_limit {
                self.tree.status = SolveStatus::NodeLimit;
                break;
            }

            // Select next node
            let node_id = match self.node_selector.select(&self.tree.nodes, &self.tree.open_nodes) {
                Some(id) => id,
                None => {
                    // No more open nodes — problem is solved
                    if self.tree.best_solution.is_some() {
                        self.tree.status = SolveStatus::Optimal;
                    } else {
                        self.tree.status = SolveStatus::Infeasible;
                    }
                    break;
                }
            };

            // Remove from open list
            self.tree.open_nodes.retain(|&id| id != node_id);
            self.tree.nodes_processed += 1;

            // Process this node
            let result = self.process_node(node_id);

            match result {
                NodeResult::Pruned => {
                    // Node fathomed (infeasible or dominated)
                }
                NodeResult::IntegerFeasible(solution) => {
                    self.tree.update_primal(solution);
                    self.tree.prune();
                }
                NodeResult::Branch(branch_var) => {
                    self.create_children(node_id, branch_var);
                }
            }

            // Update global dual bound
            self.update_global_dual_bound();

            // Check optimality
            if self.tree.is_solved() {
                self.tree.status = SolveStatus::Optimal;
                break;
            }

            // Periodic logging
            if self.config.verbose && self.tree.nodes_processed % 100 == 0 {
                eprintln!(
                    "[B&C] Nodes: {} | Open: {} | Primal: {:.4} | Dual: {:.4} | Gap: {:.2}%",
                    self.tree.nodes_processed,
                    self.tree.open_nodes.len(),
                    self.tree.global_primal_bound,
                    self.tree.global_dual_bound,
                    self.tree.gap() * 100.0,
                );
            }
        }

        let elapsed = start_time.elapsed().as_secs_f64();

        if self.config.verbose {
            eprintln!(
                "[B&C] Done. Status: {:?} | Nodes: {} | Time: {:.2}s | Gap: {:.6}%",
                self.tree.status, self.tree.nodes_processed, elapsed, self.tree.gap() * 100.0,
            );
        }

        let stats = SolverStats {
            nodes_processed: self.tree.nodes_processed,
            cuts_added: 0, // tracked in LP
            lp_solves: 0,
            primal_bound: self.tree.global_primal_bound,
            dual_bound: self.tree.global_dual_bound,
            gap: self.tree.gap(),
            time_secs: elapsed,
            status: self.tree.status.clone(),
        };

        (self.tree.best_solution.clone(), stats)
    }

    /// Process a single B&B node: solve LP, separate, heuristics, decide.
    fn process_node(&mut self, node_id: u64) -> NodeResult {
        let node = &self.tree.nodes[node_id as usize];
        let fixings = node.fixings.clone();

        // Build LP for this node
        let mut lp = LpRelaxation::from_formulation(
            &self.graph,
            self.root,
            &self.terminals,
            &self.steiner_nodes,
        );

        // Apply variable fixings from branching
        for &(arc_id, value) in &fixings {
            // Fix variable: add constraint y_arc = value
            lp.add_cut(&[arc_id], &[1.0], value);
            if value < 0.5 {
                // y_arc <= 0 means add -y_arc >= 0 and y_arc <= 0
                // Actually for fixing to 0: add_cut with ub
                // We handle this by adding both bounds
                let arc_ids = [arc_id];
                let coeffs = [-1.0];
                lp.add_cut(&arc_ids, &coeffs, 0.0); // -y >= 0 => y <= 0
            }
        }

        // Cutting plane loop
        let mut lp_solution: Vec<f64> = Vec::new();
        let mut node_dual_bound = f64::NEG_INFINITY;

        for _round in 0..self.config.cut_rounds_per_node {
            // Solve LP
            let obj = lp.solve();

            if !lp.is_optimal() {
                return NodeResult::Pruned; // Infeasible or error
            }

            node_dual_bound = obj;

            // Pruning by bound
            if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                return NodeResult::Pruned;
            }

            lp_solution = lp.get_solution().to_vec();

            // Separation: find violated Steiner cuts
            let mut separator = FlowCutSeparator::new(
                &self.graph,
                self.root,
                &self.terminals,
            );
            let cuts = separator.find_violated_cuts(&lp_solution);

            if cuts.is_empty() {
                break; // No more violated cuts
            }

            // Add cuts to LP
            for cut in &cuts {
                lp.add_steiner_cut(&cut.cut_arcs);
            }
        }

        // Update node's dual bound
        self.tree.nodes[node_id as usize].dual_bound = node_dual_bound;

        // Check if LP solution is integral
        if self.is_integer_solution(&lp_solution) {
            let solution = self.extract_solution(&lp_solution);
            if let Some(sol) = solution {
                return NodeResult::IntegerFeasible(sol);
            }
        }

        // Run heuristics periodically
        if self.tree.nodes_processed % self.config.heuristic_frequency as u64 == 0 {
            if let Some(sol) = self.run_lp_heuristic(&lp_solution) {
                if sol.objective_value < self.tree.global_primal_bound - 1e-9 {
                    self.tree.update_primal(sol);
                    self.tree.prune();

                    // Re-check pruning after primal update
                    if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                        return NodeResult::Pruned;
                    }
                }
            }
        }

        // Branch
        match self.branching_rule.select_with_costs(&lp_solution, &self.pseudo_costs) {
            Some(var) => NodeResult::Branch(var),
            None => NodeResult::Pruned, // All variables are integer
        }
    }

    /// Run the constructive heuristic at the root to get an initial primal bound.
    fn run_initial_heuristic(&mut self) {
        let mut constructive = ConstructiveHeuristic::new(
            self.graph.clone(),
            self.root,
            self.terminals.clone(),
        );
        constructive.num_starts = 50;

        if let Some(initial_sol) = constructive.run() {
            // Verify feasibility before accepting
            if !self.verify_solution(&initial_sol) {
                return;
            }

            // Apply local search
            let mut ls = LocalSearchHeuristic::new(
                self.graph.clone(),
                self.root,
                self.terminals.clone(),
            );
            ls.set_incumbent(initial_sol.clone());

            let best = match ls.run() {
                Some(improved) if improved.objective_value < initial_sol.objective_value
                    && self.verify_solution(&improved) => improved,
                _ => initial_sol,
            };

            self.tree.update_primal(best);
        }
    }

    /// Run heuristic biased by the LP solution.
    fn run_lp_heuristic(&self, lp_solution: &[f64]) -> Option<SteinerSolution> {
        let mut constructive = ConstructiveHeuristic::new(
            self.graph.clone(),
            self.root,
            self.terminals.clone(),
        );
        constructive = constructive.with_lp_weights(lp_solution.to_vec());

        let sol = constructive.run()?;

        if !self.verify_solution(&sol) {
            return None;
        }

        // Apply local search
        let mut ls = LocalSearchHeuristic::new(
            self.graph.clone(),
            self.root,
            self.terminals.clone(),
        );
        ls.max_iterations = 10;
        ls.set_incumbent(sol.clone());

        match ls.run() {
            Some(improved) if improved.objective_value < sol.objective_value
                && self.verify_solution(&improved) => Some(improved),
            _ => Some(sol),
        }
    }

    /// Check if an LP solution is (approximately) integer.
    fn is_integer_solution(&self, solution: &[f64]) -> bool {
        solution.iter().all(|&val| {
            (val - val.round()).abs() < 1e-5
        })
    }

    /// Extract a Steiner solution from an integer LP solution.
    fn extract_solution(&self, lp_solution: &[f64]) -> Option<SteinerSolution> {
        let mut arcs: Vec<ArcId> = Vec::new();
        let mut nodes: HashSet<NodeId> = HashSet::new();
        let mut obj: Cost = 0.0;

        for (i, &val) in lp_solution.iter().enumerate() {
            if val > 0.5 {
                let arc_id = i as ArcId;
                arcs.push(arc_id);
                let arc = &self.graph.arcs[arc_id as usize];
                nodes.insert(arc.tail);
                nodes.insert(arc.head);
                obj += arc.cost;
            }
        }

        if arcs.is_empty() {
            return None;
        }

        let sol = SteinerSolution::new(arcs, nodes.into_iter().collect(), obj);
        if self.verify_solution(&sol) {
            Some(sol)
        } else {
            None
        }
    }

    /// Verify that a solution is feasible: all terminals reachable from root.
    fn verify_solution(&self, solution: &SteinerSolution) -> bool {
        let arc_set: HashSet<ArcId> = solution.arcs.iter().copied().collect();
        let mut reachable: HashSet<NodeId> = HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(self.root);
        reachable.insert(self.root);

        while let Some(node) = queue.pop_front() {
            for &(head, arc_id) in self.graph.delta_plus(node) {
                if arc_set.contains(&arc_id) && !reachable.contains(&head) {
                    reachable.insert(head);
                    queue.push_back(head);
                }
            }
        }

        self.terminals.iter().all(|t| reachable.contains(t))
    }

    /// Create two child nodes from branching on a variable.
    fn create_children(&mut self, parent_id: u64, branch_var: ArcId) {
        let parent = &self.tree.nodes[parent_id as usize];
        let parent_depth = parent.depth;
        let parent_fixings = parent.fixings.clone();

        // Child 0: fix variable to 0
        let child0_id = self.tree.nodes.len() as u64;
        let mut fixings0 = parent_fixings.clone();
        fixings0.push((branch_var, 0.0));
        self.tree.nodes.push(BbNode {
            id: child0_id,
            parent: Some(parent_id),
            depth: parent_depth + 1,
            dual_bound: self.tree.nodes[parent_id as usize].dual_bound,
            primal_bound: self.tree.global_primal_bound,
            fixings: fixings0,
        });
        self.tree.open_nodes.push(child0_id);

        // Child 1: fix variable to 1
        let child1_id = self.tree.nodes.len() as u64;
        let mut fixings1 = parent_fixings;
        fixings1.push((branch_var, 1.0));
        self.tree.nodes.push(BbNode {
            id: child1_id,
            parent: Some(parent_id),
            depth: parent_depth + 1,
            dual_bound: self.tree.nodes[parent_id as usize].dual_bound,
            primal_bound: self.tree.global_primal_bound,
            fixings: fixings1,
        });
        self.tree.open_nodes.push(child1_id);
    }

    /// Update global dual bound from open nodes.
    fn update_global_dual_bound(&mut self) {
        if self.tree.open_nodes.is_empty() {
            self.tree.global_dual_bound = self.tree.global_primal_bound;
        } else {
            self.tree.global_dual_bound = self.tree.open_nodes.iter()
                .map(|&id| self.tree.nodes[id as usize].dual_bound)
                .fold(f64::INFINITY, f64::min);
        }
    }
}

enum NodeResult {
    Pruned,
    IntegerFeasible(SteinerSolution),
    Branch(ArcId),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn build_trivial_instance() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // root(1) -> 2(terminal), cost 3
        // Unique optimal: cost 3
        let mut g = DirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 3.0);
        g.add_arc(2, 1, 3.0);
        (g, 1, vec![2])
    }

    fn build_small_instance() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // 1(root) --1-- 2 --2-- 3(T)
        //               |
        //              --5-- 4(T)
        // Also direct: 1 --10-- 3, 1 --8-- 4
        // Optimal: 1->2(1), 2->3(2), 2->4(5) = 8
        // Or: 1->2(1), 2->3(2), 1->4(8) = 11 (worse)
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(2, 3, 2.0); // 2
        g.add_arc(3, 2, 2.0); // 3
        g.add_arc(2, 4, 5.0); // 4
        g.add_arc(4, 2, 5.0); // 5
        g.add_arc(1, 3, 10.0); // 6
        g.add_arc(3, 1, 10.0); // 7
        g.add_arc(1, 4, 8.0); // 8
        g.add_arc(4, 1, 8.0); // 9

        (g, 1, vec![3, 4])
    }

    #[test]
    fn test_trivial_solve() {
        let (graph, root, terminals) = build_trivial_instance();
        let mut solver = BranchAndCutSolver::new(graph, root, terminals);
        solver.config.verbose = false;

        let (solution, stats) = solver.solve();

        assert!(solution.is_some(), "Should find a solution");
        let sol = solution.unwrap();
        assert!((sol.objective_value - 3.0).abs() < 1e-6,
            "Optimal cost should be 3, got {}", sol.objective_value);
        assert_eq!(stats.status, SolveStatus::Optimal);
    }

    #[test]
    fn test_small_instance_optimal() {
        let (graph, root, terminals) = build_small_instance();
        let mut solver = BranchAndCutSolver::new(graph, root, terminals);
        solver.config.verbose = false;
        solver.config.node_limit = 1000;

        let (solution, stats) = solver.solve();

        assert!(solution.is_some(), "Should find a solution");
        let sol = solution.unwrap();
        // Optimal: 1->2(1) + 2->3(2) + 2->4(5) = 8
        assert!(sol.objective_value <= 8.0 + 1e-6,
            "Optimal cost should be 8, got {}", sol.objective_value);
        assert!(stats.gap < 1e-4 || stats.status == SolveStatus::Optimal,
            "Should prove optimality or have small gap, gap={}", stats.gap);
    }

    #[test]
    fn test_primal_bound_always_valid() {
        let (graph, root, terminals) = build_small_instance();
        let mut solver = BranchAndCutSolver::new(graph, root, terminals);
        solver.config.verbose = false;
        solver.config.node_limit = 50;

        let (solution, stats) = solver.solve();

        if let Some(sol) = solution {
            assert!(sol.objective_value >= stats.dual_bound - 1e-6,
                "Primal {} < Dual {} is impossible", sol.objective_value, stats.dual_bound);
        }
    }
}
