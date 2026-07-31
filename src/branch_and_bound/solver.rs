use std::collections::HashSet;
use std::time::Instant;

use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use crate::graph::algorithms::{dual_ascent, reduced_cost_fixable_arcs};
use crate::model::{LpRelaxation, SteinerSolution};
use crate::separation::{FlowCutSeparator, CycleCutSeparator, PartitionSeparator, TfCutSeparator};
use crate::heuristics::{ConstructiveHeuristic, LocalSearchHeuristic, RecombinationHeuristic, PrimalHeuristic};

use super::tree::{BranchAndBoundTree, BbNode, SolveStatus};
use super::branching::{BranchingRule, PseudoCosts};
use super::node_selection::NodeSelector;

#[derive(Debug, Clone)]
pub struct SolverConfig {
    pub time_limit_secs: f64,
    pub node_limit: u64,
    pub gap_tolerance: f64,
    pub cut_rounds_per_node: u32,
    pub heuristic_frequency: u32,
    pub verbose: bool,
    pub preprocess: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            time_limit_secs: 3600.0,
            node_limit: 1_000_000,
            gap_tolerance: 1e-6,
            cut_rounds_per_node: 20,
            heuristic_frequency: 3,
            verbose: true,
            preprocess: true,
        }
    }
}

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
    /// Persistent LP: built once, reset per node via snapshot/reset.
    base_lp: Option<LpRelaxation>,
    /// Canonical signatures for deduplication (sorted arc list as key).
    cut_signatures: HashSet<Vec<ArcId>>,
    /// Arcs fixed to 0 by reduced-cost fixing (valid globally).
    fixed_zero_arcs: HashSet<ArcId>,
    /// DA reduced costs (from root dual ascent), used for LP-bound-based arc fixing.
    da_reduced_costs: Vec<f64>,
    /// Recombination heuristic with solution pool
    recombination: RecombinationHeuristic,
    /// Running statistics
    total_cuts_added: u64,
    total_lp_solves: u64,
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
        let recombination = RecombinationHeuristic::new(
            graph.clone(), root, terminals.clone(),
        );

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
            da_reduced_costs: Vec::new(),
            base_lp: None,
            cut_signatures: HashSet::new(),
            fixed_zero_arcs: HashSet::new(),
            recombination,
            total_cuts_added: 0,
            total_lp_solves: 0,
        }
    }

    pub fn with_config(mut self, config: SolverConfig) -> Self {
        self.config = config;
        self
    }

    pub fn solve(&mut self) -> (Option<SteinerSolution>, SolverStats) {
        let start_time = Instant::now();

        self.run_initial_heuristic();

        // Dual ascent: fast lower bound + reduced-cost fixing (Wong 1984)
        let da_result = dual_ascent(&self.graph, self.root, &self.terminals);
        if da_result.lower_bound > self.tree.global_dual_bound {
            self.tree.global_dual_bound = da_result.lower_bound;
        }
        self.da_reduced_costs = da_result.reduced_costs.clone();

        // Reduced-cost fixing: fix arcs where LB + reduced_cost > UB
        if self.tree.global_primal_bound < f64::INFINITY {
            let fixable = reduced_cost_fixable_arcs(&da_result, self.tree.global_primal_bound);
            for arc_id in fixable {
                self.fixed_zero_arcs.insert(arc_id);
            }

            // DA-guided primal heuristic: use reduced costs to bias construction
            let da_weights: Vec<f64> = da_result.reduced_costs.iter()
                .enumerate()
                .map(|(i, &rc)| {
                    let orig = self.graph.arcs[i].cost;
                    if orig > 1e-10 { 1.0 - (rc / orig).min(1.0) } else { 0.0 }
                })
                .collect();

            let mut da_constructive = ConstructiveHeuristic::new(
                self.graph.clone(), self.root, self.terminals.clone(),
            );
            da_constructive = da_constructive.with_lp_weights(da_weights);
            da_constructive.num_starts = 20;

            if let Some(da_sol) = da_constructive.run() {
                if self.verify_solution(&da_sol) && da_sol.objective_value < self.tree.global_primal_bound - 1e-9 {
                    let mut ls = LocalSearchHeuristic::new(
                        self.graph.clone(), self.root, self.terminals.clone(),
                    );
                    ls.set_incumbent(da_sol.clone());
                    let best = match ls.run() {
                        Some(improved) if improved.objective_value < da_sol.objective_value
                            && self.verify_solution(&improved) => improved,
                        _ => da_sol,
                    };
                    self.recombination.add_solution(best.clone());
                    self.tree.update_primal(best);

                    // Re-run reduced-cost fixing with tighter UB
                    let fixable = reduced_cost_fixable_arcs(&da_result, self.tree.global_primal_bound);
                    for arc_id in fixable {
                        self.fixed_zero_arcs.insert(arc_id);
                    }
                }
            }
        }

        // Build the base LP once (structural constraints + global fixings)
        let mut lp = LpRelaxation::from_formulation(
            &self.graph,
            self.root,
            &self.terminals,
            &self.steiner_nodes,
        );
        let mut sorted_fixed: Vec<ArcId> = self.fixed_zero_arcs.iter().copied().collect();
        sorted_fixed.sort();
        for &arc_id in &sorted_fixed {
            lp.fix_variable(arc_id, 0.0);
        }
        lp.snapshot_base();
        self.base_lp = Some(lp);

        if self.config.verbose {
            eprintln!(
                "[B&C] Initial primal: {:.1} | DA lower bound: {:.1} | Fixed arcs: {}",
                self.tree.global_primal_bound, da_result.lower_bound, self.fixed_zero_arcs.len(),
            );
        }

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

        loop {
            let elapsed = start_time.elapsed().as_secs_f64();
            if elapsed > self.config.time_limit_secs {
                self.tree.status = SolveStatus::TimeLimit;
                break;
            }
            if self.tree.nodes_processed >= self.config.node_limit {
                self.tree.status = SolveStatus::NodeLimit;
                break;
            }

            let node_id = match self.node_selector.select(&self.tree.nodes, &self.tree.open_nodes) {
                Some(id) => id,
                None => {
                    if self.tree.best_solution.is_some() {
                        self.tree.status = SolveStatus::Optimal;
                    } else {
                        self.tree.status = SolveStatus::Infeasible;
                    }
                    break;
                }
            };

            if let Some(pos) = self.tree.open_nodes.iter().position(|&id| id == node_id) {
                self.tree.open_nodes.swap_remove(pos);
            }
            self.tree.nodes_processed += 1;

            let _parent_dual = self.tree.nodes[node_id as usize].dual_bound;
            let result = self.process_node(node_id);
            let child_dual = self.tree.nodes[node_id as usize].dual_bound;

            // Update pseudo-costs: record bound change caused by parent's branching
            if let Some(parent_id) = self.tree.nodes[node_id as usize].parent {
                let parent_node = &self.tree.nodes[parent_id as usize];
                let parent_bound = parent_node.dual_bound;
                if parent_bound > f64::NEG_INFINITY && child_dual > f64::NEG_INFINITY
                    && child_dual > parent_bound + 1e-9
                {
                    let bound_change = child_dual - parent_bound;
                    // Determine which branching decision led to this child
                    let fixings = &self.tree.nodes[node_id as usize].fixings;
                    if let Some(&(branch_arc, val)) = fixings.last() {
                        if val == 0.0 {
                            self.pseudo_costs.record_down(branch_arc, bound_change);
                        } else {
                            self.pseudo_costs.record_up(branch_arc, bound_change);
                        }
                    }
                }
            }

            match result {
                NodeResult::Pruned => {}
                NodeResult::IntegerFeasible(solution) => {
                    self.tree.update_primal(solution);
                    self.tree.prune();
                }
                NodeResult::Branch(branch_var) => {
                    self.create_children(node_id, branch_var);
                }
            }

            self.update_global_dual_bound();

            if self.tree.is_solved() {
                self.tree.status = SolveStatus::Optimal;
                break;
            }

            if self.config.verbose && self.tree.nodes_processed % 100 == 0 {
                eprintln!(
                    "[B&C] Nodes: {} | Open: {} | Primal: {:.4} | Dual: {:.4} | Gap: {:.2}% | Cuts: {} | LPs: {}",
                    self.tree.nodes_processed,
                    self.tree.open_nodes.len(),
                    self.tree.global_primal_bound,
                    self.tree.global_dual_bound,
                    self.tree.gap() * 100.0,
                    self.total_cuts_added,
                    self.total_lp_solves,
                );
            }
        }

        let elapsed = start_time.elapsed().as_secs_f64();

        if self.config.verbose {
            eprintln!(
                "[B&C] Done. Status: {:?} | Nodes: {} | Cuts: {} | LPs: {} | Time: {:.2}s | Gap: {:.6}%",
                self.tree.status, self.tree.nodes_processed,
                self.total_cuts_added, self.total_lp_solves,
                elapsed, self.tree.gap() * 100.0,
            );
        }

        let stats = SolverStats {
            nodes_processed: self.tree.nodes_processed,
            cuts_added: self.total_cuts_added,
            lp_solves: self.total_lp_solves,
            primal_bound: self.tree.global_primal_bound,
            dual_bound: self.tree.global_dual_bound,
            gap: self.tree.gap(),
            time_secs: elapsed,
            status: self.tree.status.clone(),
        };

        (self.tree.best_solution.clone(), stats)
    }

    fn process_node(&mut self, node_id: u64) -> NodeResult {
        let node = &self.tree.nodes[node_id as usize];
        let fixings = node.fixings.clone();
        let is_root_node = node.depth == 0;

        {
            let lp = self.base_lp.as_mut().unwrap();
            lp.reset_to_base();
            for &(arc_id, value) in &fixings {
                lp.fix_variable(arc_id, value);
            }
        }

        let mut lp_solution: Vec<f64> = Vec::new();
        let mut node_dual_bound = f64::NEG_INFINITY;

        let max_rounds = if is_root_node {
            self.config.cut_rounds_per_node * 5
        } else {
            self.config.cut_rounds_per_node
        };

        let mut separator = FlowCutSeparator::new(
            &self.graph,
            self.root,
            &self.terminals,
        );
        let mut cycle_sep = CycleCutSeparator::new(&self.graph);
        let mut partition_sep = PartitionSeparator::new(
            &self.graph,
            self.root,
            &self.terminals,
        );
        let mut tf_sep = TfCutSeparator::new(&self.graph, &self.terminals);

        let mut prev_bound = f64::NEG_INFINITY;
        let mut stall_rounds = 0u32;

        for _round in 0..max_rounds {
            let obj = self.base_lp.as_mut().unwrap().solve();
            self.total_lp_solves += 1;

            if !self.base_lp.as_ref().unwrap().is_optimal() {
                return NodeResult::Pruned;
            }

            node_dual_bound = obj;

            if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                return NodeResult::Pruned;
            }

            // Tailing-off detection: if bound improvement < 0.1% for 3 consecutive rounds, stop
            let improvement = if prev_bound > f64::NEG_INFINITY && prev_bound.abs() > 1e-10 {
                (node_dual_bound - prev_bound) / prev_bound.abs()
            } else {
                1.0
            };
            prev_bound = node_dual_bound;

            if improvement < 0.001 {
                stall_rounds += 1;
                if stall_rounds >= 3 && !is_root_node {
                    break;
                }
                if stall_rounds >= 10 && is_root_node {
                    break;
                }
            } else {
                stall_rounds = 0;
            }

            lp_solution = self.base_lp.as_ref().unwrap().get_solution().to_vec();

            let flow_cuts = separator.find_violated_cuts(&lp_solution);
            let cycle_cuts = cycle_sep.find_violated_cuts(&lp_solution);

            // Partition cuts: run when flow/cycle cuts are exhausted or sparse,
            // as they target multi-component fractional solutions.
            let partition_cuts = if flow_cuts.len() < 3 {
                partition_sep.find_violated_cuts(&lp_solution)
            } else {
                Vec::new()
            };

            // TF set cuts: for terminal-free sets with dead-branch structure
            let tf_cuts = if flow_cuts.len() < 5 {
                tf_sep.find_violated_cuts(&lp_solution)
            } else {
                Vec::new()
            };

            if flow_cuts.is_empty() && cycle_cuts.is_empty()
                && partition_cuts.is_empty() && tf_cuts.is_empty() {
                break;
            }

            // Sort flow cuts by violation (most violated first) and limit per round
            let mut sorted_flow = flow_cuts;
            sorted_flow.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(std::cmp::Ordering::Equal));

            let mut new_cut_arcs: Vec<Vec<ArcId>> = Vec::new();
            let max_cuts_per_round = 30;
            for cut in sorted_flow.iter().take(max_cuts_per_round) {
                let mut sig = cut.cut_arcs.clone();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    new_cut_arcs.push(cut.cut_arcs.clone());
                    self.total_cuts_added += 1;
                }
            }

            let mut new_cycle_pairs: Vec<Vec<(ArcId, ArcId)>> = Vec::new();
            for ccut in &cycle_cuts {
                let mut sig = ccut.arc_ids.clone();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    let pairs: Vec<(ArcId, ArcId)> = ccut.edge_indices.iter()
                        .map(|&ei| (2 * ei as ArcId, 2 * ei as ArcId + 1))
                        .collect();
                    new_cycle_pairs.push(pairs);
                    self.total_cuts_added += 1;
                }
            }

            // Add partition cuts
            let mut new_partition_cuts: Vec<(Vec<ArcId>, f64)> = Vec::new();
            for pcut in &partition_cuts {
                let mut sig = pcut.crossing_arcs.clone();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    new_partition_cuts.push((pcut.crossing_arcs.clone(), pcut.rhs));
                    self.total_cuts_added += 1;
                }
            }

            // Add TF set cuts: x(δ(S)) >= 2*x_e
            // In directed model: sum boundary arcs - 2*(y_fwd_e + y_rev_e) >= 0
            let mut new_tf_cuts: Vec<(Vec<ArcId>, Vec<f64>)> = Vec::new();
            for tcut in &tf_cuts {
                let mut sig: Vec<ArcId> = tcut.boundary_arcs.iter()
                    .flat_map(|&(f, r)| [f, r])
                    .chain([tcut.edge_arc_pair.0, tcut.edge_arc_pair.1])
                    .collect();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    let mut arcs: Vec<ArcId> = Vec::new();
                    let mut coeffs: Vec<f64> = Vec::new();
                    for &(fwd, rev) in &tcut.boundary_arcs {
                        arcs.push(fwd);
                        coeffs.push(1.0);
                        arcs.push(rev);
                        coeffs.push(1.0);
                    }
                    arcs.push(tcut.edge_arc_pair.0);
                    coeffs.push(-2.0);
                    arcs.push(tcut.edge_arc_pair.1);
                    coeffs.push(-2.0);
                    new_tf_cuts.push((arcs, coeffs));
                    self.total_cuts_added += 1;
                }
            }

            let lp = self.base_lp.as_mut().unwrap();
            for arcs in &new_cut_arcs {
                lp.add_steiner_cut(arcs);
            }
            for pairs in &new_cycle_pairs {
                lp.add_cycle_cut(pairs);
            }
            for (arcs, rhs) in &new_partition_cuts {
                let coeffs: Vec<f64> = vec![1.0; arcs.len()];
                lp.add_cut(arcs, &coeffs, *rhs);
            }
            for (arcs, coeffs) in &new_tf_cuts {
                lp.add_cut(arcs, coeffs, 0.0);
            }
            lp.base_constraint_count = lp.num_constraints();
        }

        self.tree.nodes[node_id as usize].dual_bound = node_dual_bound;

        if self.is_integer_solution(&lp_solution) {
            let solution = self.extract_solution(&lp_solution);
            if let Some(sol) = solution {
                return NodeResult::IntegerFeasible(sol);
            }
        }

        let run_heuristic = is_root_node
            || self.tree.nodes_processed % self.config.heuristic_frequency as u64 == 0;
        if run_heuristic {
            if let Some(sol) = self.run_lp_heuristic(&lp_solution) {
                self.recombination.add_solution(sol.clone());
                if sol.objective_value < self.tree.global_primal_bound - 1e-9 {
                    self.tree.update_primal(sol);
                    self.tree.prune();

                    if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                        return NodeResult::Pruned;
                    }
                }
            }

            // Run recombination every 5th heuristic call when we have enough solutions
            if self.tree.nodes_processed % (self.config.heuristic_frequency as u64 * 5) == 0
                && self.recombination.solution_pool.len() >= 3
            {
                if let Some(recom_sol) = self.recombination.run() {
                    if self.verify_solution(&recom_sol)
                        && recom_sol.objective_value < self.tree.global_primal_bound - 1e-9
                    {
                        self.tree.update_primal(recom_sol);
                        self.tree.prune();

                        if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                            return NodeResult::Pruned;
                        }
                    }
                }
            }
        }

        // LP-based reduced-cost fixing: DISABLED pending sign convention verification.
        // HiGHS dual_columns() values may have unexpected sign convention with
        // activation variables present, leading to incorrect arc elimination.

        // Strong branching at the top of the tree: temporarily solve child LPs
        // to determine which variable gives the best dual bound improvement.
        let node_depth = self.tree.nodes[node_id as usize].depth;
        let branch_var = if node_depth <= 3 && self.config.time_limit_secs > 30.0 {
            self.select_strong_branching(&lp_solution, node_dual_bound)
        } else {
            self.branching_rule.select_with_costs(&lp_solution, &self.pseudo_costs, self.graph.num_arcs() as usize)
        };

        match branch_var {
            Some(var) => NodeResult::Branch(var),
            None => NodeResult::Pruned,
        }
    }

    /// Real strong branching: solve temporary child LPs for candidate variables
    /// and select the one with the best combined dual bound improvement.
    ///
    /// For each candidate variable, we temporarily fix it to 0 and 1, re-solve
    /// the LP, record the bound improvement, and then restore the original bounds.
    fn select_strong_branching(
        &mut self,
        lp_solution: &[f64],
        parent_bound: f64,
    ) -> Option<ArcId> {
        let num_arcs = self.graph.num_arcs() as usize;
        let num_edges = num_arcs / 2;

        // Collect candidate edges (fractional z_e = y_fwd + y_rev)
        let mut candidates: Vec<(ArcId, f64)> = Vec::new();
        for e in 0..num_edges {
            let y_fwd = lp_solution[e * 2];
            let y_rev = lp_solution[e * 2 + 1];
            let z = y_fwd + y_rev;
            let frac = (z - z.round()).abs();
            if frac > 1e-6 {
                candidates.push(((e * 2) as ArcId, frac));
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Sort by fractionality (most fractional first) and take top candidates
        candidates.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        let max_candidates = 8.min(candidates.len());
        candidates.truncate(max_candidates);

        let mut best_score = f64::NEG_INFINITY;
        let mut best_var: Option<ArcId> = None;

        // Save the current LP bounds for the candidate variables so we can restore
        let lp = self.base_lp.as_ref().unwrap();
        let saved_lb: Vec<f64> = lp.var_lb.clone();
        let saved_ub: Vec<f64> = lp.var_ub.clone();

        for &(arc_id, _frac) in &candidates {
            let reverse_arc = arc_id + 1;
            let aid = arc_id as usize;
            let rid = reverse_arc as usize;

            // Down-branch probe: fix edge to 0 (both arcs)
            let lp = self.base_lp.as_mut().unwrap();
            lp.fix_variable(arc_id, 0.0);
            if rid < num_arcs {
                lp.fix_variable(reverse_arc, 0.0);
            }
            let down_obj = lp.solve();
            self.total_lp_solves += 1;
            let down_bound = if lp.is_optimal() { down_obj } else { f64::INFINITY };

            // Restore to saved bounds
            let lp = self.base_lp.as_mut().unwrap();
            lp.change_variable_bounds(arc_id, saved_lb[aid], saved_ub[aid]);
            if rid < num_arcs {
                lp.change_variable_bounds(reverse_arc, saved_lb[rid], saved_ub[rid]);
            }

            // Up-branch probe: fix forward arc to 1
            let lp = self.base_lp.as_mut().unwrap();
            lp.fix_variable(arc_id, 1.0);
            let up_obj = lp.solve();
            self.total_lp_solves += 1;
            let up_bound = if lp.is_optimal() { up_obj } else { f64::INFINITY };

            // Restore to saved bounds
            let lp = self.base_lp.as_mut().unwrap();
            lp.change_variable_bounds(arc_id, saved_lb[aid], saved_ub[aid]);

            // Compute score: product rule (SCIP-style)
            let down_gain = (down_bound - parent_bound).max(1e-6);
            let up_gain = (up_bound - parent_bound).max(1e-6);
            let score = (1.0 - 1e-6) * down_gain.min(up_gain) + 1e-6 * down_gain.max(up_gain);

            // Update pseudo-costs with real strong branching data
            let z_val = lp_solution[aid] + lp_solution.get(rid).copied().unwrap_or(0.0);
            if down_bound < f64::INFINITY && down_gain > 1e-6 {
                self.pseudo_costs.record_down(arc_id, down_gain / z_val.max(1e-6));
            }
            if up_bound < f64::INFINITY && up_gain > 1e-6 {
                self.pseudo_costs.record_up(arc_id, up_gain / (1.0 - z_val).max(1e-6));
            }

            if score > best_score {
                best_score = score;
                best_var = Some(arc_id);
            }
        }

        best_var
    }

    fn run_initial_heuristic(&mut self) {
        let mut constructive = ConstructiveHeuristic::new(
            self.graph.clone(),
            self.root,
            self.terminals.clone(),
        );
        constructive.num_starts = 50;

        if let Some(initial_sol) = constructive.run() {
            if !self.verify_solution(&initial_sol) {
                return;
            }

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

            self.recombination.add_solution(best.clone());
            self.tree.update_primal(best);
        }
    }

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

    fn is_integer_solution(&self, solution: &[f64]) -> bool {
        let num_arcs = self.graph.num_arcs() as usize;
        solution.iter().take(num_arcs).all(|&val| (val - val.round()).abs() < 1e-5)
    }

    fn extract_solution(&self, lp_solution: &[f64]) -> Option<SteinerSolution> {
        let mut arcs: Vec<ArcId> = Vec::new();
        let mut nodes: HashSet<NodeId> = HashSet::new();
        let mut obj: Cost = 0.0;

        let num_arcs = self.graph.num_arcs() as usize;
        for (i, &val) in lp_solution.iter().take(num_arcs).enumerate() {
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
        if self.verify_solution(&sol) { Some(sol) } else { None }
    }

    /// Independent solution verifier: connectivity check via BFS from root.
    /// Verifies all terminals are reachable through selected arcs.
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

    fn create_children(&mut self, parent_id: u64, branch_var: ArcId) {
        let parent = &self.tree.nodes[parent_id as usize];
        let parent_depth = parent.depth;
        let parent_fixings = parent.fixings.clone();

        // Symmetry-aware branching: branch_var is the first arc in a pair.
        // Fix BOTH anti-parallel arcs (undirected edge branching).
        let reverse_arc = branch_var + 1;
        let has_reverse = (reverse_arc as usize) < self.graph.arcs.len();

        // Child 0: fix edge to 0 (both arcs to 0)
        let child0_id = self.tree.nodes.len() as u64;
        let mut fixings0 = parent_fixings.clone();
        fixings0.push((branch_var, 0.0));
        if has_reverse {
            fixings0.push((reverse_arc, 0.0));
        }
        self.tree.nodes.push(BbNode {
            id: child0_id,
            parent: Some(parent_id),
            depth: parent_depth + 1,
            dual_bound: self.tree.nodes[parent_id as usize].dual_bound,
            primal_bound: self.tree.global_primal_bound,
            fixings: fixings0,
        });
        self.tree.open_nodes.push(child0_id);

        // Child 1: fix edge to 1 (at least one arc must be 1)
        // We fix the forward arc to 1 (the reverse may still be 0 or 1)
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
        let mut g = DirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 3.0);
        g.add_arc(2, 1, 3.0);
        (g, 1, vec![2])
    }

    fn build_small_instance() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 2.0);
        g.add_arc(3, 2, 2.0);
        g.add_arc(2, 4, 5.0);
        g.add_arc(4, 2, 5.0);
        g.add_arc(1, 3, 10.0);
        g.add_arc(3, 1, 10.0);
        g.add_arc(1, 4, 8.0);
        g.add_arc(4, 1, 8.0);

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
        assert!(stats.lp_solves > 0, "Should track LP solves");
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
