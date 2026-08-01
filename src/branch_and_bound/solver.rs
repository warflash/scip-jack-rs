use std::collections::HashSet;
use std::time::Instant;

use crate::graph::{costs_are_integral, tighten_dual, DirectedGraph, NodeId, ArcId, Cost};
use crate::graph::algorithms::{
    dual_ascent_cuts, dual_ascent_masked, reduced_cost_distances, reduced_cost_fixable_arcs,
    reduced_cost_fixings, ArcIndex,
};

/// Arc entries the root ascent may contribute to the initial cut pool. Sized so
/// the seeded rows stay comparable to the structural model rather than dwarfing
/// it; beyond that the LP costs more per solve than the bound is worth.
const ASCENT_CUT_NNZ: usize = 400_000;
use crate::model::{LpRelaxation, LpStatus, SteinerSolution};
use crate::separation::{
    ActivationRankSeparator, CycleCutSeparator, FlowCutSeparator, PartitionSeparator,
    TfCutSeparator,
};
use crate::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use crate::heuristics::sph::{mst_prune, shortest_path_heuristic, SphResult, SphWorkspace};
use crate::heuristics::{RecombinationHeuristic, PrimalHeuristic};

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
    /// Separate cycle closure inequalities `x(C) <= |C| - 1`.
    pub cycle_cuts: bool,
    /// Separate terminal-partition inequalities.
    pub partition_cuts: bool,
    /// Separate activation-rank inequalities. Off by default: with the
    /// in-degree equality `y(delta^-(v)) = s_v` in the model, the family is
    /// implied and the separator provably finds nothing, at a cost of one max
    /// flow per terminal per round. It is kept as a diagnostic -- switching it
    /// on is how the implication gets re-checked if the formulation changes.
    pub activation_rank_cuts: bool,
    /// Separate terminal-free boundary inequalities `x(delta(S)) >= 2 x_e`.
    pub tf_cuts: bool,
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
            cycle_cuts: true,
            partition_cuts: true,
            activation_rank_cuts: false,
            tf_cuts: true,
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
    /// CSR arc index, reused by every node-level dual ascent.
    arc_index: Option<ArcIndex>,
    /// Terminal membership by node id, for the primal heuristics.
    is_terminal: Vec<bool>,
    /// Heuristic scratch space, kept so the node heuristics allocate nothing.
    sph_ws: Option<SphWorkspace>,
    kp_ws: Option<KeyPathWorkspace>,
    /// Running statistics
    total_cuts_added: u64,
    total_lp_solves: u64,
    /// Nodes pruned by the dual-ascent bound without solving an LP.
    da_prunes: u64,
    /// Every arc cost is an integer, so every feasible objective value is too
    /// and dual bounds may be rounded up.
    integral_objective: bool,
    /// Set the moment any node is left unfinished. While it is set, an empty
    /// node queue no longer means "everything was pruned", so the search may not
    /// conclude that the incumbent is optimal.
    search_incomplete: bool,
    /// Wall-clock stop. Checked inside the cut loop as well as between nodes:
    /// a root node runs a hundred cut rounds, each of which may solve dozens of
    /// LPs, so a between-nodes check alone lets one node overrun the budget by
    /// an order of magnitude.
    deadline: Option<Instant>,
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
        let integral_objective = costs_are_integral(graph.arcs.iter().map(|a| a.cost));
        let mut is_terminal = vec![false; graph.num_nodes as usize + 1];
        for &t in &terminals {
            is_terminal[t as usize] = true;
        }
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
            arc_index: None,
            is_terminal,
            sph_ws: None,
            kp_ws: None,
            total_cuts_added: 0,
            total_lp_solves: 0,
            da_prunes: 0,
            integral_objective,
            search_incomplete: false,
            deadline: None,
        }
    }

    pub fn with_config(mut self, config: SolverConfig) -> Self {
        self.config = config;
        self
    }

    /// Install an incumbent found before the search started.
    ///
    /// Unlike [`BranchAndCutSolver::seed_bounds`] this makes the solution itself
    /// available, so the search can report and verify it instead of merely
    /// pruning against its cost.
    pub fn seed_incumbent(&mut self, arcs: Vec<ArcId>) {
        if arcs.is_empty() {
            return;
        }
        let mut nodes: Vec<NodeId> = Vec::with_capacity(arcs.len() + 1);
        nodes.push(self.root);
        let mut cost = 0.0;
        for &a in &arcs {
            let arc = &self.graph.arcs[a as usize];
            nodes.push(arc.tail);
            nodes.push(arc.head);
            cost += arc.cost;
        }
        nodes.sort_unstable();
        nodes.dedup();
        let solution = SteinerSolution::new(arcs, nodes, cost);
        if self.verify_solution(&solution) {
            self.recombination.add_solution(solution.clone());
            self.tree.update_primal(solution);
        }
    }

    /// Seed the search with bounds already proved at the root by ascend-and-prune.
    ///
    /// The primal bound is a *cutoff* only: the corresponding solution lives in a
    /// graph this solver no longer sees, so no incumbent is installed. Nodes whose
    /// dual bound reaches the cutoff can still be pruned, which is the point.
    pub fn seed_bounds(&mut self, lower: f64, upper: f64) {
        if lower > self.tree.global_dual_bound {
            self.tree.global_dual_bound = lower;
        }
        if upper < self.tree.global_primal_bound {
            self.tree.global_primal_bound = upper;
        }
    }

    pub fn solve(&mut self) -> (Option<SteinerSolution>, SolverStats) {
        let start_time = Instant::now();
        self.deadline = Some(
            start_time + std::time::Duration::from_secs_f64(self.config.time_limit_secs.max(0.0)),
        );

        let idx = ArcIndex::new(&self.graph);
        self.sph_ws = Some(SphWorkspace::new(idx.num_nodes()));
        self.kp_ws = Some(KeyPathWorkspace::new(idx.num_nodes()));
        self.arc_index = Some(idx);

        // No construction heuristic here. Ascend-and-prune has already run a
        // far stronger primal search — many guided shortest-path starts, key-path
        // exchange and recombination — and handed the result over through
        // `seed_bounds`/`seed_incumbent`. Repeating a weaker search would only
        // burn the time budget before the first LP is ever solved.
        let da_result = {
            let idx = self.arc_index.as_ref().unwrap();
            let active = vec![true; idx.num_arcs()];
            dual_ascent_cuts(idx, self.root, &self.terminals, &active, ASCENT_CUT_NNZ)
        };
        let da_bound = self.lift(da_result.lower_bound);
        if da_bound > self.tree.global_dual_bound {
            self.tree.global_dual_bound = da_bound;
        }
        self.da_reduced_costs = da_result.reduced_costs.clone();

        if self.tree.global_primal_bound < f64::INFINITY {
            for arc_id in reduced_cost_fixable_arcs(&da_result, self.tree.global_primal_bound) {
                self.fixed_zero_arcs.insert(arc_id);
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

        // Install the ascent's own cut packing. These rows make the ascent's dual
        // solution feasible for the LP, so the very first LP solve returns a bound
        // at least as strong as the ascent's — instead of starting from a
        // relaxation with no connectivity requirement at all and separating its
        // way back up one max-flow at a time.
        let mut seeded = 0usize;
        for cut in &da_result.cuts {
            if cut.iter().any(|a| self.fixed_zero_arcs.contains(a)) {
                // A cut whose arcs this solver has already deleted is still valid,
                // but its row would be over variables pinned to zero.
                let live: Vec<ArcId> = cut
                    .iter()
                    .copied()
                    .filter(|a| !self.fixed_zero_arcs.contains(a))
                    .collect();
                if live.is_empty() {
                    continue;
                }
                let mut sig = live.clone();
                sig.sort_unstable();
                if self.cut_signatures.insert(sig) {
                    lp.add_lazy_steiner_cut(&live);
                    seeded += 1;
                }
                continue;
            }
            let mut sig = cut.clone();
            sig.sort_unstable();
            if self.cut_signatures.insert(sig) {
                lp.add_lazy_steiner_cut(cut);
                seeded += 1;
            }
        }
        self.total_cuts_added += seeded as u64;

        lp.snapshot_base();
        self.base_lp = Some(lp);

        if self.config.verbose {
            eprintln!(
                "[B&C] Initial primal: {:.1} | DA lower bound: {:.1} | Fixed arcs: {} | Seeded cuts: {}",
                self.tree.global_primal_bound, da_result.lower_bound, self.fixed_zero_arcs.len(),
                seeded,
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
                self.search_incomplete = !self.tree.open_nodes.is_empty();
                self.tree.status = SolveStatus::TimeLimit;
                break;
            }
            if self.tree.nodes_processed >= self.config.node_limit {
                self.search_incomplete = !self.tree.open_nodes.is_empty();
                self.tree.status = SolveStatus::NodeLimit;
                break;
            }

            let node_id = match self.node_selector.select(&self.tree.nodes, &self.tree.open_nodes) {
                Some(id) => id,
                None => {
                    self.update_global_dual_bound();
                    self.tree.status = if self.search_incomplete {
                        SolveStatus::TimeLimit
                    } else if self.tree.best_solution.is_some()
                        || self.tree.global_primal_bound.is_finite()
                    {
                        // Every node was closed by a genuine prune, so nothing
                        // cheaper than the incumbent exists anywhere.
                        SolveStatus::Optimal
                    } else {
                        SolveStatus::Infeasible
                    };
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
                    // An integral LP point is only a tree once every cut has
                    // been separated. Until then it can be a disconnected arc
                    // set, so it is verified rather than trusted.
                    if self.verify_solution(&solution) {
                        self.tree.update_primal(solution);
                        self.tree.prune();
                    }
                }
                NodeResult::Branch(branch_var) => {
                    self.create_children(node_id, branch_var);
                }
                NodeResult::Abandoned => {
                    // Put it back: its bound is valid, its subtree is not
                    // explored, and the search is no longer a proof.
                    self.search_incomplete = true;
                    self.tree.open_nodes.push(node_id);
                    self.update_global_dual_bound();
                    self.tree.status = SolveStatus::TimeLimit;
                    break;
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
            let (lp_secs, rows) = self
                .base_lp
                .as_ref()
                .map_or((0.0, 0), |lp| (lp.solve_time_secs, lp.num_constraints()));
            let rebuilds = self.base_lp.as_ref().map_or(0, |lp| lp.rebuilds);
            eprintln!(
                "[B&C] Done. Status: {:?} | Nodes: {} (DA-pruned {}) | Cuts: {} | LPs: {} | Time: {:.2}s | \
                 LP time: {:.2}s ({:.1}ms/solve, {} rows, {} rebuilds) | Gap: {:.6}%",
                self.tree.status, self.tree.nodes_processed, self.da_prunes,
                self.total_cuts_added, self.total_lp_solves,
                elapsed,
                lp_secs,
                if self.total_lp_solves > 0 { lp_secs * 1000.0 / self.total_lp_solves as f64 } else { 0.0 },
                rows,
                rebuilds,
                self.tree.gap() * 100.0,
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

    /// Dual ascent on the arcs this node still allows.
    ///
    /// The node's feasible set is contained in that of the relaxation obtained by
    /// simply deleting every arc branched to zero — the arcs branched to *one* are
    /// only ignored, which weakens the bound but keeps it valid. So the ascent's
    /// value is a legitimate lower bound for the node, and it costs about a
    /// millisecond against roughly a hundred for an LP solve.
    ///
    /// Returns the bound and the arcs its reduced costs rule out at this node.
    fn node_dual_ascent(&mut self, fixings: &[(ArcId, f64)]) -> (f64, Vec<ArcId>) {
        let idx = match self.arc_index.as_ref() {
            Some(i) => i,
            None => return (f64::NEG_INFINITY, Vec::new()),
        };
        let mut active = vec![true; idx.num_arcs()];
        for &a in &self.fixed_zero_arcs {
            active[a as usize] = false;
        }
        for &(a, v) in fixings {
            if v == 0.0 {
                active[a as usize] = false;
            }
        }

        let da = dual_ascent_masked(idx, self.root, &self.terminals, &active);
        let cutoff = self.tree.global_primal_bound;
        if !cutoff.is_finite() {
            return (da.lower_bound, Vec::new());
        }
        let dists = reduced_cost_distances(idx, self.root, &self.terminals, &da.reduced_costs, &active);
        let fix = reduced_cost_fixings(
            idx, self.root, &self.terminals, &da, &dists, &active, cutoff,
        );
        (da.lower_bound, fix.arcs)
    }

    /// Lift a dual bound to the next integer when the objective is integral.
    fn lift(&self, bound: f64) -> f64 {
        tighten_dual(bound, self.integral_objective)
    }

    fn out_of_time(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }


    fn process_node(&mut self, node_id: u64) -> NodeResult {
        let node = &self.tree.nodes[node_id as usize];
        let fixings = node.fixings.clone();
        let is_root_node = node.depth == 0;

        // Cheap dual bound first: if the ascent already reaches the cutoff there
        // is no reason to touch the LP at all.
        let (da_bound, da_fixable) = self.node_dual_ascent(&fixings);
        let da_bound = self.lift(da_bound);
        if da_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
            self.tree.nodes[node_id as usize].dual_bound = da_bound;
            self.da_prunes += 1;
            return NodeResult::Pruned;
        }

        {
            let lp = self.base_lp.as_mut().unwrap();
            lp.reset_to_base();
            for &(arc_id, value) in &fixings {
                lp.fix_variable(arc_id, value);
            }
            // Node-local eliminations from the ascent's reduced costs. These are
            // undone by `reset_to_base` when the next node is processed.
            for &a in &da_fixable {
                lp.fix_variable(a, 0.0);
            }
        }

        let mut lp_solution: Vec<f64> = Vec::new();
        let mut node_dual_bound = f64::NEG_INFINITY;

        // Cuts separated anywhere are globally valid and stay in the pool, so
        // the root is where it pays to iterate. Deep in the tree the bound is
        // moved much more cheaply by branching than by another twenty rounds of
        // separation against an LP that costs milliseconds a solve.
        let max_rounds = if is_root_node {
            self.config.cut_rounds_per_node * 5
        } else {
            (self.config.cut_rounds_per_node / 6).max(2)
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
        let mut ar_sep = ActivationRankSeparator::new(&self.graph);

        let no_cycle = !self.config.cycle_cuts;
        let no_partition = !self.config.partition_cuts;
        let no_tf = !self.config.tf_cuts;
        let no_ar = !self.config.activation_rank_cuts;

        let node_deadline = self.deadline;
        let mut prev_bound = f64::NEG_INFINITY;
        let mut stall_rounds = 0u32;

        let mut rounds_done = 0usize;
        for _round in 0..max_rounds as usize {
            if self.out_of_time() {
                // A node that has completed a round has a valid bound and a
                // valid fractional point, so it can still be branched: the
                // children carry the bound and stay in the queue, and the search
                // remains a proof of whatever it goes on to establish. Only a
                // node that never got that far is genuinely unresolved.
                if rounds_done == 0 {
                    return NodeResult::Abandoned;
                }
                break;
            }
            arm(self.base_lp.as_mut().unwrap(), node_deadline);
            let mut obj = self.base_lp.as_mut().unwrap().solve();
            self.total_lp_solves += 1;

            if !self.base_lp.as_ref().unwrap().is_optimal() {
                // Infeasible is a genuine prune; anything else — an iteration
                // limit, a numerical failure — proves nothing.
                return if self.base_lp.as_ref().unwrap().status == LpStatus::Infeasible {
                    NodeResult::Pruned
                } else {
                    NodeResult::Abandoned
                };
            }

            // Complete the model before doing anything with the solution: the
            // held-back structural rows are part of the relaxation, not optional
            // strengthening, so iterate to a fixpoint. Doing this inside the cut
            // round (rather than consuming one) keeps node bounds identical to
            // the fully resident model while the working LP stays small.
            // Geometric batches. A fixed batch of 500 costs one LP re-solve per
            // batch, and on a graph with tens of thousands of held-back rows that
            // is dozens of solves before the node's bound is even valid to read.
            // Growing the batch keeps the model small when few rows are wanted
            // and converges in a handful of solves when many are.
            let mut batch = 500usize;
            for _ in 0..64 {
                let added = self.base_lp.as_mut().unwrap().separate_structural(batch);
                batch = batch.saturating_mul(4);
                if added == 0 || self.out_of_time() {
                    break;
                }
                self.total_cuts_added += added as u64;
                arm(self.base_lp.as_mut().unwrap(), node_deadline);
                obj = self.base_lp.as_mut().unwrap().solve();
                self.total_lp_solves += 1;
                if !self.base_lp.as_ref().unwrap().is_optimal() {
                    return if self.base_lp.as_ref().unwrap().status == LpStatus::Infeasible {
                        NodeResult::Pruned
                    } else {
                        NodeResult::Abandoned
                    };
                }
            }

            // Age the global cut pool against this solution and drop cuts that
            // have been slack for a while. Without this the model grows
            // monotonically and the LP comes to dominate the whole runtime.
            self.base_lp.as_mut().unwrap().prune_cuts();

            node_dual_bound = self.lift(obj);

            if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                return NodeResult::Pruned;
            }

            // Stop when the relaxation stops getting stronger — not when it stops
            // getting stronger *quickly*.
            //
            // The old test compared the round's gain against 0.1% of the bound
            // itself, which is the wrong scale: on PACE instance161 the bound sits
            // near 5,100 while 220 units of gap remain, so "0.1% of the bound" is
            // five units a round and the loop declared victory with 4% of the gap
            // still open and the whole point of the LP unrealised. What matters is
            // whether another round moves the bound at all; if it does, separation
            // is still buying something, and if it does not, no number of further
            // rounds will.
            let moved = node_dual_bound > prev_bound + 1e-9 * node_dual_bound.abs().max(1.0);
            prev_bound = node_dual_bound;

            if !moved {
                stall_rounds += 1;
                if stall_rounds >= if is_root_node { 3 } else { 2 } {
                    break;
                }
            } else {
                stall_rounds = 0;
            }

            lp_solution = self.base_lp.as_ref().unwrap().get_solution().to_vec();
            rounds_done += 1;

            // Round the current point into a tree as the relaxation tightens,
            // not only once the node is finished. On the instances where the
            // root consumes the whole budget the node-level call would fire
            // exactly once, against the weakest LP point of the run, and the
            // incumbent is what every reduced-cost elimination is measured
            // against.
            if _round % self.config.heuristic_frequency.max(1) as usize == 0 {
                let candidate = lp_guided_tree(
                    self.arc_index.as_ref().unwrap(),
                    &self.fixed_zero_arcs,
                    &self.terminals,
                    &self.is_terminal,
                    self.root,
                    &lp_solution,
                    self.sph_ws.as_mut().unwrap(),
                    self.kp_ws.as_mut().unwrap(),
                );
                if let Some(sol) = candidate.filter(|s| {
                    crate::model::verify_solution(&self.graph, self.root, &self.terminals, s)
                        .is_valid
                }) {
                    if sol.objective_value < self.tree.global_primal_bound - 1e-9 {
                        self.recombination.add_solution(sol.clone());
                        self.tree.update_primal(sol);
                        self.tree.prune();
                        if node_dual_bound
                            >= self.tree.global_primal_bound - self.config.gap_tolerance
                        {
                            return NodeResult::Pruned;
                        }
                    }
                }
            }

            let flow_cuts = separator.find_violated_cuts(&lp_solution);
            let cycle_cuts = if no_cycle {
                Vec::new()
            } else {
                cycle_sep.find_violated_cuts(&lp_solution)
            };

            // Partition cuts: run when flow/cycle cuts are exhausted or sparse,
            // as they target multi-component fractional solutions.
            let partition_cuts = if flow_cuts.len() < 3 && !no_partition {
                partition_sep.find_violated_cuts(&lp_solution)
            } else {
                Vec::new()
            };

            // TF set cuts: for terminal-free sets with dead-branch structure
            let tf_cuts = if flow_cuts.len() < 5 && !no_tf {
                tf_sep.find_violated_cuts(&lp_solution)
            } else {
                Vec::new()
            };

            // Activation-rank cuts. The separation is exact, so the only reason
            // to hold it back is cost: one max flow per anchor. It runs when the
            // connectivity separators have gone quiet, which is where the bound
            // stops moving and a rank argument is what is left to say.
            // Unguarded on purpose when enabled: as a diagnostic it has to run
            // at every point the loop visits, not only at the quiet ones.
            let ar_cuts = if !no_ar {
                let s_values = {
                    let lp = self.base_lp.as_ref().unwrap();
                    let mut values = vec![0.0; lp.node_col.len()];
                    for (v, col) in lp.node_col.iter().enumerate() {
                        if let Some(c) = col {
                            values[v] = lp.get_solution().get(*c as usize).copied().unwrap_or(0.0);
                        }
                    }
                    values
                };
                ar_sep.find_violated_cuts(&lp_solution, &s_values, &self.terminals)
            } else {
                Vec::new()
            };

            if flow_cuts.is_empty() && cycle_cuts.is_empty()
                && partition_cuts.is_empty() && tf_cuts.is_empty() && ar_cuts.is_empty() {
                break;
            }

            // Sort flow cuts by violation (most violated first) and limit per round
            let mut sorted_flow = flow_cuts;
            sorted_flow.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(std::cmp::Ordering::Equal));

            let mut new_cut_arcs: Vec<Vec<ArcId>> = Vec::new();
            // Install everything the nested separator found. Generating a family
            // and then discarding five sixths of it wastes the max-flows that
            // produced it, and nested cuts are disjoint by construction, so they
            // are not the near-duplicates that a cap is meant to suppress.
            let max_cuts_per_round = 200;
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

            // Activation-rank rows carry activation columns, so they are built
            // against the LP's own column map rather than from arcs alone.
            let mut new_ar_rows: Vec<(Vec<(u32, f64)>, f64)> = Vec::new();
            for cut in ar_cuts.iter().take(8) {
                let node_col = self.base_lp.as_ref().unwrap().node_col.clone();
                let Some((entries, hi)) = ar_sep.row(cut, &node_col) else { continue };
                let mut sig: Vec<ArcId> = entries.iter().map(|&(c, _)| c).collect();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    new_ar_rows.push((entries, hi));
                    self.total_cuts_added += 1;
                }
            }

            let lp = self.base_lp.as_mut().unwrap();
            for (entries, hi) in new_ar_rows {
                lp.add_upper_cut(entries, hi);
            }
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
        }

        // An integral point with no verified tree behind it has no fractional
        // variable to branch on, so the node would be abandoned and — at the root
        // — the whole search would end there. That is not a corner case: the cut
        // loop leaves as soon as the bound tails off, and the point it leaves
        // behind is routinely an integral arc set that a connectivity cut still
        // forbids.
        // On SteinLib e18 exactly this ended the search at the root with a 5% gap
        // and 30 seconds of unused budget.
        //
        // The remedy is the one the formulation already provides: a disconnected
        // integral point violates a terminal cut by a full unit, so the max-flow
        // separator is guaranteed to find one. Keep separating against it until
        // the point becomes a tree or turns fractional.
        while !lp_solution.is_empty()
            && self.is_integer_solution(&lp_solution)
            && !self.out_of_time()
        {
            if let Some(sol) = self.extract_solution(&lp_solution) {
                self.tree.nodes[node_id as usize].dual_bound = node_dual_bound.max(da_bound);
                return NodeResult::IntegerFeasible(sol);
            }
            let forced = separator.find_violated_cuts(&lp_solution);
            let mut added = 0usize;
            for cut in &forced {
                let mut sig = cut.cut_arcs.clone();
                sig.sort();
                if self.cut_signatures.insert(sig) {
                    self.base_lp.as_mut().unwrap().add_steiner_cut(&cut.cut_arcs);
                    added += 1;
                }
            }
            if added == 0 {
                break;
            }
            self.total_cuts_added += added as u64;
            arm(self.base_lp.as_mut().unwrap(), node_deadline);
            let obj = self.base_lp.as_mut().unwrap().solve();
            self.total_lp_solves += 1;
            if !self.base_lp.as_ref().unwrap().is_optimal() {
                return if self.base_lp.as_ref().unwrap().status == LpStatus::Infeasible {
                    NodeResult::Pruned
                } else {
                    NodeResult::Abandoned
                };
            }
            node_dual_bound = self.lift(obj);
            if node_dual_bound >= self.tree.global_primal_bound - self.config.gap_tolerance {
                return NodeResult::Pruned;
            }
            lp_solution = self.base_lp.as_ref().unwrap().get_solution().to_vec();
        }

        // Both bounds are valid for this node, so the node's bound is the better
        // of them. The ascent frequently wins on instances where separation has
        // not caught up — dropping it here left nodes carrying a bound far below
        // one already in hand, which is what the open queue is minimised over.
        node_dual_bound = node_dual_bound.max(da_bound);
        self.tree.nodes[node_id as usize].dual_bound = node_dual_bound;

        if !lp_solution.is_empty() && self.is_integer_solution(&lp_solution) {
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

        // LP-based reduced-cost fixing at root: uses verified HiGHS sign convention.
        // For minimization with vars in [0,1]:
        //   - var at lb=0: rc >= 0, meaning any solution using this arc costs at least LP_bound + rc
        //   - Therefore: if LP_bound + rc > UB, this arc can never be in an optimal integer solution
        // All cuts added are globally valid, so root fixings are global.
        //
        // The optimality check is not a formality. Reduced-cost fixing is a
        // statement about an *optimal* basis: `rc_a` bounds the objective
        // increase from forcing `y_a` up only when the current point is optimal
        // for the current model. When a solve stops on its own clock, HiGHS
        // reports a non-optimal status and `LpRelaxation` leaves `solution`,
        // `reduced_costs` and `dual_bound` holding the values from the previous
        // solve -- a *different, smaller* model. Pairing that stale reduced-cost
        // vector with the current gap is not a weak bound, it is a wrong one.
        //
        // It fires: on PACE instance164 a root LP with 43,054 rows timed out and
        // the block then fixed 78,442 of 81,716 arcs, emptying the graph and
        // letting the search report a proved optimum of 5265 against a true
        // optimum of 5205.
        if is_root_node
            && self.base_lp.as_ref().is_some_and(|lp| lp.is_optimal())
            && self.tree.global_primal_bound < f64::INFINITY
            && lp_solution.len() >= self.graph.num_arcs() as usize
        {
            // The gap must be measured against the *raw* LP objective, not the
            // lifted one. Reduced-cost fixing rests on
            //
            //     cost of any solution using arc a  >=  LP_opt + rc_a,
            //
            // so the sound test is `LP_opt + rc_a > UB`. Substituting
            // `ceil(LP_opt)` for `LP_opt` shrinks the gap and drops arcs the
            // inequality does not license: `ceil(LP_opt) + rc_a > UB` says
            // nothing about `LP_opt + rc_a` unless the LP optimum happens to be
            // integral, and a cut-loop LP optimum essentially never is.
            let lp_objective = self.base_lp.as_ref().unwrap().get_dual_bound();
            let gap = self.tree.global_primal_bound - lp_objective.min(node_dual_bound);
            if gap > 1e-6 && lp_objective.is_finite() {
                let num_arcs = self.graph.num_arcs() as usize;
                let rc = &self.base_lp.as_ref().unwrap().reduced_costs;
                let sol = &lp_solution;
                let mut lp_fixed_count = 0usize;

                for a in 0..num_arcs {
                    if self.fixed_zero_arcs.contains(&(a as ArcId)) {
                        continue;
                    }
                    if sol[a] < 1e-6 && rc[a] > gap + 1e-4 {
                        self.fixed_zero_arcs.insert(a as ArcId);
                        lp_fixed_count += 1;
                    }
                }

                // Compound the LP's eliminations into the dual ascent. The ascent
                // is run on the arcs that survive, so every arc the LP removed
                // makes it tighter, and a tighter ascent removes more arcs in
                // turn. Both rules exclude arcs from *cheaper-than-incumbent*
                // solutions only, and both are stated for this solver's single
                // root, so the conclusions compose without the orientation
                // caveat that applies across roots.
                let mut ascent_fixed = 0usize;
                loop {
                    let before = self.fixed_zero_arcs.len();
                    let (da_bound, da_fixable) = self.node_dual_ascent(&[]);
                    let da_bound = self.lift(da_bound);
                    if da_bound > self.tree.global_dual_bound {
                        self.tree.global_dual_bound = da_bound;
                    }
                    for a in da_fixable {
                        self.fixed_zero_arcs.insert(a);
                    }
                    let gained = self.fixed_zero_arcs.len() - before;
                    ascent_fixed += gained;
                    if gained == 0 || self.out_of_time() {
                        break;
                    }
                }

                if lp_fixed_count + ascent_fixed > 0 {
                    let lp = self.base_lp.as_mut().unwrap();
                    for &arc_id in &self.fixed_zero_arcs {
                        lp.fix_variable(arc_id, 0.0);
                    }
                    lp.snapshot_base();
                    if self.config.verbose {
                        eprintln!(
                            "[B&C] root fixing: {lp_fixed_count} arcs by LP, {ascent_fixed} more by the ascent it enabled (gap={gap:.2})"
                        );
                    }
                }
            }
        }

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
            // No fractional variable and no integer solution extracted: the node
            // is unresolved, not closed.
            None => NodeResult::Abandoned,
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

        let mut candidates = super::branching::fractional_candidates(lp_solution, num_arcs);
        if candidates.is_empty() {
            return None;
        }
        candidates.truncate(8);

        let mut best_score = f64::NEG_INFINITY;
        let mut best_var: Option<ArcId> = None;

        // Save the current LP bounds for the candidate variables so we can restore
        let lp = self.base_lp.as_ref().unwrap();
        let saved_lb: Vec<f64> = lp.var_lb.clone();
        let saved_ub: Vec<f64> = lp.var_ub.clone();

        for &(arc_id, _frac) in &candidates {
            let aid = arc_id as usize;
            let value = lp_solution[aid];

            // Probe y_a = 0.
            let lp = self.base_lp.as_mut().unwrap();
            lp.fix_variable(arc_id, 0.0);
            let down_obj = lp.solve();
            self.total_lp_solves += 1;
            let down_bound = if lp.is_optimal() { down_obj } else { f64::INFINITY };
            lp.change_variable_bounds(arc_id, saved_lb[aid], saved_ub[aid]);

            // Probe y_a = 1.
            let lp = self.base_lp.as_mut().unwrap();
            lp.fix_variable(arc_id, 1.0);
            let up_obj = lp.solve();
            self.total_lp_solves += 1;
            let up_bound = if lp.is_optimal() { up_obj } else { f64::INFINITY };
            lp.change_variable_bounds(arc_id, saved_lb[aid], saved_ub[aid]);

            // Product score (SCIP-style): favour candidates whose weaker side
            // still improves the bound.
            let down_gain = (down_bound - parent_bound).max(1e-6);
            let up_gain = (up_bound - parent_bound).max(1e-6);
            let score = (1.0 - 1e-6) * down_gain.min(up_gain) + 1e-6 * down_gain.max(up_gain);

            // Feed the measurements back as pseudo-costs, normalised per unit of
            // variable movement so they transfer to other nodes.
            if down_bound < f64::INFINITY && down_gain > 1e-6 {
                self.pseudo_costs.record_down(arc_id, down_gain / value.max(1e-6));
            }
            if up_bound < f64::INFINITY && up_gain > 1e-6 {
                self.pseudo_costs.record_up(arc_id, up_gain / (1.0 - value).max(1e-6));
            }

            if score > best_score {
                best_score = score;
                best_var = Some(arc_id);
            }
        }

        best_var
    }

    fn run_lp_heuristic(&mut self, lp_solution: &[f64]) -> Option<SteinerSolution> {
        let sol = lp_guided_tree(
            self.arc_index.as_ref()?,
            &self.fixed_zero_arcs,
            &self.terminals,
            &self.is_terminal,
            self.root,
            lp_solution,
            self.sph_ws.as_mut()?,
            self.kp_ws.as_mut()?,
        )?;
        self.verify_solution(&sol).then_some(sol)
    }
}

/// Turn the fractional LP point into a tree.
///
/// Two operators, both driven by the same solution:
///
/// 1. **Support rebuild.** Take every vertex the LP puts any weight on and
///    return the pruned minimum spanning tree of the induced subgraph. When the
///    relaxation is nearly integral — which, at the root of these instances, it
///    usually is — this alone lands on the optimum.
/// 2. **Guided growth.** Run the shortest-path heuristic with arc weights
///    `c_a (1 - y_a)`, so corridors the LP has committed to are nearly free and
///    the greedy growth follows them, then improve the result by key-path
///    exchange.
///
/// Both are scored with the true arc costs, never with the search weights.
/// This is a free function rather than a method so that it can run inside the
/// cut loop, where the separators already hold a borrow of the graph.
#[allow(clippy::too_many_arguments)]
fn lp_guided_tree(
    idx: &ArcIndex,
    fixed_zero: &HashSet<ArcId>,
    terminals: &[NodeId],
    is_terminal: &[bool],
    root: NodeId,
    lp_solution: &[f64],
    sws: &mut SphWorkspace,
    kws: &mut KeyPathWorkspace,
) -> Option<SteinerSolution> {
        let num_arcs = idx.num_arcs();
        let mut active = vec![true; num_arcs];
        for &a in fixed_zero {
            active[a as usize] = false;
        }

        let mut support: Vec<NodeId> = vec![root];
        let mut weights: Vec<Cost> = Vec::with_capacity(num_arcs);
        for a in 0..num_arcs {
            let arc = a as ArcId;
            let c = idx.cost(arc);
            let y = lp_solution.get(a).copied().unwrap_or(0.0).clamp(0.0, 1.0);
            if y > 1e-6 && active[a] {
                support.push(idx.tail(arc));
                support.push(idx.head(arc));
            }
            weights.push(c * (1.0 - y));
        }
        support.sort_unstable();
        support.dedup();

        let mut best: Option<SphResult> = None;
        let offer = |r: SphResult, best: &mut Option<SphResult>| {
            if best.as_ref().is_none_or(|b| r.cost < b.cost) {
                *best = Some(r);
            }
        };

        if support.len() > 1 {
            if let Some(rebuilt) = mst_prune(idx, &active, root, &support, is_terminal, sws) {
                if !rebuilt.arcs.is_empty() {
                    offer(rebuilt, &mut best);
                }
            }
        }

        // A spread of starts, capped: this runs many times per node.
        let starts = 4.min(terminals.len()).max(1);
        for i in 0..starts {
            let start = terminals[i * terminals.len() / starts];
            if let Some(r) = shortest_path_heuristic(
                idx, &active, &weights, root, start, terminals, is_terminal, sws,
            ) {
                offer(r, &mut best);
            }
        }

        if let Some(current) = best.take() {
            let improved =
                key_path_exchange(idx, &active, root, &current, is_terminal, 8, kws, sws);
            best = Some(improved.unwrap_or(current));
        }

        let r = best?;
        if r.arcs.is_empty() {
            return None;
        }
        let mut nodes: Vec<NodeId> = Vec::with_capacity(r.arcs.len() + 1);
        nodes.push(root);
        for &a in &r.arcs {
            nodes.push(idx.tail(a));
            nodes.push(idx.head(a));
        }
        nodes.sort_unstable();
        nodes.dedup();
        Some(SteinerSolution::new(r.arcs, nodes, r.cost))
}

impl BranchAndCutSolver {

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
    /// The single gate every incumbent passes through.
    ///
    /// There used to be two verifiers: a connectivity-only check here and the
    /// strict one in `model::verifier`, which the top level applied afterwards.
    /// They disagreed, and the disagreement was not academic — on PACE
    /// instance105 the loose check accepted an arc set of cost 226 that left ten
    /// terminals unreachable, which became the incumbent, pruned the whole tree
    /// against itself and produced a proof of optimality at a cost no tree has.
    fn verify_solution(&self, solution: &SteinerSolution) -> bool {
        crate::model::verify_solution(&self.graph, self.root, &self.terminals, solution).is_valid
    }

    fn create_children(&mut self, parent_id: u64, branch_var: ArcId) {
        let parent = &self.tree.nodes[parent_id as usize];
        let parent_depth = parent.depth;
        let parent_fixings = parent.fixings.clone();

        // Branch on a single arc: {y_a = 0} and {y_a = 1} partition the feasible
        // set. Fixing both anti-parallel arcs in the down child would leave the
        // case y_a = 0, y_reverse = 1 in neither child and lose optima.

        // Child 0: y_a = 0
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

        // Child 1: y_a = 1
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

    /// The dual bound is the weakest bound among the open nodes.
    ///
    /// An empty queue means every node was closed by a genuine prune, so nothing
    /// cheaper than the incumbent survives anywhere and the incumbent is optimal.
    /// That inference is only available when the search actually finished, which
    /// is why an abandoned node is pushed back before this is called.
    fn update_global_dual_bound(&mut self) {
        let from_queue = if self.tree.open_nodes.is_empty() {
            if self.search_incomplete {
                // The queue emptied because work was abandoned, not because the
                // tree was exhausted. It proves nothing.
                f64::NEG_INFINITY
            } else {
                self.tree.global_primal_bound
            }
        } else {
            self.tree
                .open_nodes
                .iter()
                .map(|&id| self.tree.nodes[id as usize].dual_bound)
                .fold(f64::INFINITY, f64::min)
        };
        // A dual bound never gets worse. The minimum over the open queue is a
        // valid bound and so is the value already held — which includes the one
        // seeded from ascend-and-prune before the first node was touched, and
        // which the old unconditional assignment threw away the moment a node
        // was queued with no bound of its own yet.
        //
        // It also never exceeds a value that is actually achieved. Node bounds
        // can run far above the cutoff — the node-local eliminations delete
        // everything that cannot beat the incumbent, so once the incumbent *is*
        // optimal the node LP jumps to whatever survives — and without this clamp
        // that leaks out as a dual bound above the primal, which reads as a
        // negative gap and, through `is_solved`, as a proof.
        let raised = from_queue.max(self.tree.global_dual_bound);
        self.tree.global_dual_bound = raised.min(self.tree.global_primal_bound);
    }
}

/// Hand the LP the time it actually has left, so one hard solve cannot overrun
/// the whole budget while the cut loop waits to check the clock between solves.
fn arm(lp: &mut LpRelaxation, deadline: Option<Instant>) {
    lp.time_limit_secs = deadline
        .map(|d| d.saturating_duration_since(Instant::now()).as_secs_f64())
        .unwrap_or(f64::INFINITY);
}

enum NodeResult {
    /// The node is finished: nothing cheaper than the incumbent lives below it.
    Pruned,
    IntegerFeasible(SteinerSolution),
    Branch(ArcId),
    /// The node could not be finished — the clock ran out, the LP did not solve,
    /// or there was no fractional variable to branch on. It stays open, and the
    /// search must not claim to have proved anything.
    ///
    /// Treating this as a prune is how a search reports a false optimum: the last
    /// node leaves the queue, `update_global_dual_bound` sees an empty queue and
    /// sets the dual bound to the incumbent, and the solver announces a proof it
    /// never had.
    Abandoned,
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
