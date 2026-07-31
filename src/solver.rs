//! Top-level solve pipeline.
//!
//! ```text
//! read -> classical reductions -> ascend-and-prune -> exact finish
//! ```
//!
//! The exact finish is dynamic programming when the terminal set is small enough
//! for it to be cheap, and branch-and-cut otherwise. Most SteinLib B/C instances
//! never reach it: ascend-and-prune closes the bound at the root.

use std::time::Instant;

use crate::branch_and_bound::{BranchAndCutSolver, SolveStatus, SolverConfig};
use crate::graph::algorithms::dreyfus_wagner;
use crate::graph::{Cost, DirectedGraph, SteinerInstance, UndirectedGraph};
use crate::io;
use crate::model::verify_solution;
use crate::preprocessing::preprocess;
use crate::root_reduce::{tighten, ReduceConfig};

/// Only dispatch to the Dreyfus-Wagner DP when its `3^k * n` term is affordable.
/// The old code keyed off the terminal count alone, which is meaningless without
/// the graph size: 15 terminals on 500 nodes is 7e9 operations.
const DW_WORK_BUDGET: f64 = 5e7;

#[derive(Debug, Clone)]
pub struct SolveResult {
    pub status: SolveStatus,
    pub primal_bound: f64,
    pub dual_bound: f64,
    pub gap_pct: f64,
    pub nodes_processed: u64,
    pub cuts_added: u64,
    pub lp_solves: u64,
    pub time_secs: f64,
    pub verified: bool,
    pub method: SolveMethod,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SolveMethod {
    DreyfusWagner,
    /// Proved at the root by dual ascent and reduced-cost elimination.
    AscendAndPrune,
    BranchAndCut,
}

fn dw_is_affordable(num_terminals: usize, num_nodes: u32) -> bool {
    if num_terminals < 2 || num_terminals > 24 {
        return false;
    }
    let work = 3f64.powi(num_terminals as i32) * num_nodes as f64;
    work <= DW_WORK_BUDGET
}

/// Solve a Steiner tree instance held in memory.
pub fn solve(instance: &SteinerInstance, config: SolverConfig) -> SolveResult {
    let start = Instant::now();
    let deadline = start + std::time::Duration::from_secs_f64(config.time_limit_secs.max(0.001));

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let (mut work_graph, mut terminals) = if config.preprocess {
        let (rg, pr) = preprocess(instance, &graph);
        let (ri, ru) = rg.to_instance();
        if config.verbose {
            eprintln!(
                "[reduce] classical: {} -> {} nodes, {} -> {} edges",
                instance.num_nodes, ri.num_nodes, instance.num_edges, ri.num_edges
            );
            let _ = pr;
        }
        (ru, ri.terminals)
    } else {
        (graph, instance.terminals.clone())
    };

    if terminals.len() < 2 {
        return trivial_result(start, 0.0, SolveMethod::AscendAndPrune);
    }

    if let Some(r) = try_dreyfus_wagner(&work_graph, &terminals, start) {
        return r;
    }

    // Ascend-and-prune, then branch-and-cut, then — if the search improved the
    // incumbent without proving it — ascend-and-prune again with that better
    // cutoff. The heuristic's own bound is often several percent off, and the
    // reduced-cost eliminations scale with `UB - LB`, so a tighter cutoff
    // discovered during the search can collapse the instance on a second pass.
    let mut incoming_ub = Cost::INFINITY;
    let mut best: Option<SolveResult> = None;

    for pass in 0..2 {
        let reduce_config = ReduceConfig {
            deadline: Some(deadline),
            verbose: config.verbose,
            initial_upper_bound: incoming_ub,
            ..ReduceConfig::default()
        };
        let reduced = tighten(work_graph.clone(), terminals.clone(), &reduce_config);
        // Cap the first search so an unproved-but-improved incumbent still
        // leaves time for the second tightening pass to exploit it.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let pass_deadline = if pass == 0 {
            Instant::now() + remaining.mul_f64(0.4)
        } else {
            deadline
        };
        let outcome = finish(reduced, &config, start, pass_deadline);
        let improved = best.as_ref().is_none_or(|b| outcome.primal_bound < b.primal_bound);
        if improved {
            best = Some(outcome.clone());
        }
        let done = best.as_ref().map(|b| b.status == SolveStatus::Optimal).unwrap_or(false);
        if done || Instant::now() >= deadline {
            break;
        }
        let Some(b) = best.as_ref() else { break };
        if !b.primal_bound.is_finite() || b.primal_bound >= incoming_ub {
            break;
        }
        incoming_ub = b.primal_bound;
    }

    return best.unwrap_or_else(|| trivial_result(start, Cost::INFINITY, SolveMethod::AscendAndPrune));
}

/// Finish a tightened instance: exact DP when cheap, otherwise branch-and-cut.
fn finish(
    reduced: crate::root_reduce::Reduced,
    config: &SolverConfig,
    start: Instant,
    deadline: Instant,
) -> SolveResult {

    if config.verbose {
        eprintln!(
            "[reduce] after {} rounds: |V|={} |E|={} LB={:.1} UB={:.1}",
            reduced.rounds,
            reduced.graph.num_nodes,
            reduced.graph.edges.len(),
            reduced.lower_bound,
            reduced.upper_bound
        );
    }

    if reduced.proved_optimal(config.gap_tolerance.max(1e-6)) {
        let value = reduced.upper_bound;
        return SolveResult {
            status: SolveStatus::Optimal,
            primal_bound: value,
            dual_bound: value,
            gap_pct: 0.0,
            nodes_processed: 0,
            cuts_added: 0,
            lp_solves: 0,
            time_secs: start.elapsed().as_secs_f64(),
            verified: true,
            method: SolveMethod::AscendAndPrune,
        };
    }

    let work_graph = reduced.graph;
    let terminals = reduced.terminals;
    let root = reduced.root;
    let root_lower_bound = reduced.lower_bound;
    let root_upper_bound = reduced.upper_bound;

    // The reduced instance may now be small enough for the exact DP.
    if let Some(mut r) = try_dreyfus_wagner(&work_graph, &terminals, start) {
        // The DP solves the *reduced* instance, which only retains solutions
        // strictly cheaper than the incumbent. Keep whichever is better.
        if root_upper_bound < r.primal_bound {
            r.primal_bound = root_upper_bound;
            r.dual_bound = root_upper_bound;
        }
        return r;
    }

    let directed = DirectedGraph::from_undirected(&work_graph);
    let mut solver = BranchAndCutSolver::new(directed.clone(), root, terminals.clone());
    let remaining = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
    solver.config = SolverConfig { time_limit_secs: remaining, ..config.clone() };
    solver.seed_bounds(root_lower_bound, root_upper_bound);

    let (solution, stats) = solver.solve();

    let mut verified = false;
    let mut primal = root_upper_bound;
    if let Some(ref sol) = solution {
        let vr = verify_solution(&directed, root, &terminals, sol);
        verified = vr.is_valid;
        if verified && sol.objective_value < primal {
            primal = sol.objective_value;
        }
    }
    if !primal.is_finite() {
        verified = false;
    } else if solution.is_none() {
        // The incumbent came from the heuristic during ascend-and-prune; it was
        // built and pruned to a tree by construction.
        verified = true;
    }

    // The branch-and-cut runs on a graph that only retains solutions cheaper than
    // `root_upper_bound`, so its dual bound proves nothing above that value.
    let dual = stats.dual_bound.max(root_lower_bound).min(primal);
    let gap_pct = if primal.is_finite() && dual > f64::NEG_INFINITY {
        ((primal - dual) / primal.abs().max(1e-10)) * 100.0
    } else {
        100.0
    };

    let status = if primal.is_finite() && dual >= primal - config.gap_tolerance.max(1e-6) {
        SolveStatus::Optimal
    } else {
        stats.status
    };

    SolveResult {
        status,
        primal_bound: primal,
        dual_bound: dual,
        gap_pct: gap_pct.max(0.0),
        nodes_processed: stats.nodes_processed,
        cuts_added: stats.cuts_added,
        lp_solves: stats.lp_solves,
        time_secs: start.elapsed().as_secs_f64(),
        verified,
        method: SolveMethod::BranchAndCut,
    }
}

fn try_dreyfus_wagner(
    graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    start: Instant,
) -> Option<SolveResult> {
    if !dw_is_affordable(terminals.len(), graph.num_nodes) {
        return None;
    }
    let dw = dreyfus_wagner(graph, terminals)?;
    Some(SolveResult {
        status: SolveStatus::Optimal,
        primal_bound: dw.optimal_cost,
        dual_bound: dw.optimal_cost,
        gap_pct: 0.0,
        nodes_processed: 0,
        cuts_added: 0,
        lp_solves: 0,
        time_secs: start.elapsed().as_secs_f64(),
        verified: true,
        method: SolveMethod::DreyfusWagner,
    })
}

fn trivial_result(start: Instant, value: Cost, method: SolveMethod) -> SolveResult {
    SolveResult {
        status: SolveStatus::Optimal,
        primal_bound: value,
        dual_bound: value,
        gap_pct: 0.0,
        nodes_processed: 0,
        cuts_added: 0,
        lp_solves: 0,
        time_secs: start.elapsed().as_secs_f64(),
        verified: true,
        method,
    }
}

/// Solve a Steiner tree instance from a SteinLib `.stp` file.
pub fn solve_file(path: &str, config: SolverConfig) -> SolveResult {
    let instance = io::read_instance(path).expect("Failed to read instance");
    solve(&instance, config)
}
