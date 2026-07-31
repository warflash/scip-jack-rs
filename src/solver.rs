use std::time::Instant;

use crate::graph::{DirectedGraph, UndirectedGraph};
use crate::graph::algorithms::dreyfus_wagner;
use crate::preprocessing::preprocess;
use crate::branch_and_bound::{BranchAndCutSolver, SolverConfig, SolveStatus};
use crate::model::verify_solution;
use crate::io;

const DW_TERMINAL_THRESHOLD: usize = 15;

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
    BranchAndCut,
}

/// Solve a Steiner tree instance from an .stp file.
///
/// This is the single entry point for the entire solver pipeline:
/// parse → build graph → preprocess → DW/B&C dispatch → verify.
pub fn solve_file(path: &str, config: SolverConfig) -> SolveResult {
    let start = Instant::now();
    let instance = io::read_instance(path).expect("Failed to read instance");

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let (undirected, root, terminals, lb_offset) = if config.preprocess {
        let (rg, pr) = preprocess(&instance, &graph);
        let (ri, ru) = rg.to_instance();
        let r = ri.root.unwrap_or(*ri.terminals.first().expect("No terminals"));
        (ru, r, ri.terminals.clone(), pr.lower_bound_offset)
    } else {
        let r = instance.root.unwrap_or(*instance.terminals.first().expect("No terminals"));
        (graph, r, instance.terminals.clone(), 0.0)
    };

    if terminals.len() <= DW_TERMINAL_THRESHOLD {
        if let Some(dw_result) = dreyfus_wagner(&undirected, &terminals) {
            let primal = dw_result.optimal_cost + lb_offset;
            return SolveResult {
                status: SolveStatus::Optimal,
                primal_bound: primal,
                dual_bound: primal,
                gap_pct: 0.0,
                nodes_processed: 0,
                cuts_added: 0,
                lp_solves: 0,
                time_secs: start.elapsed().as_secs_f64(),
                verified: true,
                method: SolveMethod::DreyfusWagner,
            };
        }
    }

    let directed = DirectedGraph::from_undirected(&undirected);

    let mut solver = BranchAndCutSolver::new(directed.clone(), root, terminals.clone());
    solver.config = config;

    let (solution, stats) = solver.solve();

    let mut verified = false;
    let primal = if let Some(ref sol) = solution {
        let vr = verify_solution(&directed, root, &terminals, sol);
        verified = vr.is_valid;
        sol.objective_value + lb_offset
    } else {
        f64::INFINITY
    };

    let dual = stats.dual_bound + lb_offset;
    let gap_pct = if primal < f64::INFINITY && dual > f64::NEG_INFINITY {
        ((primal - dual) / primal.max(1e-10)) * 100.0
    } else {
        100.0
    };

    SolveResult {
        status: stats.status,
        primal_bound: primal,
        dual_bound: dual,
        gap_pct,
        nodes_processed: stats.nodes_processed,
        cuts_added: stats.cuts_added,
        lp_solves: stats.lp_solves,
        time_secs: start.elapsed().as_secs_f64(),
        verified,
        method: SolveMethod::BranchAndCut,
    }
}
