//! Benchmarks against SteinLib B-series instances with known optimal values.
//! Tests correctness of the solver by comparing against published optima.

use scip_jack::io;
use scip_jack::graph::{DirectedGraph, UndirectedGraph};
use scip_jack::preprocessing::preprocess;
use scip_jack::branch_and_bound::{BranchAndCutSolver, SolverConfig, SolveStatus};

/// Run solver WITHOUT preprocessing to isolate B&C correctness.
fn solve_no_preprocess(path: &str, time_limit: f64) -> (f64, SolveStatus) {
    let instance = io::read_instance(path).expect("Failed to read instance");

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let directed = DirectedGraph::from_undirected(&graph);
    let root = instance.root.unwrap_or(*instance.terminals.first().expect("No terminals"));
    let terminals = instance.terminals.clone();

    let mut solver = BranchAndCutSolver::new(directed, root, terminals);
    solver.config = SolverConfig {
        time_limit_secs: time_limit,
        node_limit: 10_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 20,
        heuristic_frequency: 3,
        verbose: false,
    };

    let (solution, stats) = solver.solve();
    let obj = solution.map_or(f64::INFINITY, |s| s.objective_value);
    (obj, stats.status)
}

/// Run solver WITH preprocessing.
fn solve_with_preprocess(path: &str, time_limit: f64) -> (f64, SolveStatus) {
    let instance = io::read_instance(path).expect("Failed to read instance");

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let (reduced_graph, preprocess_result) = preprocess(&instance, &graph);
    let (reduced_instance, reduced_undirected) = reduced_graph.to_instance();
    let directed = DirectedGraph::from_undirected(&reduced_undirected);

    let root = reduced_instance.root.unwrap_or(*reduced_instance.terminals.first().expect("No terminals"));
    let terminals = reduced_instance.terminals.clone();

    let mut solver = BranchAndCutSolver::new(directed, root, terminals);
    solver.config = SolverConfig {
        time_limit_secs: time_limit,
        node_limit: 10_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 20,
        heuristic_frequency: 3,
        verbose: false,
    };

    let (solution, stats) = solver.solve();
    let obj = solution.map_or(f64::INFINITY, |s| s.objective_value + preprocess_result.lower_bound_offset);
    (obj, stats.status)
}

// Known optimal values from SteinLib (https://steinlib.zib.de/showset.php?B)
const B01_OPT: f64 = 82.0;
const B04_OPT: f64 = 59.0;

#[test]
fn test_steinlib_b01_no_preprocess() {
    let (obj, _status) = solve_no_preprocess("tests/B/b01.stp", 120.0);
    eprintln!("b01 no-preprocess: obj={:.1}, optimal={:.1}", obj, B01_OPT);
    // Solution must be >= optimal (can't be cheaper than optimal!)
    assert!(obj >= B01_OPT - 1e-4,
        "b01: solution {:.1} < optimal {:.1} — infeasible solution!", obj, B01_OPT);
    assert!(obj <= B01_OPT * 1.20 + 1e-4,
        "b01: solution {:.1} is more than 20% above optimal {:.1}", obj, B01_OPT);
}

#[test]
fn test_steinlib_b04_no_preprocess() {
    let (obj, _status) = solve_no_preprocess("tests/B/b04.stp", 120.0);
    eprintln!("b04 no-preprocess: obj={:.1}, optimal={:.1}", obj, B04_OPT);
    assert!(obj <= B04_OPT * 1.20 + 1e-4,
        "b04: solution {:.1} is more than 20% above optimal {:.1}", obj, B04_OPT);
}

#[test]
fn test_steinlib_b01_with_preprocess() {
    let (obj, _status) = solve_with_preprocess("tests/B/b01.stp", 120.0);
    eprintln!("b01 with-preprocess: obj={:.1}, optimal={:.1}", obj, B01_OPT);
    // Check that preprocessing doesn't break correctness
    assert!(obj <= B01_OPT * 1.20 + 1e-4,
        "b01: preprocessed solution {:.1} is more than 20% above optimal {:.1}", obj, B01_OPT);
}
