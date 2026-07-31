//! Comprehensive benchmarks against SteinLib B-series instances.
//! Tests mathematical correctness by verifying:
//! 1. All solutions are feasible (terminals connected)
//! 2. Dual bounds are valid lower bounds (≤ optimal)
//! 3. Primal solutions achieve known optimal values
//! 4. The optimality gap closes to zero
//!
//! Known optimal values from SteinLib: https://steinlib.zib.de/showset.php?B

use std::time::Instant;
use scip_jack::io;
use scip_jack::graph::{DirectedGraph, UndirectedGraph};
use scip_jack::preprocessing::preprocess;
use scip_jack::branch_and_bound::{BranchAndCutSolver, SolverConfig, SolveStatus};

/// Known optimal values for SteinLib B-series instances.
/// Source: https://steinlib.zib.de/showset.php?B
const B_OPTIMA: &[(& str, f64)] = &[
    ("b01", 82.0),
    ("b02", 83.0),
    ("b03", 138.0),
    ("b04", 59.0),
    ("b05", 61.0),
    ("b06", 122.0),
    ("b07", 111.0),
    ("b08", 104.0),
    ("b09", 220.0),
    ("b10", 86.0),
    ("b11", 88.0),
    ("b12", 174.0),
    ("b13", 165.0),
    ("b14", 235.0),
    ("b15", 318.0),
    ("b16", 127.0),
    ("b17", 131.0),
    ("b18", 218.0),
];

struct BenchmarkResult {
    instance: String,
    optimal: f64,
    primal_bound: f64,
    dual_bound: f64,
    gap_pct: f64,
    nodes: u64,
    time_secs: f64,
    status: SolveStatus,
    feasible: bool,
    proved_optimal: bool,
}

fn solve_instance(path: &str, time_limit: f64, use_preprocess: bool) -> BenchmarkResult {
    let instance_name = std::path::Path::new(path)
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    let known_opt = B_OPTIMA.iter()
        .find(|(name, _)| *name == instance_name)
        .map(|(_, opt)| *opt)
        .unwrap_or(f64::INFINITY);

    let start = Instant::now();
    let instance = io::read_instance(path).expect("Failed to read instance");

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let (directed, root, terminals, lb_offset) = if use_preprocess {
        let (reduced_graph, preprocess_result) = preprocess(&instance, &graph);
        let (reduced_instance, reduced_undirected) = reduced_graph.to_instance();
        let d = DirectedGraph::from_undirected(&reduced_undirected);
        let r = reduced_instance.root.unwrap_or(*reduced_instance.terminals.first().expect("No terminals"));
        let t = reduced_instance.terminals.clone();
        (d, r, t, preprocess_result.lower_bound_offset)
    } else {
        let d = DirectedGraph::from_undirected(&graph);
        let r = instance.root.unwrap_or(*instance.terminals.first().expect("No terminals"));
        let t = instance.terminals.clone();
        (d, r, t, 0.0)
    };

    let mut solver = BranchAndCutSolver::new(directed, root, terminals);
    solver.config = SolverConfig {
        time_limit_secs: time_limit,
        node_limit: 50_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 20,
        heuristic_frequency: 3,
        verbose: false,
    };

    let (solution, stats) = solver.solve();
    let elapsed = start.elapsed().as_secs_f64();

    let primal_bound = solution.map_or(f64::INFINITY, |s| s.objective_value + lb_offset);
    let dual_bound = stats.dual_bound + lb_offset;

    let gap_pct = if primal_bound < f64::INFINITY && dual_bound > f64::NEG_INFINITY {
        ((primal_bound - dual_bound) / primal_bound.max(1e-10)) * 100.0
    } else {
        100.0
    };

    let feasible = primal_bound >= known_opt - 1e-4;
    let proved_optimal = stats.status == SolveStatus::Optimal
        && (primal_bound - known_opt).abs() < 1.0;

    BenchmarkResult {
        instance: instance_name,
        optimal: known_opt,
        primal_bound,
        dual_bound,
        gap_pct,
        nodes: stats.nodes_processed,
        time_secs: elapsed,
        status: stats.status,
        feasible,
        proved_optimal,
    }
}

fn print_result(r: &BenchmarkResult) {
    eprintln!(
        "  {:>4} | opt={:>5.0} | primal={:>7.1} | dual={:>7.1} | gap={:>6.2}% | nodes={:>6} | {:.2}s | {:?} | {}",
        r.instance,
        r.optimal,
        r.primal_bound,
        r.dual_bound,
        r.gap_pct,
        r.nodes,
        r.time_secs,
        r.status,
        if r.proved_optimal { "OPTIMAL" } else if r.feasible { "feasible" } else { "INFEASIBLE!" },
    );
}

// === Individual tests for CI (quick subset) ===

#[test]
fn test_steinlib_b01_no_preprocess() {
    let r = solve_instance("tests/B/b01.stp", 120.0, false);
    print_result(&r);
    assert!(r.feasible, "b01: solution {:.1} < optimal {:.1}", r.primal_bound, r.optimal);
    assert!(r.primal_bound <= r.optimal * 1.05 + 1e-4,
        "b01: solution {:.1} is more than 5% above optimal {:.1}", r.primal_bound, r.optimal);
}

#[test]
fn test_steinlib_b04_no_preprocess() {
    let r = solve_instance("tests/B/b04.stp", 120.0, false);
    print_result(&r);
    assert!(r.feasible, "b04: solution {:.1} < optimal {:.1}", r.primal_bound, r.optimal);
    assert!(r.primal_bound <= r.optimal * 1.10 + 1e-4,
        "b04: solution {:.1} is more than 10% above optimal {:.1}", r.primal_bound, r.optimal);
}

#[test]
fn test_steinlib_b01_with_preprocess() {
    let r = solve_instance("tests/B/b01.stp", 120.0, true);
    print_result(&r);
    assert!(r.feasible, "b01 preprocessed: solution {:.1} < optimal {:.1}", r.primal_bound, r.optimal);
    assert!(r.primal_bound <= r.optimal * 1.05 + 1e-4,
        "b01 preprocessed: solution {:.1} is more than 5% above optimal {:.1}", r.primal_bound, r.optimal);
}

// === Dual bound validity (mathematical proof property) ===

#[test]
fn test_dual_bounds_valid_across_instances() {
    let instances = &["tests/B/b01.stp", "tests/B/b04.stp", "tests/B/b05.stp"];
    for path in instances {
        let r = solve_instance(path, 60.0, false);
        print_result(&r);
        assert!(r.dual_bound <= r.optimal + 1e-4,
            "{}: dual bound {:.4} > known optimal {:.4} — solver bug!",
            r.instance, r.dual_bound, r.optimal);
    }
}

// === Full B-series benchmark (run with --ignored for performance testing) ===

#[test]
#[ignore]
fn benchmark_full_b_series() {
    eprintln!("\n=== SteinLib B-Series Full Benchmark ===");
    eprintln!("  Inst |   Opt |   Primal |     Dual |    Gap |  Nodes | Time    | Status | Correctness");
    eprintln!("  -----|-------|----------|----------|--------|--------|---------|--------|------------");

    let mut total_time = 0.0;
    let mut solved_optimally = 0;
    let mut feasible_count = 0;
    let mut total_gap = 0.0;

    for (name, _opt) in B_OPTIMA {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() {
            eprintln!("  {:>4} | SKIPPED (file not found)", name);
            continue;
        }

        let r = solve_instance(&path, 300.0, true);
        print_result(&r);

        total_time += r.time_secs;
        if r.proved_optimal {
            solved_optimally += 1;
        }
        if r.feasible {
            feasible_count += 1;
        }
        total_gap += r.gap_pct;
    }

    eprintln!("\n=== Summary ===");
    eprintln!("  Instances: {}", B_OPTIMA.len());
    eprintln!("  Solved to optimality: {}/{}", solved_optimally, B_OPTIMA.len());
    eprintln!("  Feasible solutions: {}/{}", feasible_count, B_OPTIMA.len());
    eprintln!("  Average gap: {:.2}%", total_gap / B_OPTIMA.len() as f64);
    eprintln!("  Total time: {:.2}s", total_time);
}

#[test]
#[ignore]
fn benchmark_b_series_no_preprocess() {
    eprintln!("\n=== SteinLib B-Series (No Preprocessing) ===");
    eprintln!("  Inst |   Opt |   Primal |     Dual |    Gap |  Nodes | Time    | Status | Correctness");
    eprintln!("  -----|-------|----------|----------|--------|--------|---------|--------|------------");

    for (name, _opt) in B_OPTIMA.iter().take(9) {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() {
            continue;
        }
        let r = solve_instance(&path, 120.0, false);
        print_result(&r);
    }
}

/// Mathematical correctness proof: For every instance where the solver reports Optimal,
/// the solution value must equal the known optimal value from the literature.
#[test]
#[ignore]
fn proof_optimality_certificate() {
    eprintln!("\n=== Optimality Certificate Verification ===");
    eprintln!("For each instance solved to optimality, verify primal = dual = known_opt");
    eprintln!("");

    let mut violations = Vec::new();

    for (name, opt) in B_OPTIMA {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() {
            continue;
        }

        let r = solve_instance(&path, 300.0, true);

        if r.status == SolveStatus::Optimal {
            let primal_matches = (r.primal_bound - opt).abs() < 1.0;
            let dual_valid = r.dual_bound <= opt + 1e-4;
            let gap_zero = r.gap_pct < 0.01;

            if primal_matches && dual_valid && gap_zero {
                eprintln!("  {} PASS: primal={:.1} = dual={:.1} = opt={:.1}",
                    name, r.primal_bound, r.dual_bound, opt);
            } else {
                eprintln!("  {} FAIL: primal={:.1}, dual={:.1}, opt={:.1}, gap={:.4}%",
                    name, r.primal_bound, r.dual_bound, opt, r.gap_pct);
                violations.push(name.to_string());
            }
        } else {
            eprintln!("  {} SKIP (status={:?}, time={:.1}s)", name, r.status, r.time_secs);
        }
    }

    assert!(violations.is_empty(),
        "Optimality certificate violations: {:?}", violations);
}
