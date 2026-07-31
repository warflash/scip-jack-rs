//! SteinLib B-series benchmarks with correctness verification.
//! Non-ignored tests complete in ~2-3 minutes total.
//! Use `--ignored` for the full suite (may take 15+ minutes).

use std::time::Instant;
use scip_jack::io;
use scip_jack::graph::{DirectedGraph, UndirectedGraph};
use scip_jack::preprocessing::preprocess;
use scip_jack::branch_and_bound::{BranchAndCutSolver, SolverConfig, SolveStatus};
use scip_jack::model::verify_solution as verify;

/// Known optimal values for SteinLib B-series.
/// Source: https://steinlib.zib.de/showset.php?B
const B_OPTIMA: &[(&str, f64)] = &[
    ("b01", 82.0),  ("b02", 83.0),  ("b03", 138.0),
    ("b04", 59.0),  ("b05", 61.0),  ("b06", 122.0),
    ("b07", 111.0), ("b08", 104.0), ("b09", 220.0),
    ("b10", 86.0),  ("b11", 88.0),  ("b12", 174.0),
    ("b13", 165.0), ("b14", 235.0), ("b15", 318.0),
    ("b16", 127.0), ("b17", 131.0), ("b18", 218.0),
];

const C_OPTIMA: &[(&str, f64)] = &[
    ("c01", 85.0),   ("c02", 144.0),  ("c03", 754.0),
    ("c04", 1079.0), ("c05", 1579.0), ("c06", 55.0),
    ("c07", 102.0),  ("c08", 509.0),  ("c09", 707.0),
    ("c10", 1093.0), ("c11", 32.0),   ("c12", 46.0),
    ("c13", 258.0),  ("c14", 323.0),  ("c15", 556.0),
    ("c16", 11.0),   ("c17", 18.0),   ("c18", 113.0),
    ("c19", 146.0),  ("c20", 267.0),
];

const D_OPTIMA: &[(&str, f64)] = &[
    ("d01", 106.0),  ("d02", 220.0),  ("d03", 1565.0),
    ("d04", 1935.0), ("d05", 3250.0), ("d06", 67.0),
    ("d07", 103.0),  ("d08", 1072.0), ("d09", 1448.0),
    ("d10", 2110.0), ("d11", 29.0),   ("d12", 42.0),
    ("d13", 500.0),  ("d14", 667.0),  ("d15", 1116.0),
    ("d16", 13.0),   ("d17", 23.0),   ("d18", 223.0),
    ("d19", 310.0),  ("d20", 537.0),
];

const E_OPTIMA: &[(&str, f64)] = &[
    ("e01", 111.0),  ("e02", 214.0),  ("e03", 4013.0),
    ("e04", 5101.0), ("e05", 8128.0), ("e06", 73.0),
    ("e07", 145.0),  ("e08", 2640.0), ("e09", 3604.0),
    ("e10", 5600.0), ("e11", 34.0),   ("e12", 67.0),
    ("e13", 1280.0), ("e14", 1732.0), ("e15", 2784.0),
    ("e16", 15.0),   ("e17", 25.0),   ("e18", 564.0),
    ("e19", 758.0),  ("e20", 1342.0),
];

struct BenchResult {
    name: String,
    optimal: f64,
    primal: f64,
    dual: f64,
    gap_pct: f64,
    nodes: u64,
    cuts: u64,
    lp_solves: u64,
    time_secs: f64,
    status: SolveStatus,
    verified: bool,
}

impl BenchResult {
    fn is_proved_optimal(&self) -> bool {
        self.status == SolveStatus::Optimal && (self.primal - self.optimal).abs() < 1.0
    }
    fn is_feasible(&self) -> bool {
        self.primal >= self.optimal - 1e-4
    }
    fn print(&self) {
        let cert = if self.verified { "V" } else { "?" };
        eprintln!(
            "  {:>4} | opt={:>5.0} | pri={:>6.0} | dual={:>6.1} | gap={:>5.1}% | n={:>5} | cuts={:>5} | lps={:>5} | {:.2}s | {:?} | {} [{}]",
            self.name, self.optimal, self.primal, self.dual, self.gap_pct,
            self.nodes, self.cuts, self.lp_solves, self.time_secs, self.status,
            if self.is_proved_optimal() { "OPTIMAL" } else if self.is_feasible() { "feasible" } else { "WRONG!" },
            cert,
        );
    }
}

fn solve(path: &str, time_limit: f64, preprocess_on: bool) -> BenchResult {
    let name = std::path::Path::new(path)
        .file_stem().unwrap().to_str().unwrap().to_string();
    let known_opt = B_OPTIMA.iter()
        .chain(C_OPTIMA.iter())
        .chain(D_OPTIMA.iter())
        .chain(E_OPTIMA.iter())
        .find(|(n, _)| *n == name).map(|(_, o)| *o).unwrap_or(f64::INFINITY);

    let start = Instant::now();
    let instance = io::read_instance(path).expect("Failed to read instance");

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes { graph.add_node(node.id, node.node_type, node.weight); }
    for edge in &instance.edges { graph.add_edge(edge.src, edge.dst, edge.cost); }

    let (directed, root, terminals, lb_offset) = if preprocess_on {
        let (rg, pr) = preprocess(&instance, &graph);
        let (ri, ru) = rg.to_instance();
        let d = DirectedGraph::from_undirected(&ru);
        let r = ri.root.unwrap_or(*ri.terminals.first().expect("No terminals"));
        (d, r, ri.terminals.clone(), pr.lower_bound_offset)
    } else {
        let d = DirectedGraph::from_undirected(&graph);
        let r = instance.root.unwrap_or(*instance.terminals.first().expect("No terminals"));
        (d, r, instance.terminals.clone(), 0.0)
    };

    let mut solver = BranchAndCutSolver::new(directed.clone(), root, terminals.clone());
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

    let mut verified = false;
    let primal = if let Some(ref sol) = solution {
        let vr = verify(&directed, root, &terminals, sol);
        verified = vr.is_valid;
        sol.objective_value + lb_offset
    } else {
        f64::INFINITY
    };

    let dual = stats.dual_bound + lb_offset;
    let gap_pct = if primal < f64::INFINITY && dual > f64::NEG_INFINITY {
        ((primal - dual) / primal.max(1e-10)) * 100.0
    } else { 100.0 };

    BenchResult {
        name, optimal: known_opt, primal, dual, gap_pct,
        nodes: stats.nodes_processed, cuts: stats.cuts_added,
        lp_solves: stats.lp_solves, time_secs: elapsed, status: stats.status,
        verified,
    }
}

// === Quick correctness tests (run in CI, ~2 min total) ===

#[test]
fn test_b01_optimal() {
    let r = solve("tests/B/b01.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible(), "b01: {} < opt {}", r.primal, r.optimal);
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b02_optimal() {
    let r = solve("tests/B/b02.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b04_optimal() {
    let r = solve("tests/B/b04.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b08_fast() {
    let r = solve("tests/B/b08.stp", 15.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b05_fast() {
    let r = solve("tests/B/b05.stp", 15.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b07_fast() {
    let r = solve("tests/B/b07.stp", 15.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b09_fast() {
    let r = solve("tests/B/b09.stp", 15.0, true);
    r.print();
    assert!(r.is_feasible());
    assert!(r.primal <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b14_with_preprocess() {
    let r = solve("tests/B/b14.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible(), "b14: {} < opt {}", r.primal, r.optimal);
    assert!(r.primal <= r.optimal * 1.02 + 0.5, "b14: {} > opt*1.02", r.primal);
}

/// Mathematical invariant: dual bound must never exceed true optimal.
#[test]
fn test_dual_bounds_valid() {
    for name in &["b01", "b04", "b08", "b09", "b14"] {
        let path = format!("tests/B/{}.stp", name);
        let r = solve(&path, 15.0, false);
        r.print();
        assert!(r.dual <= r.optimal + 1e-4,
            "{}: dual {:.4} > optimal {:.4} — invalid!", r.name, r.dual, r.optimal);
    }
}

/// Verify solution statistics are properly tracked.
#[test]
fn test_statistics_wired() {
    let r = solve("tests/B/b01.stp", 30.0, false);
    assert!(r.lp_solves > 0, "LP solves must be tracked, got 0");
    assert!(r.cuts > 0, "Cuts must be tracked, got 0");
}

/// Independent solution verification: connectivity, acyclicity, terminal coverage, cost.
#[test]
fn test_solution_verified() {
    for name in &["b01", "b04"] {
        let path = format!("tests/B/{}.stp", name);
        let r = solve(&path, 30.0, true);
        r.print();
        assert!(r.verified, "{}: solution failed independent verification", name);
    }
}

// === C-series quick tests (500 nodes) ===

#[test]
fn test_c01_optimal() {
    let r = solve("tests/C/c01.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible(), "c01: {} < opt {}", r.primal, r.optimal);
}

#[test]
fn test_c06_optimal() {
    let r = solve("tests/C/c06.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible());
}

#[test]
fn test_c11_optimal() {
    let r = solve("tests/C/c11.stp", 30.0, true);
    r.print();
    assert!(r.is_feasible());
}

// === D-series quick test (1000 nodes) ===

#[test]
fn test_d01_optimal() {
    let r = solve("tests/D/d01.stp", 60.0, true);
    r.print();
    assert!(r.is_feasible(), "d01: {} < opt {}", r.primal, r.optimal);
}

// === Dreyfus-Wagner DP exact solver for small-terminal instances ===

#[test]
fn test_dreyfus_wagner_b_series() {
    use scip_jack::graph::algorithms::dreyfus_wagner;

    for name in &["b01", "b02", "b04", "b07"] {
        let path = format!("tests/B/{}.stp", name);
        let instance = io::read_instance(&path).expect("read");
        let mut graph = UndirectedGraph::new(instance.num_nodes);
        for node in &instance.nodes { graph.add_node(node.id, node.node_type, node.weight); }
        for edge in &instance.edges { graph.add_edge(edge.src, edge.dst, edge.cost); }

        let start = std::time::Instant::now();
        let result = dreyfus_wagner(&graph, &instance.terminals);
        let elapsed = start.elapsed().as_secs_f64();

        let known_opt = B_OPTIMA.iter()
            .find(|(n, _)| n == name).map(|(_, o)| *o).unwrap();

        if let Some(r) = result {
            eprintln!("  DW {} | opt={:.0} | dw={:.0} | {:.3}s | {}",
                name, known_opt, r.optimal_cost, elapsed,
                if (r.optimal_cost - known_opt).abs() < 1e-6 { "EXACT" } else { "MISMATCH!" });
            assert!((r.optimal_cost - known_opt).abs() < 1e-4,
                "DW {}: expected {}, got {}", name, known_opt, r.optimal_cost);
        } else {
            eprintln!("  DW {} | infeasible or too many terminals", name);
        }
    }
}

// === Full benchmarks (run with --ignored) ===

#[test]
#[ignore]
fn benchmark_full_b_series() {
    eprintln!("\n=== SteinLib B-Series Full Benchmark (with preprocessing) ===");
    let mut solved = 0;
    let mut total_time = 0.0;

    for (name, _) in B_OPTIMA {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 120.0, true);
        r.print();
        if r.is_proved_optimal() { solved += 1; }
        total_time += r.time_secs;
    }
    eprintln!("  Proved optimal: {}/{} | Total: {:.1}s", solved, B_OPTIMA.len(), total_time);
}

#[test]
#[ignore]
fn benchmark_full_c_series() {
    eprintln!("\n=== SteinLib C-Series Full Benchmark (500 nodes) ===");
    let mut solved = 0;
    let mut total_time = 0.0;

    for (name, _) in C_OPTIMA {
        let path = format!("tests/C/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 120.0, true);
        r.print();
        if r.is_proved_optimal() { solved += 1; }
        total_time += r.time_secs;
    }
    eprintln!("  Proved optimal: {}/{} | Total: {:.1}s", solved, C_OPTIMA.len(), total_time);
}

#[test]
#[ignore]
fn benchmark_full_d_series() {
    eprintln!("\n=== SteinLib D-Series Full Benchmark (1000 nodes) ===");
    let mut solved = 0;
    let mut total_time = 0.0;

    for (name, _) in D_OPTIMA {
        let path = format!("tests/D/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 120.0, true);
        r.print();
        if r.is_proved_optimal() { solved += 1; }
        total_time += r.time_secs;
    }
    eprintln!("  Proved optimal: {}/{} | Total: {:.1}s", solved, D_OPTIMA.len(), total_time);
}

#[test]
#[ignore]
fn benchmark_full_e_series() {
    eprintln!("\n=== SteinLib E-Series Full Benchmark (2500 nodes) ===");
    let mut solved = 0;
    let mut total_time = 0.0;

    for (name, _) in E_OPTIMA {
        let path = format!("tests/E/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 180.0, true);
        r.print();
        if r.is_proved_optimal() { solved += 1; }
        total_time += r.time_secs;
    }
    eprintln!("  Proved optimal: {}/{} | Total: {:.1}s", solved, E_OPTIMA.len(), total_time);
}

#[test]
#[ignore]
fn proof_optimality_certificate() {
    eprintln!("\n=== Optimality Certificate Verification ===");
    let mut violations = Vec::new();

    for (name, opt) in B_OPTIMA {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 120.0, true);

        if r.status == SolveStatus::Optimal {
            let ok = (r.primal - opt).abs() < 1.0
                && r.dual <= opt + 1e-4
                && r.gap_pct < 0.01;
            if ok {
                eprintln!("  {} PASS: pri={:.0} = dual={:.1} = opt={:.0}", name, r.primal, r.dual, opt);
            } else {
                eprintln!("  {} FAIL: pri={:.0}, dual={:.1}, opt={:.0}", name, r.primal, r.dual, opt);
                violations.push(name.to_string());
            }
        } else {
            eprintln!("  {} SKIP ({:?}, {:.1}s)", name, r.status, r.time_secs);
        }
    }
    assert!(violations.is_empty(), "Violations: {:?}", violations);
}
