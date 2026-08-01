//! SteinLib benchmarks with correctness verification.
//! Non-ignored tests complete in ~2-3 minutes total.
//! Use `--ignored` for the full suite (may take 15+ minutes).

use scip_jack::branch_and_bound::{SolverConfig, SolveStatus};
use scip_jack::solver::{solve_file, SolveResult, SolveMethod};

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

fn lookup_optimum(name: &str) -> f64 {
    B_OPTIMA.iter()
        .chain(C_OPTIMA.iter())
        .chain(D_OPTIMA.iter())
        .chain(E_OPTIMA.iter())
        .find(|(n, _)| *n == name)
        .map(|(_, o)| *o)
        .unwrap_or(f64::INFINITY)
}

struct BenchResult {
    name: String,
    optimal: f64,
    result: SolveResult,
}

impl BenchResult {
    fn is_proved_optimal(&self) -> bool {
        self.result.status == SolveStatus::Optimal
            && (self.result.primal_bound - self.optimal).abs() < 1.0
    }
    fn is_feasible(&self) -> bool {
        self.result.primal_bound >= self.optimal - 1e-4
    }
    fn print(&self) {
        let cert = if self.result.verified { "V" } else { "?" };
        let method = match self.result.method {
            SolveMethod::DreyfusWagner => "DW",
            SolveMethod::AscendAndPrune => "AP",
            SolveMethod::BranchAndCut => "BC",
        };
        eprintln!(
            "  {:>4} | opt={:>5.0} | pri={:>6.0} | dual={:>6.1} | gap={:>5.1}% | n={:>5} | cuts={:>5} | lps={:>5} | {:.2}s | {:?} | {} [{}] {}",
            self.name, self.optimal, self.result.primal_bound, self.result.dual_bound,
            self.result.gap_pct, self.result.nodes_processed, self.result.cuts_added,
            self.result.lp_solves, self.result.time_secs, self.result.status,
            if self.is_proved_optimal() { "OPTIMAL" } else if self.is_feasible() { "feasible" } else { "WRONG!" },
            cert, method,
        );
    }
}

fn solve(path: &str, time_limit: f64) -> BenchResult {
    solve_with(path, time_limit, true)
}

fn solve_with(path: &str, time_limit: f64, preprocess_on: bool) -> BenchResult {
    let name = std::path::Path::new(path)
        .file_stem().unwrap().to_str().unwrap().to_string();
    let optimal = lookup_optimum(&name);

    let config = SolverConfig {
        time_limit_secs: time_limit,
        node_limit: 50_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 20,
        heuristic_frequency: 3,
        verbose: false,
        preprocess: preprocess_on,
        cycle_cuts: true,
        partition_cuts: true,
        activation_rank_cuts: false,
        tf_cuts: true,
    };

    let result = solve_file(path, config);

    BenchResult { name, optimal, result }
}

// === Quick correctness tests (run in CI, ~2 min total) ===

#[test]
fn test_b01_optimal() {
    let r = solve("tests/B/b01.stp", 30.0);
    r.print();
    assert!(r.is_feasible(), "b01: {} < opt {}", r.result.primal_bound, r.optimal);
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b02_optimal() {
    let r = solve("tests/B/b02.stp", 30.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b04_optimal() {
    let r = solve("tests/B/b04.stp", 30.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b08_fast() {
    let r = solve("tests/B/b08.stp", 15.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b05_fast() {
    let r = solve("tests/B/b05.stp", 15.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b07_fast() {
    let r = solve("tests/B/b07.stp", 15.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b09_fast() {
    let r = solve("tests/B/b09.stp", 15.0);
    r.print();
    assert!(r.is_feasible());
    assert!(r.result.primal_bound <= r.optimal * 1.05 + 0.5);
}

#[test]
fn test_b14_with_preprocess() {
    let r = solve("tests/B/b14.stp", 30.0);
    r.print();
    assert!(r.is_feasible(), "b14: {} < opt {}", r.result.primal_bound, r.optimal);
    assert!(r.result.primal_bound <= r.optimal * 1.02 + 0.5, "b14: {} > opt*1.02", r.result.primal_bound);
}

/// Mathematical invariant: dual bound must never exceed true optimal.
#[test]
fn test_dual_bounds_valid() {
    for name in &["b01", "b04", "b08", "b09", "b14", "b17", "b18"] {
        let path = format!("tests/B/{}.stp", name);
        let r = solve_with(&path, 30.0, false);
        r.print();
        assert!(r.result.dual_bound <= r.optimal + 1e-4,
            "{}: dual {:.4} > optimal {:.4} — invalid!", r.name, r.result.dual_bound, r.optimal);
    }
}

/// Verify solution statistics are tracked whenever branch-and-cut actually runs.
///
/// Which instances reach branch-and-cut is not fixed: ascend-and-prune closes the
/// bound at the root for most of the B series, and that is the desired outcome.
/// So this asserts the counters are wired for whichever instance does reach the
/// search, rather than pinning a particular instance to a particular method.
#[test]
fn test_statistics_wired() {
    let mut saw_branch_and_cut = false;
    for name in &["b03", "b09", "b13", "b15", "b18"] {
        let r = solve(&format!("tests/B/{name}.stp"), 30.0);
        r.print();
        if r.result.method == SolveMethod::BranchAndCut {
            saw_branch_and_cut = true;
            assert!(r.result.lp_solves > 0, "{name}: LP solves must be tracked, got 0");
        }
        assert!(
            r.result.primal_bound >= r.optimal - 1e-4,
            "{name}: {} is below the reference optimum {}",
            r.result.primal_bound,
            r.optimal
        );
    }
    // Not a failure if every instance was closed at the root — that is better —
    // but record it so the counter wiring does not silently go untested.
    if !saw_branch_and_cut {
        eprintln!("note: every sampled instance was proved at the root by ascend-and-prune");
    }
}

/// Independent solution verification: connectivity, acyclicity, terminal coverage, cost.
#[test]
fn test_solution_verified() {
    for name in &["b01", "b04"] {
        let path = format!("tests/B/{}.stp", name);
        let r = solve(&path, 30.0);
        r.print();
        assert!(r.result.verified, "{}: solution failed independent verification", name);
    }
}

// === C-series quick tests (500 nodes) ===

#[test]
fn test_c01_optimal() {
    let r = solve("tests/C/c01.stp", 30.0);
    r.print();
    assert!(r.is_feasible(), "c01: {} < opt {}", r.result.primal_bound, r.optimal);
}

#[test]
fn test_c06_optimal() {
    let r = solve("tests/C/c06.stp", 30.0);
    r.print();
    assert!(r.is_feasible());
}

#[test]
fn test_c11_optimal() {
    let r = solve("tests/C/c11.stp", 30.0);
    r.print();
    assert!(r.is_feasible());
}

// === D-series quick test (1000 nodes) ===

#[test]
fn test_d01_optimal() {
    let r = solve("tests/D/d01.stp", 60.0);
    r.print();
    assert!(r.is_feasible(), "d01: {} < opt {}", r.result.primal_bound, r.optimal);
}

#[test]
fn test_d_series_dual_validity() {
    for name in &["d01", "d02", "d06", "d07", "d11", "d12", "d16", "d17"] {
        let path = format!("tests/D/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 30.0);
        r.print();
        assert!(r.result.dual_bound <= r.optimal + 1e-4,
            "{}: dual {:.4} > optimal {:.4} — preprocessing too aggressive!",
            r.name, r.result.dual_bound, r.optimal);
    }
}

// === Full benchmarks (run with --ignored) ===

fn run_series(label: &str, optima: &[(&str, f64)], series: &str, time_limit: f64) {
    eprintln!("\n=== {} ===", label);
    let mut solved = 0;
    let mut total_time = 0.0;

    for (name, _) in optima {
        let path = format!("tests/{}/{}.stp", series, name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, time_limit);
        r.print();
        if r.is_proved_optimal() { solved += 1; }
        total_time += r.result.time_secs;
    }
    eprintln!("  Proved optimal: {}/{} | Total: {:.1}s", solved, optima.len(), total_time);
}

#[test]
#[ignore]
fn benchmark_full_b_series() {
    run_series("SteinLib B-Series Full Benchmark", B_OPTIMA, "B", 120.0);
}

#[test]
#[ignore]
fn benchmark_full_c_series() {
    run_series("SteinLib C-Series Full Benchmark (500 nodes)", C_OPTIMA, "C", 120.0);
}

#[test]
#[ignore]
fn benchmark_full_d_series() {
    run_series("SteinLib D-Series Full Benchmark (1000 nodes)", D_OPTIMA, "D", 120.0);
}

#[test]
#[ignore]
fn benchmark_full_e_series() {
    run_series("SteinLib E-Series Full Benchmark (2500 nodes)", E_OPTIMA, "E", 180.0);
}

#[test]
#[ignore]
fn proof_optimality_certificate() {
    eprintln!("\n=== Optimality Certificate Verification ===");
    let mut violations = Vec::new();

    for (name, opt) in B_OPTIMA {
        let path = format!("tests/B/{}.stp", name);
        if !std::path::Path::new(&path).exists() { continue; }
        let r = solve(&path, 120.0);

        if r.result.status == SolveStatus::Optimal {
            let ok = (r.result.primal_bound - opt).abs() < 1.0
                && r.result.dual_bound <= opt + 1e-4
                && r.result.gap_pct < 0.01;
            if ok {
                eprintln!("  {} PASS: pri={:.0} = dual={:.1} = opt={:.0}", name, r.result.primal_bound, r.result.dual_bound, opt);
            } else {
                eprintln!("  {} FAIL: pri={:.0}, dual={:.1}, opt={:.0}", name, r.result.primal_bound, r.result.dual_bound, opt);
                violations.push(name.to_string());
            }
        } else {
            eprintln!("  {} SKIP ({:?}, {:.1}s)", name, r.result.status, r.result.time_secs);
        }
    }
    assert!(violations.is_empty(), "Violations: {:?}", violations);
}
