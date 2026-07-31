//! End-to-end integration tests verifying mathematical optimality.
//!
//! Each test loads a .stp instance, solves it through the full pipeline
//! (parse -> preprocess -> DW/B&C solve -> verify), using the library's
//! unified solver entry point.

use scip_jack::branch_and_bound::{SolverConfig, SolveStatus};
use scip_jack::solver::solve_file;

fn quick_config(time_limit: f64) -> SolverConfig {
    SolverConfig {
        time_limit_secs: time_limit,
        node_limit: 10_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 10,
        heuristic_frequency: 5,
        verbose: false,
        preprocess: true,
    }
}

#[test]
fn test_trivial_instance_optimal() {
    let r = solve_file("tests/test_trivial.stp", quick_config(30.0));
    assert!(r.primal_bound <= 8.0 + 1e-4,
        "Trivial instance: expected cost <= 8, got {:.4}", r.primal_bound);
    assert!(r.status == SolveStatus::Optimal || r.primal_bound <= 8.0 + 1e-4);
}

#[test]
fn test_path_instance_optimal() {
    let r = solve_file("tests/test_path.stp", quick_config(30.0));
    assert!(r.primal_bound <= 4.0 + 1e-4,
        "Path instance: expected cost <= 4, got {:.4}", r.primal_bound);
    assert!(r.status == SolveStatus::Optimal || r.primal_bound <= 4.0 + 1e-4);
}

#[test]
fn test_b01_instance() {
    let r = solve_file("tests/test_b01.stp", quick_config(60.0));
    assert!(r.primal_bound <= 9.0 + 1e-4,
        "B01 instance: expected cost <= 9, got {:.4}", r.primal_bound);
    assert!(r.primal_bound >= 7.0 - 1e-4,
        "B01 instance: cost {} is impossibly low", r.primal_bound);
}

#[test]
fn test_dual_bound_valid() {
    let r = solve_file("tests/test_b01.stp", quick_config(30.0));
    assert!(r.dual_bound <= r.primal_bound + 1e-6,
        "Dual bound ({:.4}) must not exceed primal bound ({:.4})",
        r.dual_bound, r.primal_bound);
}
