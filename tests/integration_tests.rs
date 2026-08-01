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
        cycle_cuts: true,
        partition_cuts: true,
        activation_rank_cuts: false,
        tf_cuts: true,
    }
}

/// Instances whose SteinLib reference optimum the solver must reproduce exactly.
///
/// These are regression guards for two soundness bugs that each produced a
/// *proved* answer one unit above the true optimum:
///
/// * `c09` (707): branch-and-cut branched on `z_e = y_uv + y_vu` with children
///   `{y_uv = 0, y_vu = 0}` and `{y_uv = 1}`, leaving `y_uv = 0, y_vu = 1`
///   in neither child. Every optimum traversing an edge in that orientation was
///   discarded and the search reported 708 as proved.
/// * `b18` (218): the reduction package returned 219 while the unreduced solve
///   returned 218.
const REFERENCE_OPTIMA: &[(&str, &str, f64)] = &[
    ("tests/B/b18.stp", "b18", 218.0),
    ("tests/C/c03.stp", "c03", 754.0),
    ("tests/C/c08.stp", "c08", 509.0),
    ("tests/C/c09.stp", "c09", 707.0),
];

#[test]
fn reference_optima_are_reproduced_exactly() {
    for &(path, name, reference) in REFERENCE_OPTIMA {
        let r = solve_file(path, quick_config(600.0));
        assert_eq!(
            r.status,
            SolveStatus::Optimal,
            "{name}: expected a proved optimum, got {:?}",
            r.status
        );
        assert!(
            r.primal_bound >= reference - 1e-6,
            "{name}: returned {} below the reference optimum {reference} — the \
             solution is infeasible or the instance was altered",
            r.primal_bound
        );
        assert!(
            r.primal_bound <= reference + 1e-6,
            "{name}: proved {} but the reference optimum is {reference} — some \
             reduction, cut, or branching rule discarded an optimal solution",
            r.primal_bound
        );
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

/// A time limit must never turn into a proof.
///
/// The branch-and-cut tree used to treat an unfinished node as a pruned one.
/// When the clock ran out inside the root's cut loop the node left the queue,
/// the empty queue was read as "everything was pruned", and the dual bound was
/// set to the incumbent — so the solver announced `Optimal` on a value it had
/// only guessed. PACE instance200 reported 6491 as proved against a true optimum
/// of 6393.
///
/// The property this pins is the one that matters: a claimed optimum must be the
/// optimum, whatever the budget.
#[test]
fn a_tight_budget_never_produces_a_false_proof() {
    let hard: &[(&str, &str, f64)] = &[
        ("tests/C/c18.stp", "c18", 113.0),
        ("tests/D/d18.stp", "d18", 223.0),
        ("tests/D/d19.stp", "d19", 310.0),
        ("tests/E/e18.stp", "e18", 564.0),
        ("tests/E/e19.stp", "e19", 758.0),
    ];

    for &(path, name, reference) in hard {
        for &budget in &[0.02, 0.1, 0.35, 1.0, 2.5] {
            let r = solve_file(path, quick_config(budget));
            assert!(
                r.primal_bound >= reference - 1e-6,
                "{name} at {budget}s: returned {} below the true optimum {reference}",
                r.primal_bound
            );
            if r.status == SolveStatus::Optimal {
                assert!(
                    (r.primal_bound - reference).abs() < 1e-6,
                    "{name} at {budget}s: claimed {} is optimal, but the optimum is \
                     {reference} — the search reported a proof it did not have",
                    r.primal_bound
                );
            }
            assert!(
                r.dual_bound <= reference + 1e-6,
                "{name} at {budget}s: dual bound {} exceeds the optimum {reference}",
                r.dual_bound
            );
        }
    }
}
