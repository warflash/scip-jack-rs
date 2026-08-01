//! Deterministic, time-budgeted SteinLib benchmark campaign for CI.
//!
//! The campaign is intentionally a binary instead of a collection of Rust
//! tests: one process owns the clock and visits every instance in a fixed
//! order. That makes the number of completed instances a useful performance
//! signal as the solver improves.

use std::env;
use std::fs;
use std::time::Instant;

use scip_jack::branch_and_bound::SolverConfig;
use scip_jack::solver::solve_file;

const DEFAULT_BUDGET_SECS: f64 = 180.0;

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

const SERIES: &[(&str, &[(&str, f64)])] = &[
    ("B", B_OPTIMA),
    ("C", C_OPTIMA),
    ("D", D_OPTIMA),
    ("E", E_OPTIMA),
];

struct CaseResult {
    series: &'static str,
    name: &'static str,
    optimal: f64,
    primal: f64,
    dual: f64,
    gap_pct: f64,
    elapsed_secs: f64,
    status: String,
    verified: bool,
}

fn argument(name: &str, default: f64) -> f64 {
    let args: Vec<String> = env::args().collect();
    args.windows(2)
        .find(|pair| pair[0] == name)
        .map(|pair| {
            pair[1]
                .parse::<f64>()
                .unwrap_or_else(|_| panic!("{name} must be a number"))
        })
        .unwrap_or(default)
}

fn solve_case(
    series: &'static str,
    name: &'static str,
    path: &str,
    optimal: f64,
    time_limit_secs: f64,
) -> CaseResult {
    let config = SolverConfig {
        time_limit_secs,
        node_limit: 50_000,
        gap_tolerance: 1e-6,
        cut_rounds_per_node: 20,
        heuristic_frequency: 3,
        verbose: false,
        preprocess: true,
        cycle_cuts: true,
        partition_cuts: true,
        activation_rank_cuts: false,
        tf_cuts: true,
    };

    let result = solve_file(path, config);

    CaseResult {
        series,
        name,
        optimal,
        primal: result.primal_bound,
        dual: result.dual_bound,
        gap_pct: result.gap_pct,
        elapsed_secs: result.time_secs,
        status: format!("{:?}", result.status),
        verified: result.verified,
    }
}

fn panic_result(
    series: &'static str,
    name: &'static str,
    optimal: f64,
    elapsed_secs: f64,
) -> CaseResult {
    CaseResult {
        series,
        name,
        optimal,
        primal: f64::NAN,
        dual: f64::NAN,
        gap_pct: 100.0,
        elapsed_secs,
        status: "Panic".to_string(),
        verified: false,
    }
}

fn write_results(results: &[CaseResult], total_cases: usize, budget_secs: f64, started: Instant) {
    let elapsed_secs = started.elapsed().as_secs_f64();
    let remaining = total_cases.saturating_sub(results.len());
    let mut records = Vec::with_capacity(results.len() + 2);

    for result in results {
        records.push(format!(
            "    {{\"name\":\"SteinLib/CI/{}/{} runtime\",\"unit\":\"seconds\",\"value\":{:.6}}}",
            result.series, result.name, result.elapsed_secs
        ));
    }
    records.push(format!(
        "    {{\"name\":\"SteinLib/CI/campaign/benchmarks remaining\",\"unit\":\"benchmarks\",\"value\":{remaining}}}"
    ));
    records.push(format!(
        "    {{\"name\":\"SteinLib/CI/campaign/elapsed\",\"unit\":\"seconds\",\"value\":{elapsed_secs:.6}}}"
    ));

    let json = format!("[\n{}\n]\n", records.join(",\n"));
    fs::write("ci-benchmark-results.json", json).expect("write ci-benchmark-results.json");

    let mut summary = String::new();
    summary.push_str("# SteinLib three-minute CI benchmark campaign\n\n");
    summary.push_str(&format!(
        "Completed **{} / {}** instances in **{:.1}s** (budget: {:.0}s).\n\n",
        results.len(),
        total_cases,
        elapsed_secs,
        budget_secs
    ));
    summary.push_str("The fixed order is B01–B18, C01–C20, D01–D20, then E01–E20.\n\n");
    summary.push_str("| # | Instance | Time (s) | Status | Primal | Dual | Gap | Verified |\n");
    summary.push_str("|---:|---|---:|---|---:|---:|---:|:---:|\n");
    for (index, result) in results.iter().enumerate() {
        let primal = if result.primal.is_finite() {
            format!("{:.1}", result.primal)
        } else {
            "-".to_string()
        };
        let dual = if result.dual.is_finite() {
            format!("{:.1}", result.dual)
        } else {
            "-".to_string()
        };
        summary.push_str(&format!(
            "| {} | {}/{} | {:.3} | {} | {} / {:.0} | {} | {:.1}% | {} |\n",
            index + 1,
            result.series,
            result.name,
            result.elapsed_secs,
            result.status,
            primal,
            result.optimal,
            dual,
            result.gap_pct,
            result.verified
        ));
    }
    fs::write("ci-benchmark-summary.md", summary).expect("write ci-benchmark-summary.md");
}

fn main() {
    let budget_secs = argument("--budget-secs", DEFAULT_BUDGET_SECS);
    assert!(budget_secs > 0.0, "--budget-secs must be positive");

    let total_cases: usize = SERIES.iter().map(|(_, cases)| cases.len()).sum();
    let campaign_started = Instant::now();
    let deadline = campaign_started + std::time::Duration::from_secs_f64(budget_secs);
    let mut results = Vec::new();
    let mut ordinal = 0;

    println!("SteinLib CI campaign: {budget_secs:.0}s total budget, {total_cases} instances");

    'campaign: for (series, cases) in SERIES {
        for &(name, optimal) in *cases {
            let remaining_secs = deadline
                .saturating_duration_since(Instant::now())
                .as_secs_f64();
            if remaining_secs <= 0.0 {
                println!(
                    "BUDGET EXHAUSTED after {} completed instances; remaining series are skipped",
                    results.len()
                );
                break 'campaign;
            }

            ordinal += 1;
            // Cap each instance so one hard case cannot eat the whole campaign.
            // The global deadline alone is not enough: it is only consulted
            // between instances.
            let time_limit_secs = remaining_secs.min(budget_secs / 4.0);
            let path = format!("tests/{series}/{name}.stp");
            println!(
                "START {ordinal:02}/{total_cases} {series}/{name} ({time_limit_secs:.1}s remaining)"
            );
            let case_started = Instant::now();
            let result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                solve_case(series, name, &path, optimal, time_limit_secs)
            })) {
                Ok(result) => result,
                Err(_) => {
                    println!(
                        "ERROR {ordinal:02}/{total_cases} {series}/{name} solver panicked; recording and continuing"
                    );
                    panic_result(series, name, optimal, case_started.elapsed().as_secs_f64())
                }
            };
            println!(
                "DONE  {ordinal:02}/{total_cases} {series}/{name} time={:.3}s status={} primal={:.1}/{:.1} dual={:.1} gap={:.1}% verified={}",
                result.elapsed_secs,
                result.status,
                result.primal,
                result.optimal,
                result.dual,
                result.gap_pct,
                result.verified
            );
            results.push(result);
        }
    }

    write_results(&results, total_cases, budget_secs, campaign_started);
    println!(
        "CAMPAIGN SUMMARY completed={} total={} elapsed={:.3}s",
        results.len(),
        total_cases,
        campaign_started.elapsed().as_secs_f64()
    );
}
