pub mod graph;
pub mod model;
pub mod preprocessing;
pub mod separation;
pub mod heuristics;
pub mod branch_and_bound;
pub mod transformations;
pub mod io;
pub mod solver;

use std::env;
use branch_and_bound::SolverConfig;
use solver::SolveMethod;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage(&args[0]);
        return;
    }

    let input_file = &args[1];
    let config = parse_args(&args);

    eprintln!("scip-jack: Steiner Tree Problem Solver (Directed Cut Formulation)");
    eprintln!("================================================================");
    eprintln!();

    let result = solver::solve_file(input_file, config);

    let method_name = match result.method {
        SolveMethod::DreyfusWagner => "Dreyfus-Wagner DP",
        SolveMethod::BranchAndCut => "Branch-and-Cut",
    };

    eprintln!("Results ({}):", method_name);
    eprintln!("  Status: {:?}", result.status);
    eprintln!("  Primal bound: {:.6}", result.primal_bound);
    eprintln!("  Dual bound: {:.6}", result.dual_bound);
    eprintln!("  Gap: {:.4}%", result.gap_pct);
    eprintln!("  Nodes processed: {}", result.nodes_processed);
    eprintln!("  Cuts added: {}", result.cuts_added);
    eprintln!("  LP solves: {}", result.lp_solves);
    eprintln!("  Time: {:.3}s", result.time_secs);
    eprintln!("  Verified: {}", result.verified);

    if result.primal_bound < f64::INFINITY {
        println!("{:.6}", result.primal_bound);
    }
}

fn parse_args(args: &[String]) -> SolverConfig {
    let mut config = SolverConfig::default();

    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--time-limit" | "-t" => {
                if i + 1 < args.len() {
                    config.time_limit_secs = args[i + 1].parse().unwrap_or(3600.0);
                    i += 1;
                }
            }
            "--node-limit" | "-n" => {
                if i + 1 < args.len() {
                    config.node_limit = args[i + 1].parse().unwrap_or(1_000_000);
                    i += 1;
                }
            }
            "--gap" | "-g" => {
                if i + 1 < args.len() {
                    config.gap_tolerance = args[i + 1].parse().unwrap_or(1e-6);
                    i += 1;
                }
            }
            "--quiet" | "-q" => {
                config.verbose = false;
            }
            _ => {}
        }
        i += 1;
    }

    config
}

fn print_usage(program: &str) {
    eprintln!("scip-jack: Steiner Tree Problem Solver");
    eprintln!();
    eprintln!("Usage: {} <input.stp> [options]", program);
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --time-limit, -t <secs>  Time limit in seconds (default: 3600)");
    eprintln!("  --node-limit, -n <num>   Maximum B&B nodes (default: 1000000)");
    eprintln!("  --gap, -g <tol>          Optimality gap tolerance (default: 1e-6)");
    eprintln!("  --quiet, -q              Suppress progress output");
    eprintln!();
    eprintln!("Example:");
    eprintln!("  {} instance.stp --time-limit 60", program);
}
