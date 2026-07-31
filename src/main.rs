pub mod graph;
pub mod model;
pub mod preprocessing;
pub mod separation;
pub mod heuristics;
pub mod branch_and_bound;
pub mod transformations;
pub mod io;

use std::env;
use std::time::Instant;

use graph::{DirectedGraph, UndirectedGraph};
use graph::algorithms::dreyfus_wagner;
use preprocessing::preprocess;
use branch_and_bound::{BranchAndCutSolver, SolverConfig, SolveStatus};

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

    // Phase 1: Parse input
    let start = Instant::now();
    let instance = match io::read_instance(input_file) {
        Ok(inst) => inst,
        Err(e) => {
            eprintln!("Error reading instance '{}': {}", input_file, e);
            std::process::exit(1);
        }
    };
    let parse_time = start.elapsed().as_secs_f64();

    eprintln!("Instance: {}", instance);
    if let Some(root) = instance.root {
        eprintln!("Root: {}", root);
    }
    eprintln!("Parse time: {:.3}s", parse_time);
    eprintln!();

    // Phase 2: Build undirected graph
    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    // Phase 3: Preprocessing
    let preprocess_start = Instant::now();
    let (reduced_graph, preprocess_result) = preprocess(&instance, &graph);
    let preprocess_time = preprocess_start.elapsed().as_secs_f64();

    eprintln!("Preprocessing:");
    eprintln!("  Nodes removed: {}", preprocess_result.nodes_removed);
    eprintln!("  Edges removed: {}", preprocess_result.edges_removed);
    eprintln!("  Edges fixed: {}", preprocess_result.edges_fixed.len());
    eprintln!("  LB offset: {:.4}", preprocess_result.lower_bound_offset);
    eprintln!("  Time: {:.3}s", preprocess_time);
    eprintln!();

    // Phase 4: Build directed graph (SAP transformation)
    let (reduced_instance, reduced_undirected) = reduced_graph.to_instance();
    let directed = DirectedGraph::from_undirected(&reduced_undirected);

    let root = reduced_instance.root.unwrap_or_else(|| {
        // If no root specified, pick first terminal
        *reduced_instance.terminals.first().expect("No terminals in instance")
    });

    let terminals: Vec<u32> = reduced_instance.terminals.clone();

    eprintln!("Reduced instance: |V|={}, |E|={}, |T|={}",
        reduced_instance.num_nodes,
        reduced_instance.num_edges,
        reduced_instance.num_terminals,
    );
    eprintln!("Directed graph: {} nodes, {} arcs", directed.num_nodes, directed.num_arcs());
    eprintln!();

    // Phase 5: Solve
    // Use Dreyfus-Wagner DP for small-terminal instances (exact, faster than B&C)
    let dw_threshold = 15;
    if reduced_instance.num_terminals <= dw_threshold as u32 {
        eprintln!("Using Dreyfus-Wagner DP ({} terminals ≤ {} threshold)",
            reduced_instance.num_terminals, dw_threshold);
        eprintln!("--------------------------------------------------");

        let dw_start = Instant::now();
        if let Some(dw_result) = dreyfus_wagner(&reduced_undirected, &reduced_instance.terminals) {
            let dw_time = dw_start.elapsed().as_secs_f64();
            let total_obj = dw_result.optimal_cost + preprocess_result.lower_bound_offset;

            eprintln!("--------------------------------------------------");
            eprintln!();
            eprintln!("Results (Dreyfus-Wagner DP):");
            eprintln!("  Status: Optimal (exact DP)");
            eprintln!("  Optimal cost: {:.6}", total_obj);
            eprintln!("  Tree edges: {}", dw_result.tree_edges.len());
            eprintln!("  Time: {:.3}s", dw_time);
            eprintln!("  OPTIMAL (proven by DP)");

            println!("{:.6}", total_obj);
            return;
        }
        eprintln!("DW infeasible, falling back to branch-and-cut");
    }

    eprintln!("Using Branch-and-Cut solver");
    eprintln!("--------------------------------------------------");

    let mut solver = BranchAndCutSolver::new(directed, root, terminals);
    solver.config = config;

    let (solution, stats) = solver.solve();

    eprintln!("--------------------------------------------------");
    eprintln!();

    let total_obj = stats.primal_bound + preprocess_result.lower_bound_offset;

    eprintln!("Results:");
    eprintln!("  Status: {:?}", stats.status);
    eprintln!("  Primal bound: {:.6}", total_obj);
    eprintln!("  Dual bound: {:.6}", stats.dual_bound + preprocess_result.lower_bound_offset);
    eprintln!("  Gap: {:.4}%", stats.gap * 100.0);
    eprintln!("  Nodes processed: {}", stats.nodes_processed);
    eprintln!("  Time: {:.3}s", stats.time_secs);
    eprintln!();

    if let Some(sol) = &solution {
        eprintln!("Solution:");
        eprintln!("  Arcs: {}", sol.arcs.len());
        eprintln!("  Nodes: {}", sol.nodes.len());
        eprintln!("  Objective: {:.6}", sol.objective_value + preprocess_result.lower_bound_offset);
        if stats.status == SolveStatus::Optimal {
            eprintln!("  OPTIMAL (proven)");
        }
    } else {
        eprintln!("No feasible solution found.");
    }

    if let Some(sol) = &solution {
        println!("{:.6}", sol.objective_value + preprocess_result.lower_bound_offset);
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
