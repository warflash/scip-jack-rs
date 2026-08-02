//! What the extended reduction deletes on the graphs the solver actually fails.
//!
//! §47's census is the reason this probe exists rather than a global A/B:
//! `root_reduce::tighten` deletes essentially nothing on the sixty refused Track
//! 2 instances — median edge ratio 1.000, mean 0.989 — so the question is not
//! whether the framework helps overall but whether it deletes anything *there*.
//! A rule that fires only where the pipeline already succeeds is worth nothing.
//!
//! ```text
//! extended_probe <instance> [seconds] [max-edges] [max-nodes]
//! ```
//!
//! emits
//!
//! ```text
//! <name>,<V>,<E>,<R>,<E after>,<deleted>,<candidates>,<trees>,<cor3>,<prop7>,<exhausted>,<dijkstras>,<secs>
//! ```
//!
//! where `V/E/R` are the graph *after* the classical reduction and the
//! tightening, at the same time shares `solver::solve` uses. That is the graph
//! the exact stage sees, and it is the only one whose size is worth reducing.

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::{Cost, UndirectedGraph};
use scip_jack::preprocessing::extended::{extended_reductions, ExtendedLimits};
use scip_jack::preprocessing::{preprocess_until, ReducibleGraph};
use scip_jack::root_reduce::{as_instance, tighten, ReduceConfig};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: extended_probe <instance> [seconds] [max-edges] [max-nodes]");
        return;
    }
    let limit: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5.0);
    let max_edges: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(4);
    let max_nodes: u64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(400);
    let budget: f64 = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(30.0);
    let name = std::path::Path::new(&args[1])
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();

    let start = Instant::now();
    let instance = scip_jack::io::read_instance(&args[1]).expect("read");
    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let reduce_deadline = start + Duration::from_secs_f64(limit / 3.0);
    let (rg, _) = preprocess_until(&instance, &graph, Some(reduce_deadline));
    let (ri, ru) = rg.to_instance();
    let cfg = ReduceConfig {
        deadline: Some(Instant::now() + Duration::from_secs_f64(limit * 2.0 / 3.0 * 0.35)),
        initial_upper_bound: Cost::INFINITY,
        ..ReduceConfig::default()
    };
    let reduced = tighten(ru, ri.terminals.clone(), &cfg);
    let g = reduced.graph;
    let terminals = reduced.terminals;

    let before_v = g.num_nodes;
    let before = g.edges.len();
    let before_r = terminals.len();
    let before_width = width_of(&g);

    // Interleave with the classical fixpoint. A deleted edge drops degrees, and
    // a degree that drops to one or two is what the classical rules are for; the
    // extended framework's own deletions are therefore worth re-offering to them.
    // Nothing here can move the optimum that the two parts do not already move:
    // both preserve `reduced optimum + offset`, and composing two such maps
    // composes their offsets.
    let mut cur_graph = g;
    let mut cur_terms = terminals;
    let mut offset = 0.0;
    let mut deleted = 0u32;
    let mut stats = scip_jack::preprocessing::extended::ExtendedStats::default();
    let t0 = Instant::now();
    let hard = Instant::now() + Duration::from_secs_f64(budget);
    for _ in 0..4 {
        let inst2 = as_instance(&cur_graph, &cur_terms);
        let mut work = ReducibleGraph::from_instance(&inst2, &cur_graph);
        let limits = ExtendedLimits { max_edges, max_nodes, ..ExtendedLimits::default() };
        let (d, st) = extended_reductions(&mut work, limits, Some(hard));
        deleted += d;
        stats.candidates += st.candidates;
        stats.trees_visited += st.trees_visited;
        stats.ruled_out_by_corollary3 += st.ruled_out_by_corollary3;
        stats.ruled_out_by_proposition7 += st.ruled_out_by_proposition7;
        stats.budget_exhausted += st.budget_exhausted;
        stats.dijkstras += st.dijkstras;
        if d == 0 {
            break;
        }
        let (i3, g3) = work.to_instance();
        offset += work.offset;
        let (rg3, _) = preprocess_until(&i3, &g3, Some(hard));
        offset += rg3.offset;
        let (i4, g4) = rg3.to_instance();
        cur_graph = g4;
        cur_terms = i4.terminals;
        if Instant::now() >= hard {
            break;
        }
    }
    let secs = t0.elapsed().as_secs_f64();
    let after = cur_graph.edges.len();
    let after_width = width_of(&cur_graph);

    println!(
        "{name},{before_v},{before},{before_r},{},{after},{},{deleted},{before_width},{after_width},{},{},{},{},{},{},{offset:.0},{secs:.2}",
        cur_graph.num_nodes,
        cur_terms.len(),
        stats.candidates,
        stats.trees_visited,
        stats.ruled_out_by_corollary3,
        stats.ruled_out_by_proposition7,
        stats.budget_exhausted,
        stats.dijkstras,
    );
}

/// The width the ordering portfolio finds, or `-1` when it refuses at 40.
fn width_of(g: &UndirectedGraph) -> i64 {
    use scip_jack::graph::algorithms::tree_decomposition::{decompose_portfolio, ORDERINGS};
    decompose_portfolio(g, 40, Some(Instant::now() + Duration::from_secs_f64(20.0)), &ORDERINGS)
        .map(|(t, _)| t.width as i64)
        .unwrap_or(-1)
}
