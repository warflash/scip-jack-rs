//! Width census of the graph the solver *actually* hands to its exact stage.
//!
//! [`tw_probe`] decomposes the output of the classical reduction. That is not
//! the graph `try_decomposition` sees: between the two sits `root_reduce::tighten`,
//! whose reduced-cost eliminations routinely halve the edge count, and the width
//! of a graph is not monotone under anything but vertex deletion. So a census
//! meant to answer "would a faster join have closed this instance?" has to
//! reproduce the pipeline, not approximate it.
//!
//! ```text
//! td_census <instance> [seconds]
//! ```
//!
//! emits one CSV row:
//!
//! ```text
//! name,red_V,red_E,red_R,tight_V,tight_E,tight_R,width,work,dp_secs,outcome
//! ```
//!
//! where `outcome` is one of
//!
//! - `refused` — no ordering in the portfolio kept every bag at or below the
//!   encoding's cap, so the DP is never entered. A faster join buys nothing.
//! - `timeout` — the graph decomposed and the DP ran out of clock. A faster join
//!   buys exactly its factor here.
//! - `capped` — the DP hit its state budget, which is a memory guard.
//! - `solved:<value>` — the DP finished. (Then the solver's failure, if any, was
//!   a scheduling matter and not the DP's.)
//!
//! The time shares mirror `solver::solve`: a third of the limit to the classical
//! reduction, then 35 % of what is left to the tightening, then the rest to the
//! decomposition and the DP. That over-states the DP's share slightly — the real
//! pass gives the goal-directed search half of the remainder first — and
//! over-stating it is the safe direction for this question: an instance that
//! times out under a *generous* budget certainly times out under the real one.

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::steiner_td::{
    steiner_tree_over_decomposition, work_estimate, MAX_BAG,
};
use scip_jack::graph::algorithms::tree_decomposition::{decompose_portfolio, ORDERINGS};
use scip_jack::graph::{Cost, UndirectedGraph};
use scip_jack::preprocessing::preprocess_until;
use scip_jack::root_reduce::{tighten, ReduceConfig};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: td_census <instance> [seconds]");
        return;
    }
    let limit: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5.0);
    let name = std::path::Path::new(&args[1])
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();

    let start = Instant::now();
    let deadline = start + Duration::from_secs_f64(limit);
    let instance = scip_jack::io::read_instance(&args[1]).expect("read");
    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let reduce_deadline = start + Duration::from_secs_f64((limit / 3.0).max(0.05));
    let (rg, _) = preprocess_until(&instance, &graph, Some(reduce_deadline));
    let (ri, ru) = rg.to_instance();

    let remaining = deadline.saturating_duration_since(Instant::now());
    let cfg = ReduceConfig {
        deadline: Some(Instant::now() + remaining.mul_f64(0.35)),
        initial_upper_bound: Cost::INFINITY,
        ..ReduceConfig::default()
    };
    let reduced = tighten(ru, ri.terminals.clone(), &cfg);
    let g = reduced.graph;
    let terminals = reduced.terminals;

    let mut row = format!(
        "{name},{},{},{},{},{},{}",
        ri.num_nodes,
        ri.num_edges,
        ri.terminals.len(),
        g.num_nodes,
        g.edges.len(),
        terminals.len(),
    );

    // The decomposition gets its own budget, separate from the DP's.
    //
    // The first version of this probe handed `decompose_portfolio` the overall
    // deadline, which by then the reduction had usually consumed — so an
    // ordering that never ran was recorded as "the graph is too wide". On PACE
    // Track 2's instance052 that mislabelled a graph of width **8** as refused
    // at a cap of 13, and instance089 (width 10) with it. Refusal has to mean
    // refusal.
    let cap = MAX_BAG - 2;
    let order_deadline = Instant::now() + Duration::from_secs_f64(30.0);
    let td = decompose_portfolio(&g, cap, Some(order_deadline), &ORDERINGS).map(|(t, _)| t);
    match td {
        None => {
            // What the width actually is, so "refused" can be read as a number
            // rather than as an inequality.
            let wide = decompose_portfolio(
                &g,
                64,
                Some(Instant::now() + Duration::from_secs_f64(30.0)),
                &ORDERINGS,
            )
            .map(|(t, _)| t.width);
            match wide {
                Some(w) => println!("{row},{w},,,refused"),
                None => println!("{row},>64,,,refused"),
            }
        }
        Some(td) => {
            let work = work_estimate(&td, g.edges.len(), 1);
            row.push_str(&format!(",{},{:.2e}", td.width, work));
            let t0 = Instant::now();
            let out = steiner_tree_over_decomposition(
                &g,
                &terminals,
                &td,
                40_000_000,
                false,
                Some(deadline),
            );
            let secs = t0.elapsed().as_secs_f64();
            match out {
                Some((cost, _)) => println!("{row},{secs:.2},solved:{cost:.0}"),
                None if Instant::now() >= deadline => println!("{row},{secs:.2},timeout"),
                None => println!("{row},{secs:.2},capped"),
            }
        }
    }
}
