//! The sizing question item 0 asks: how big is the *raw* reachable table?
//!
//! The width ceiling of the tree-decomposition dynamic programme is not a
//! property of the recurrence. It is a property of two representations:
//!
//! - a signature packs a 4-bit block index per bag position into a `u64`, which
//!   caps a bag at 15 positions; and
//! - the rank-based reduction of §43 stores a `2^{|S|-1}`-bit cut vector per
//!   state, which at `|S| = 20` is 64 KiB *per state offered*.
//!
//! §34 measured the reduced tables at 15 to 39 states per class against a cut
//! space of dimension 128 at `s = 8` — an order of magnitude below the bound the
//! representation pays for. If the *raw* tables are that small too, then at the
//! widths the solver currently refuses the reduction is not merely unnecessary,
//! it is the thing forbidding the width; and the naive table, which is already
//! proved and is the differential baseline, is the affordable object.
//!
//! This probe answers that. It reproduces the solver's pipeline exactly as
//! `td_census` does — classical reduction, then `root_reduce::tighten` — then
//! decomposes at a width cap the packed encoding cannot reach, and runs
//! [`scip_jack::graph::algorithms::steiner_td::reference::raw_dp`], which has
//! neither representation: `Vec<u8>` signatures, no reduction, every reachable
//! state kept.
//!
//! ```text
//! table_census <instance> [seconds] [width-cap] [state-cap]
//! ```
//!
//! emits one `class` row per `(bag positions, |S|)` seen,
//!
//! ```text
//! class,<name>,<b>,<s>,<classes>,<total states>,<max class>,<2^(s-1)>
//! ```
//!
//! and one summary row
//!
//! ```text
//! summary,<name>,<V>,<E>,<R>,<width>,<nodes>,<joins>,<peak live>,<max class>,<secs>,<outcome>
//! ```
//!
//! The state cap and the deadline are guards, not results: a run that hits
//! either is reported `aborted` and its aggregates are a *lower* bound on the
//! full run's. That is the safe direction for the question — an aborted run
//! whose classes are all small is weak evidence, an aborted run with a large
//! class is conclusive.

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::steiner_td::reference::{dp, RawCensus};
use scip_jack::graph::algorithms::tree_decomposition::{decompose_portfolio, ORDERINGS};
use scip_jack::graph::{Cost, UndirectedGraph};
use scip_jack::preprocessing::preprocess_until;
use scip_jack::root_reduce::{tighten, ReduceConfig};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: table_census <instance> [seconds] [width-cap] [state-cap]");
        return;
    }
    let limit: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(60.0);
    let width_cap: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(21);
    let state_cap: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(20_000_000);
    // Bytes one class's rank-reduction basis may hold; `0` runs the recurrence
    // raw. The reduction is exact either way, so this changes what is measured
    // and never what is computed.
    let basis_budget: u64 = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);
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

    // The same shares `td_census` uses, so the graph measured here is the graph
    // the solver's exact stage would have seen at a five-second budget. The
    // *census* budget is separate and generous: the question is how big the
    // table gets, not whether it fits in five seconds.
    let solver_limit = 5.0;
    let reduce_deadline = start + Duration::from_secs_f64(solver_limit / 3.0);
    let (rg, _) = preprocess_until(&instance, &graph, Some(reduce_deadline));
    let (ri, ru) = rg.to_instance();
    let cfg = ReduceConfig {
        deadline: Some(Instant::now() + Duration::from_secs_f64(solver_limit * 2.0 / 3.0 * 0.35)),
        initial_upper_bound: Cost::INFINITY,
        ..ReduceConfig::default()
    };
    let reduced = tighten(ru, ri.terminals.clone(), &cfg);
    let g = reduced.graph;
    let terminals = reduced.terminals;

    let head = format!("{name},{},{},{}", g.num_nodes, g.edges.len(), terminals.len());

    let order_deadline = Instant::now() + Duration::from_secs_f64(60.0);
    let Some((td, _)) = decompose_portfolio(&g, width_cap, Some(order_deadline), &ORDERINGS) else {
        println!("summary,{head},>{width_cap},,,,,0.00,too-wide");
        return;
    };

    let mut census = RawCensus::default();
    let t0 = Instant::now();
    let deadline = t0 + Duration::from_secs_f64(limit);
    let out = dp(
        &g,
        &terminals,
        &td,
        state_cap,
        Some(deadline),
        (basis_budget > 0).then_some(basis_budget),
        &mut census,
    );
    let secs = t0.elapsed().as_secs_f64();

    for (&(b, s), &(classes, total, mx)) in &census.by_class {
        let bound = if s == 0 { 1.0 } else { (1u64 << (s - 1).min(62)) as f64 };
        println!("class,{name},{b},{s},{classes},{total},{mx},{bound:.0}");
    }
    for (&(b, s), &(classes, total, mx)) in &census.reduced_by_class {
        let bound = if s == 0 { 1.0 } else { (1u64 << (s - 1).min(62)) as f64 };
        println!("red,{name},{b},{s},{classes},{total},{mx},{bound:.0}");
    }
    let worst = census.worst().map(|w| w.2).unwrap_or(0);
    let outcome = match out {
        Some(c) => format!("solved:{c:.0}"),
        None if census.aborted => "aborted".to_string(),
        None => "infeasible".to_string(),
    };
    println!(
        "summary,{head},{},{},{},{},{worst},{secs:.2},{outcome},{},{},{}",
        td.width,
        census.nodes,
        census.joins,
        census.peak_live,
        census.basis_bytes,
        census.basis_at_s,
        census.reduction_refused
    );
}
