//! Does the tightening preserve the optimum under a *loose* cutoff?
//!
//! Every bound-based rule in `root_reduce::round` preserves the trees strictly
//! cheaper than the incumbent it is handed, not the optimum outright. When the
//! incumbent *is* the optimum that distinction never shows; when it is a few
//! units above, it is the whole question. This probe reproduces the scenario on
//! a real instance: run the classical reduction, then the tightening under a
//! cutoff supplied on the command line, then solve the result exactly and
//! compare against the reference.
//!
//! ```text
//! cutoff_probe <instance> <cutoff-on-the-reduced-scale> [seconds]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::dijkstra_steiner;
use scip_jack::graph::{Cost, UndirectedGraph};
use scip_jack::preprocessing::preprocess_until;
use scip_jack::root_reduce::{tighten, ReduceConfig};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: cutoff_probe <instance> <cutoff> [seconds]");
        return;
    }
    let cutoff: Cost = args[2].parse().expect("cutoff");
    let secs: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(120.0);
    // A deadline on the *tightening*, so a truncated fixpoint can be reproduced
    // as well as a converged one.
    let reduce_secs: f64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(f64::INFINITY);

    let instance = scip_jack::io::read_instance(&args[1]).expect("read");
    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    let (rg, pr) = preprocess_until(&instance, &graph, None);
    let (ri, ru) = rg.to_instance();
    let base = pr.lower_bound_offset;
    println!(
        "classical: V={} E={} R={} offset={base}",
        ri.num_nodes,
        ri.num_edges,
        ri.terminals.len()
    );

    // The optimum of the classically reduced instance, for reference.
    let t0 = Instant::now();
    let before = dijkstra_steiner(
        &ru,
        &ri.terminals,
        Cost::INFINITY,
        u64::MAX,
        Some(Instant::now() + Duration::from_secs_f64(secs)),
    );
    println!(
        "classical optimum: {:?} (+{base}) in {:.1}s",
        before.as_ref().and_then(|r| r.optimal),
        t0.elapsed().as_secs_f64()
    );

    let cfg = ReduceConfig {
        initial_upper_bound: cutoff,
        deadline: reduce_secs
            .is_finite()
            .then(|| Instant::now() + Duration::from_secs_f64(reduce_secs)),
        ..ReduceConfig::default()
    };
    let out = tighten(ru, ri.terminals, &cfg);
    println!(
        "tightened under cutoff {cutoff}: V={} E={} R={} LB={} UB={} offset={} rounds={}",
        out.graph.num_nodes,
        out.graph.edges.len(),
        out.terminals.len(),
        out.lower_bound,
        out.upper_bound,
        out.offset,
        out.rounds,
    );

    let t0 = Instant::now();
    let after = dijkstra_steiner(
        &out.graph,
        &out.terminals,
        Cost::INFINITY,
        u64::MAX,
        Some(Instant::now() + Duration::from_secs_f64(secs)),
    );
    let value = after.as_ref().and_then(|r| r.optimal);
    println!(
        "reduced optimum: {:?} + offset {} in {:.1}s",
        value,
        out.offset,
        t0.elapsed().as_secs_f64()
    );
    if let (Some(b), Some(a)) = (before.and_then(|r| r.optimal), value) {
        let restated = a + out.offset;
        println!(
            "INVARIANT {}: reduced {a} + offset {} = {restated} against classical optimum {b}",
            if (restated - b).abs() < 1e-6 { "HOLDS" } else { "*** VIOLATED ***" },
            out.offset
        );
    }
}
