//! Measures the three lower bounds available at the root of a reduced instance:
//! the dual ascent's, the cut relaxation's after a converged separation loop,
//! and the value of the packing certified out of that LP's dual.
//!
//! It exists because those three numbers answer different questions. The ascent
//! bound is what the search's potential is worth today; the LP bound is the
//! ceiling any packing read off that LP can reach; the packing value is how much
//! of that ceiling survives the feasibility repair. A gap between the second and
//! third is the price of the repair, and a gap between the LP bound and the
//! optimum is the relaxation's own, which no dual extraction can close.
//!
//! With a cutoff supplied it also reports how many arcs reduced-cost fixing can
//! eliminate against it, and runs the search at a fixed label budget under each
//! potential in turn — which is the only way to see that neither packing
//! dominates the other and that their pointwise maximum beats both.
//!
//! ```text
//! certify_probe <instance> [seconds] [upper bound]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{DirectedGraph, UndirectedGraph};
use scip_jack::model::root_certificate;
use scip_jack::preprocessing::preprocess_until;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: certify_probe <instance> [seconds] [upper bound]");
        return;
    }
    let budget: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(60.0);

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
    let offset = pr.lower_bound_offset;
    let terminals = ri.terminals.clone();
    println!(
        "reduced: |V|={} |E|={} |R|={} offset={:.1}",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        offset
    );
    if terminals.len() < 2 {
        return;
    }

    let directed = DirectedGraph::from_undirected(&ru);
    let idx = ArcIndex::new(&directed);
    let active = vec![true; idx.num_arcs()];
    let root = terminals[0];

    let t = Instant::now();
    let da = dual_ascent_masked(&idx, root, &terminals, &active);
    println!("ascent           {:10.2}   ({:.2}s)", da.lower_bound + offset, t.elapsed().as_secs_f64());

    let ub: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(f64::INFINITY);

    let t = Instant::now();
    let deadline = Instant::now() + Duration::from_secs_f64(budget);
    match root_certificate(&directed, root, &terminals, ub - offset, deadline, 100_000, 1 << 24) {
        Some(cert) => {
            println!(
                "root LP          {:10.2}   ({} solves, {:.2}s)",
                cert.lp_bound + offset,
                cert.lp_solves,
                t.elapsed().as_secs_f64()
            );
            println!(
                "certified packing{:10.2}   ({} sets, {:.1}% of the LP)",
                cert.packing.value + offset,
                cert.packing.sets.len(),
                100.0 * cert.packing.value / cert.lp_bound.max(1e-9)
            );
            println!(
                "eliminated arcs  {:10}   of {}",
                cert.eliminated_arcs.len(),
                idx.num_arcs()
            );
            // Round-by-round: what the separation loop actually costs and buys.
            // A loop that needs hundreds of solves is either separating too
            // little per round or re-solving a model that barely changed, and
            // these three columns say which.
            println!("  round      bound  struct   cuts    rows    secs");
            let last = cert.rounds.len().saturating_sub(1);
            for (i, r) in cert.rounds.iter().enumerate() {
                if i < 8 || i % 16 == 0 || i == last {
                    println!(
                        "  {:5}  {:9.2}  {:6}  {:5}  {:6}  {:6.3}",
                        i,
                        r.bound + offset,
                        r.structural,
                        r.cuts,
                        r.rows,
                        r.secs
                    );
                }
            }
            assert!(cert.packing.verify(&idx, root, 1e-6), "packing violates (PACK)");

            let ascent_pack = scip_jack::graph::algorithms::dual_ascent_packing(
                &idx,
                root,
                &terminals,
                &active,
                1 << 24,
            );
            for labels in [50_000u64, 400_000] {
                println!("search at {labels} labels, cutoff {ub}:");
                compare_search(
                    &ru,
                    &terminals,
                    ub,
                    &ascent_pack.sets,
                    &cert.packing.sets,
                    labels,
                );
            }
        }
        None => println!("root LP           unavailable"),
    }
}

/// Same label budget, three potentials: what the search's frontier bound reaches.
fn compare_search(
    graph: &UndirectedGraph,
    terminals: &[scip_jack::graph::NodeId],
    upper_bound: f64,
    ascent: &[(f64, Vec<scip_jack::graph::NodeId>)],
    lp: &[(f64, Vec<scip_jack::graph::NodeId>)],
    labels: u64,
) {
    use scip_jack::graph::algorithms::dijkstra_steiner_guided;
    let cases: [(&str, Vec<&[(f64, Vec<scip_jack::graph::NodeId>)]>); 3] = [
        ("ascent only", vec![ascent]),
        ("lp only", vec![lp]),
        ("max of both", vec![ascent, lp]),
    ];
    for (name, guides) in cases {
        let t = Instant::now();
        let r = dijkstra_steiner_guided(graph, terminals, upper_bound, labels, None, &guides);
        match r {
            Some(r) => println!(
                "  {name:<12} frontier {:10.2}  optimal {:?}  {} labels  {:.2}s",
                r.lower_bound,
                r.optimal,
                r.labels_settled,
                t.elapsed().as_secs_f64()
            ),
            None => println!("  {name:<12} unavailable"),
        }
    }
}
