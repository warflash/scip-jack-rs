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

    // The hypergraphic certificate, when the subset table is affordable. It is a
    // different relaxation, not a strengthening of the one below, so the two are
    // reported side by side rather than combined.
    if scip_jack::model::hyp_is_affordable(terminals.len(), ru.num_nodes, ru.edges.len()) {
        let t = Instant::now();
        match scip_jack::model::hyp_certificate(&ru, &terminals, Some(Instant::now() + Duration::from_secs_f64(budget))) {
            Some(h) => println!(
                "hypergraphic     {:10.2}   ({} partitions, repair {:.6}, {:.2}s)",
                h.lower_bound + offset,
                h.partitions.len(),
                h.repair_ratio,
                t.elapsed().as_secs_f64()
            ),
            None => println!("hypergraphic      unavailable"),
        }
    } else {
        println!("hypergraphic      out of range ({} terminals, {} nodes)", terminals.len(), ru.num_nodes);
    }

    // The grouped hypergraphic dual, at every clustering size the oracle can
    // afford. Unlike the enumerating certificate this has no terminal ceiling:
    // the exponent is the number of classes, which is chosen, not given.
    for h in [4usize, 6, 8, 10, 12] {
        let work = scip_jack::model::group_steiner_work(h, ru.num_nodes, ru.edges.len());
        if work > 3e9 {
            println!("grouped h={h:<3}      out of range ({work:.1e} units)");
            continue;
        }
        let t = Instant::now();
        match scip_jack::model::grouped_hyp_dual(
            &ru,
            &terminals,
            h,
            Some(Instant::now() + Duration::from_secs_f64(budget)),
        ) {
            Some(d) => println!(
                "grouped h={h:<3} {:10.2}   ({} classes, {} partitions, repair {:.4}, {:.2}s)",
                d.lower_bound + offset,
                d.groups.len(),
                d.partitions.len(),
                d.repair_ratio,
                t.elapsed().as_secs_f64()
            ),
            None => println!("grouped h={h:<3}  unavailable"),
        }
    }

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
            println!("  round      bound  struct   cuts    rows    secs |  cyc(s)   part(s)     tf(s)");
            let last = cert.rounds.len().saturating_sub(1);
            for (i, r) in cert.rounds.iter().enumerate() {
                if i < 8 || i % 16 == 0 || i == last {
                    println!(
                        "  {:5}  {:9.2}  {:6}  {:5}  {:6}  {:6.3} | {:3}({:.3}) {:3}({:.3}) {:3}({:.3})",
                        i,
                        r.bound + offset,
                        r.structural,
                        r.cuts,
                        r.rows,
                        r.secs,
                        r.family[0].0, r.family[0].1,
                        r.family[1].0, r.family[1].1,
                        r.family[2].0, r.family[2].1,
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
            // Ascent from every terminal in turn. A packing rooted at `r'`
            // consists of sets missing `r'`, which may contain the search's own
            // root; dropping those leaves a feasible packing (removing sets only
            // lowers every arc's load), so each is a legal extra layer of the
            // pointwise maximum.
            let t = Instant::now();
            let mut multi: Vec<Vec<(f64, Vec<scip_jack::graph::NodeId>)>> = Vec::new();
            for &r in terminals.iter() {
                let p = scip_jack::graph::algorithms::dual_ascent_packing(
                    &idx, r, &terminals, &active, 1 << 22,
                );
                let kept: Vec<(f64, Vec<scip_jack::graph::NodeId>)> =
                    p.sets.into_iter().filter(|(_, s)| !s.contains(&root)).collect();
                if !kept.is_empty() {
                    multi.push(kept);
                }
            }
            // `MAX_PACKING_LAYERS` is 2, so handing the search a list of 26
            // packings tests only its first two. Rank them by value and keep the
            // best, which is the question that can actually be asked.
            multi.sort_by(|a, b| {
                let (x, y): (f64, f64) = (a.iter().map(|s| s.0).sum(), b.iter().map(|s| s.0).sum());
                y.total_cmp(&x)
            });
            println!(
                "multi-root ascent: {} usable packings of {} terminals, values {:.1} .. {:.1} ({:.2}s)",
                multi.len(),
                terminals.len(),
                multi.first().map_or(0.0, |p| p.iter().map(|s| s.0).sum::<f64>()) + offset,
                multi.last().map_or(0.0, |p| p.iter().map(|s| s.0).sum::<f64>()) + offset,
                t.elapsed().as_secs_f64()
            );
            multi.truncate(1);

            // How much of the separation loop the *potential* actually needs.
            // The converged LP is what closes these instances, and it is also
            // what costs twenty seconds; the question is whether a truncated
            // loop's packing is already strong enough to guide the search home.
            for secs in [0.25f64, 0.5, 1.0, 2.0, 4.0] {
                let t = Instant::now();
                let Some(c) = root_certificate(
                    &directed,
                    root,
                    &terminals,
                    ub - offset,
                    Instant::now() + Duration::from_secs_f64(secs),
                    100_000,
                    1 << 24,
                ) else {
                    println!("  budget {secs:>4}s   unavailable");
                    continue;
                };
                let built = t.elapsed().as_secs_f64();
                let t2 = Instant::now();
                let r = scip_jack::graph::algorithms::dijkstra_steiner_guided(
                    &ru,
                    &terminals,
                    ub,
                    400_000,
                    None,
                    &[&c.packing.sets],
                );
                println!(
                    "  budget {secs:>4}s  {} solves  packing {:10.2}  build {:.2}s  -> {}  ({} labels, {:.2}s)",
                    c.lp_solves,
                    c.packing.value + offset,
                    built,
                    r.as_ref()
                        .and_then(|r| r.optimal)
                        .map_or_else(|| "no".to_string(), |v| format!("OPTIMAL {v:.0}")),
                    r.as_ref().map_or(0, |r| r.labels_settled),
                    t2.elapsed().as_secs_f64()
                );
            }
            for labels in [50_000u64, 400_000] {
                println!("search at {labels} labels, cutoff {ub}:");
                compare_search(
                    &ru,
                    &terminals,
                    ub,
                    &ascent_pack.sets,
                    &cert.packing.sets,
                    &multi,
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
    multi: &[Vec<(f64, Vec<scip_jack::graph::NodeId>)>],
    labels: u64,
) {
    use scip_jack::graph::algorithms::dijkstra_steiner_guided;
    let multi_refs: Vec<&[(f64, Vec<scip_jack::graph::NodeId>)]> =
        multi.iter().map(|v| v.as_slice()).collect();
    let mut multi_lp = multi_refs.clone();
    multi_lp.push(lp);
    let cases: Vec<(&str, Vec<&[(f64, Vec<scip_jack::graph::NodeId>)]>)> = vec![
        ("ascent only", vec![ascent]),
        ("lp only", vec![lp]),
        ("max of both", vec![ascent, lp]),
        ("multi-root", multi_refs),
        ("multi + lp", multi_lp),
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
