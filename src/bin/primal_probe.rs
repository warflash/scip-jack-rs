//! Which dual guides the primal best?
//!
//! §86 of the fourteenth round measured the thing that decides the wide half of
//! this benchmark: over the 63 unproved Track 2 instances with more than 64
//! terminals, the incumbent at five seconds equals the optimum on **six**. The
//! relaxation is at or beside the optimum on almost all of them (§85), so what is
//! missing is a tree and not a bound.
//!
//! The shortest-path heuristic is already driven by a *metric* supplied
//! separately from the true costs, and `root_reduce` drives it with each dual
//! ascent's reduced costs. Nothing has ever driven it with a **stronger** dual's,
//! and the reason to expect that to matter is item 2's corollary: if `L = OPT`
//! then every optimal tree lies in the zero-price subgraph, so the price vector
//! of a stronger dual is a sharper statement about where the optimum is.
//!
//! This probe runs the same heuristic, from the same starts, under three metrics
//! and reports the best tree each finds:
//!
//! 1. the true costs;
//! 2. the dual ascent's reduced costs, which is what ships;
//! 3. the flow dual's, after a measured budget of ascent.
//!
//! ```text
//! primal_probe <instance> [optimum] [flow-dual seconds] [starts]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{ArcId, Cost, DirectedGraph, NodeId, UndirectedGraph};
use scip_jack::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use scip_jack::heuristics::sph::{shortest_path_heuristic, SphResult, SphWorkspace};
use scip_jack::model::{FlowDual, FlowDualOptions};
use scip_jack::preprocessing::preprocess_until;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: primal_probe <instance> [optimum] [flow-dual seconds] [starts]");
        return;
    }
    let opt: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(f64::NAN);
    let fd_secs: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1.0);
    let nstarts: usize = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(8);
    let name = std::path::Path::new(&args[1])
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();

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
    if terminals.len() < 2 {
        println!("{name},closed,,,,,,,,");
        return;
    }
    let directed = DirectedGraph::from_undirected(&ru);
    let idx = ArcIndex::new(&directed);
    let active = vec![true; idx.num_arcs()];
    let mut is_terminal = vec![false; idx.num_nodes()];
    for &t in &terminals {
        is_terminal[t as usize] = true;
    }
    let true_costs: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();

    // The best ascent, and the root it came from.
    let mut ascent = Cost::NEG_INFINITY;
    let mut best_root = terminals[0];
    let mut asc_reduced: Vec<Cost> = true_costs.clone();
    for &r in &terminals {
        let da = dual_ascent_masked(&idx, r, &terminals, &active);
        if da.lower_bound > ascent {
            ascent = da.lower_bound;
            best_root = r;
            asc_reduced = da.reduced_costs.clone();
        }
    }

    let starts: Vec<NodeId> = terminals.iter().copied().take(nstarts).collect();
    let mut ws = SphWorkspace::new(idx.num_nodes());
    let mut kws = KeyPathWorkspace::new(idx.num_nodes());

    let mut run = |weights: &[Cost], root: NodeId| -> (Cost, f64) {
        let t0 = Instant::now();
        let mut best = Cost::INFINITY;
        for &s in &starts {
            if let Some(r) =
                shortest_path_heuristic(&idx, &active, weights, root, s, &terminals, &is_terminal, &mut ws)
            {
                let r: SphResult =
                    key_path_exchange(&idx, &active, root, &r, &is_terminal, 8, &mut kws, &mut ws)
                        .unwrap_or(r);
                best = best.min(r.cost);
            }
        }
        (best, t0.elapsed().as_secs_f64())
    };

    let (plain, t_plain) = run(&true_costs, best_root);
    let (guided, t_guided) = run(&asc_reduced, best_root);

    // The flow dual, at the same root, with the ascent-guided tree as its target.
    let t0 = Instant::now();
    let opts = FlowDualOptions { entry_budget: 24_000_000, ..FlowDualOptions::default() };
    let (fd_primal, fd_bound, fd_zero) = match FlowDual::new(&idx, best_root, &terminals, opts) {
        Ok(mut fd) => {
            fd.set_target(Some(guided.min(plain)));
            fd.ascend(
                &idx,
                Cost::INFINITY,
                Instant::now() + Duration::from_secs_f64(fd_secs),
                u64::MAX,
                8,
            );
            let l = fd.finish(&idx);
            let (_, d) = fd.pricing();
            let zero = d.iter().filter(|&&x| x <= 1e-9).count();
            let (p, _) = run(&d, best_root);
            (p, l, zero)
        }
        Err(_) => (Cost::INFINITY, Cost::NEG_INFINITY, 0),
    };
    let fd_total = t0.elapsed().as_secs_f64();
    let asc_zero = asc_reduced.iter().filter(|&&x| x <= 1e-9).count();

    let m = idx.num_arcs();
    let best = plain.min(guided).min(fd_primal);
    eprintln!(
        "{name}: |V|={} |E|={} |R|={} opt={opt} | sph(true) {:.1} in {t_plain:.2}s | \
         sph(ascent {:.1}, {}/{m} free) {:.1} in {t_guided:.2}s | \
         sph(flowdual {:.1}, {fd_zero}/{m} free) {:.1} in {fd_total:.2}s | best {:.1}",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        plain + offset,
        ascent + offset,
        asc_zero,
        guided + offset,
        fd_bound + offset,
        fd_primal + offset,
        best + offset,
    );
    println!(
        "{name},{opt},{:.1},{:.1},{:.1},{:.1},{},{},{m},{:.3},{:.3},{:.3}",
        plain + offset,
        guided + offset,
        fd_primal + offset,
        fd_bound + offset,
        asc_zero,
        fd_zero,
        t_plain,
        t_guided,
        fd_total,
    );
}
