//! The root relaxation's *primal* point, turned into a tree.
//!
//! # The hole this is aimed at
//!
//! §85 measured `LP*` on every unproved instance with more than 64 terminals:
//! it equals `OPT` exactly on 16 of 64 and sits within 0.01 % on 39. §86 then
//! measured the other side and found that the incumbent at five seconds equals
//! the optimum on **six of sixty-three**. So on the biggest remaining block of
//! this benchmark the dual is solved and the primal is not, and every use this
//! solver has ever made of the root LP has read its dual.
//!
//! Where `LP* = OPT`, the optimal face of the relaxation contains an integral
//! point. `x*` is then not a bound but a *description of where an optimal tree
//! is*, and the question this probe answers is whether a tree can be read back
//! out of it.
//!
//! # Three readings, all of them costed with the true costs
//!
//! Nothing here trusts `x*`. It is a search metric and a candidate support, and
//! every tree produced is costed from the true arc costs, pruned, and improved by
//! key-path exchange exactly like any other incumbent.
//!
//! 1. **Support.** Keep the arcs with `x*_a >= theta`, over a ladder of
//!    thresholds; if the kept subgraph connects the terminals, take its minimum
//!    spanning tree and prune. This is the reading that should win outright when
//!    `x*` is integral.
//! 2. **Metric.** Drive the shortest-path heuristic with `w_a = c_a (1 - x*_a)`,
//!    so an arc the relaxation is certain of is free and one it rejects costs
//!    full price. This degrades gracefully when `x*` is fractional, which the
//!    support reading does not.
//! 3. **Control.** The same heuristic under the true costs and under the best
//!    dual ascent's reduced costs — which is what ships — so the comparison is
//!    against the solver's own primal and not against nothing.
//!
//! ```text
//! lpprimal_probe <instance> [optimum] [lp seconds] [starts]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{ArcId, Cost, DirectedGraph, NodeId, UndirectedGraph};
use scip_jack::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use scip_jack::heuristics::sph::{shortest_path_heuristic, SphResult, SphWorkspace};
use scip_jack::model::RootSeparation;
use scip_jack::preprocessing::preprocess_until;

/// Minimum spanning tree of the subgraph on `keep`, restricted to the component
/// of `root`, then pruned of non-terminal leaves. Returns its true cost, or
/// `None` when the kept arcs do not connect every terminal.
fn tree_from_support(
    idx: &ArcIndex,
    keep: &[bool],
    terminals: &[NodeId],
    is_terminal: &[bool],
    root: NodeId,
) -> Option<Cost> {
    let n = idx.num_nodes();
    // Prim over the undirected graph induced by the kept arcs.
    let mut in_tree = vec![false; n];
    let mut best_cost = vec![Cost::INFINITY; n];
    let mut best_arc = vec![u32::MAX; n];
    let mut heap = std::collections::BinaryHeap::new();
    best_cost[root as usize] = 0.0;
    heap.push(std::cmp::Reverse((0u64, root)));
    let mut chosen: Vec<ArcId> = Vec::new();
    while let Some(std::cmp::Reverse((_, v))) = heap.pop() {
        if in_tree[v as usize] {
            continue;
        }
        in_tree[v as usize] = true;
        if best_arc[v as usize] != u32::MAX {
            chosen.push(best_arc[v as usize]);
        }
        for &a in idx.outgoing(v) {
            if !keep[a as usize] {
                continue;
            }
            let u = idx.head(a) as usize;
            let c = idx.cost(a);
            if !in_tree[u] && c < best_cost[u] {
                best_cost[u] = c;
                best_arc[u] = a;
                heap.push(std::cmp::Reverse((c.to_bits(), u as NodeId)));
            }
        }
    }
    if terminals.iter().any(|&t| !in_tree[t as usize]) {
        return None;
    }
    // Prune non-terminal leaves until none is left.
    let mut deg = vec![0u32; n];
    let mut alive = vec![true; chosen.len()];
    for &a in &chosen {
        deg[idx.tail(a) as usize] += 1;
        deg[idx.head(a) as usize] += 1;
    }
    loop {
        let mut cut = false;
        for (i, &a) in chosen.iter().enumerate() {
            if !alive[i] {
                continue;
            }
            for v in [idx.tail(a), idx.head(a)] {
                if deg[v as usize] == 1 && !is_terminal[v as usize] {
                    alive[i] = false;
                    deg[idx.tail(a) as usize] -= 1;
                    deg[idx.head(a) as usize] -= 1;
                    cut = true;
                    break;
                }
            }
        }
        if !cut {
            break;
        }
    }
    Some(chosen.iter().enumerate().filter(|&(i, _)| alive[i]).map(|(_, &a)| idx.cost(a)).sum())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: lpprimal_probe <instance> [optimum] [lp seconds] [starts]");
        return;
    }
    let opt: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(f64::NAN);
    let lp_secs: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(3.0);
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
    let m = idx.num_arcs();
    let mut is_terminal = vec![false; idx.num_nodes()];
    for &t in &terminals {
        is_terminal[t as usize] = true;
    }
    let true_costs: Vec<Cost> = (0..m).map(|a| idx.cost(a as ArcId)).collect();

    let mut ascent = Cost::NEG_INFINITY;
    let mut best_root = terminals[0];
    let mut asc_reduced = true_costs.clone();
    for &r in &terminals {
        let da = dual_ascent_masked(&idx, r, &terminals, &active);
        if da.lower_bound > ascent {
            ascent = da.lower_bound;
            best_root = r;
            asc_reduced = da.reduced_costs.clone();
        }
    }
    let root = terminals[0];
    let starts: Vec<NodeId> = terminals.iter().copied().take(nstarts).collect();
    let mut ws = SphWorkspace::new(idx.num_nodes());
    let mut kws = KeyPathWorkspace::new(idx.num_nodes());

    let mut run = |weights: &[Cost], from: NodeId, ws: &mut SphWorkspace, kws: &mut KeyPathWorkspace| -> Cost {
        let mut best = Cost::INFINITY;
        for &s in &starts {
            if let Some(r) =
                shortest_path_heuristic(&idx, &active, weights, from, s, &terminals, &is_terminal, ws)
            {
                let r: SphResult =
                    key_path_exchange(&idx, &active, from, &r, &is_terminal, 8, kws, ws)
                        .unwrap_or(r);
                best = best.min(r.cost);
            }
        }
        best
    };

    let t0 = Instant::now();
    let plain = run(&true_costs, best_root, &mut ws, &mut kws);
    let guided = run(&asc_reduced, best_root, &mut ws, &mut kws);
    let t_control = t0.elapsed().as_secs_f64();

    // The root LP.
    let t1 = Instant::now();
    let mut sep = RootSeparation::new(&directed, root, &terminals);
    let deadline = Instant::now() + Duration::from_secs_f64(lp_secs);
    let cert = sep.advance(guided.min(plain), deadline, 1_000_000, 1 << 22);
    let lp_bound = cert.as_ref().map_or(Cost::NEG_INFINITY, |c| c.lp_bound);
    let x = sep.primal_solution().to_vec();
    let t_lp = t1.elapsed().as_secs_f64();
    let integral = x.iter().filter(|&&v| v > 1e-6 && v < 1.0 - 1e-6).count();
    let positive = x.iter().filter(|&&v| v > 1e-6).count();

    // 1. Support, over a ladder of thresholds.
    let t2 = Instant::now();
    let mut support = Cost::INFINITY;
    let mut support_theta = f64::NAN;
    for theta in [0.99, 0.9, 0.75, 0.5, 0.25, 0.1, 0.01] {
        // An undirected edge survives when either orientation does: the tree does
        // not know which way the arborescence will run it.
        let keep: Vec<bool> = (0..m)
            .map(|a| x.get(a).copied().unwrap_or(0.0).max(x.get(a ^ 1).copied().unwrap_or(0.0)) >= theta)
            .collect();
        if let Some(c) = tree_from_support(&idx, &keep, &terminals, &is_terminal, root) {
            if c < support {
                support = c;
                support_theta = theta;
            }
        }
    }

    // 2. Metric: an arc the relaxation is sure of is free.
    let lpw: Vec<Cost> = (0..m)
        .map(|a| {
            let v = x.get(a).copied().unwrap_or(0.0).max(x.get(a ^ 1).copied().unwrap_or(0.0));
            true_costs[a] * (1.0 - v.clamp(0.0, 1.0))
        })
        .collect();
    let metric = run(&lpw, best_root, &mut ws, &mut kws);
    let t_round = t2.elapsed().as_secs_f64();

    let shipped = plain.min(guided);
    let best = shipped.min(support).min(metric);
    let pct = |v: Cost| if opt.is_finite() && opt != 0.0 { 100.0 * ((v + offset) / opt - 1.0) } else { f64::NAN };
    eprintln!(
        "{name}: |V|={} |E|={} |R|={} opt={opt} | LP {:.1} in {t_lp:.2}s ({} frac of {} positive) | \
         shipped {:.1} (+{:.3}%) | support {:.1} (+{:.3}%, theta {support_theta}) | \
         metric {:.1} (+{:.3}%) | best {:.1} (+{:.3}%) [ctl {t_control:.2}s round {t_round:.2}s]",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        lp_bound + offset,
        integral,
        positive,
        shipped + offset,
        pct(shipped),
        support + offset,
        pct(support),
        metric + offset,
        pct(metric),
        best + offset,
        pct(best),
    );
    println!(
        "{name},{opt},{:.1},{:.1},{:.1},{:.1},{:.1},{:.4},{:.4},{:.4},{},{},{m},{:.3},{:.3},{:.3}",
        lp_bound + offset,
        shipped + offset,
        support + offset,
        metric + offset,
        best + offset,
        pct(shipped),
        pct(support),
        pct(best),
        integral,
        positive,
        t_control,
        t_lp,
        t_round,
    );
}
