//! What the classical fixpoint deletes once it is told what the arcs are worth.
//!
//! Item 2 of the fourteenth round asks for the *positive* use of the certified
//! dual: not "which arcs can be deleted because their price exceeds the gap"
//! (§80 measured that as inert), but the change of costs itself. Under
//! [`scip_jack::model::flow_dual::FlowDual::pricing`],
//!
//! ```text
//! c(A) >= L + sum_{a in A} d_a       for every arborescence A,
//! ```
//!
//! so a tree of `c`-cost at most `UB` has `d`-cost at most `UB - L`. The residual
//! budget is the whole difficulty and the price vector is where it lives, so the
//! two questions this probe answers are:
//!
//! 1. **what the `d`-graph looks like** — how much of it is free, how large its
//!    zero-price components are, and what the residual budget actually is;
//! 2. **what the reduction does with it** — `tighten` run twice on the same
//!    graph, once as it stands and once handed `(L, d)` as
//!    `ReduceConfig::initial_lower_bound` and `initial_dual`, reporting what each
//!    deletes.
//!
//! The second is the comparison §80 could not make, because there the dual came
//! from an LP that had not converged; here it comes from an ascent run to its own
//! stopping rule.
//!
//! ```text
//! dgraph_probe <instance> [optimum] [dual seconds]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{ArcId, Cost, DirectedGraph, UndirectedGraph};
use scip_jack::model::{ArcDual, FlowDual, FlowDualOptions};
use scip_jack::preprocessing::preprocess_until;
use scip_jack::root_reduce::{tighten, ReduceConfig};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: dgraph_probe <instance> [optimum] [dual seconds]");
        return;
    }
    let opt: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(f64::NAN);
    let dual_secs: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(3.0);
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
        println!("{name},closed,,,,,,,,,,,");
        return;
    }
    let directed = DirectedGraph::from_undirected(&ru);
    let idx = ArcIndex::new(&directed);
    let active = vec![true; idx.num_arcs()];
    let mut ascent = Cost::NEG_INFINITY;
    for &r in &terminals {
        ascent = ascent.max(dual_ascent_masked(&idx, r, &terminals, &active).lower_bound);
    }
    let root = terminals[0];

    let opts = FlowDualOptions { entry_budget: 24_000_000, ..FlowDualOptions::default() };
    let Ok(mut fd) = FlowDual::new(&idx, root, &terminals, opts) else {
        println!("{name},refused,,,,,,,,,,,");
        return;
    };
    // The cutoff the reduction will run at: the instance's own optimum when it is
    // known, which is the tightest honest one and the one that makes the
    // comparison hardest for the *new* rule rather than easiest.
    let ub = if opt.is_finite() { opt - offset } else { Cost::INFINITY };
    fd.set_target(Some(ub));
    fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs_f64(dual_secs), u64::MAX, 8);
    let l = fd.finish(&idx);
    let (lv, d) = fd.pricing();

    // The shape of the d-graph.
    let m = idx.num_arcs();
    let zero = d.iter().filter(|&&x| x <= 1e-9).count();
    let budget = ub - lv;
    let under = d.iter().filter(|&&x| x <= budget + 1e-9).count();
    // Largest component of the graph on arcs of price zero (both orientations
    // free), as an undirected connectivity question.
    let n = idx.num_nodes();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(p: &mut Vec<usize>, x: usize) -> usize {
        let mut x = x;
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    for a in 0..m as ArcId {
        if d[a as usize] <= 1e-9 {
            let (u, v) = (find(&mut parent, idx.tail(a) as usize), find(&mut parent, idx.head(a) as usize));
            parent[u] = v;
        }
    }
    let mut size = std::collections::HashMap::new();
    for v in 0..n {
        let r = find(&mut parent, v);
        *size.entry(r).or_insert(0usize) += 1;
    }
    let biggest = size.values().copied().max().unwrap_or(0);

    // What the fixpoint deletes, with and without the pricing.
    let base = ReduceConfig { initial_upper_bound: ub, ..Default::default() };
    let plain = tighten(ru.clone(), terminals.clone(), &base);
    let priced_cfg = ReduceConfig {
        initial_upper_bound: ub,
        initial_lower_bound: lv,
        initial_dual: Some(ArcDual { root, value: lv, reduced: d.clone() }),
        ..Default::default()
    };
    let priced = tighten(ru.clone(), terminals.clone(), &priced_cfg);

    eprintln!(
        "{name}: |V|={} |E|={} |R|={} ascent={:.1} L={:.1} UB={:.1} budget={:.1} | \
         zero-price arcs {zero}/{m} ({:.1}%), arcs under budget {under}/{m}, \
         biggest free component {biggest}/{n} | reduce |E| {} -> plain {} (off {:.0}, LB {:.1})          priced {} (off {:.0}, LB {:.1})",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        ascent + offset,
        l + offset,
        ub + offset,
        budget,
        100.0 * zero as f64 / m as f64,
        ru.edges.len(),
        plain.graph.edges.len(),
        plain.offset,
        plain.lower_bound + plain.offset + offset,
        priced.graph.edges.len(),
        priced.offset,
        priced.lower_bound + priced.offset + offset,
    );
    println!(
        "{name},{opt},{:.1},{:.1},{:.1},{},{},{},{},{},{},{},{},{:.1},{:.1},{:.0},{:.0}",
        ascent + offset,
        l + offset,
        budget,
        zero,
        m,
        under,
        biggest,
        n,
        ru.edges.len(),
        plain.graph.edges.len(),
        priced.graph.edges.len(),
        plain.lower_bound + plain.offset + offset,
        priced.lower_bound + priced.offset + offset,
        plain.offset,
        priced.offset,
    );
}
