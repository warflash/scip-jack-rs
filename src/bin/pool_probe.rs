//! Measures the treewidth of the subgraph an elite pool of primal solutions
//! spans.
//!
//! The recombination step today takes the union of the vertex sets of the best
//! few trees and runs a minimum spanning tree over the induced subgraph. That
//! is a heuristic over a ground set on which the *exact* answer might be
//! affordable, because a union of `k` near-identical trees is nearly a tree:
//! its cyclomatic number is the number of edges by which the trees disagree,
//! and treewidth is bounded by that number plus one.
//!
//! This probe reports, per instance and per pool size, the union's size, its
//! cyclomatic number, and the width a heuristic decomposition of it achieves.
//! Whether an exact recombination is worth writing is exactly that column.
//!
//! ```text
//! pool_probe <instance>
//! ```

use std::env;

use scip_jack::graph::algorithms::tree_decomposition::decompose;
use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{ArcId, Cost, DirectedGraph, NodeId, NodeType, UndirectedGraph};
use scip_jack::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use scip_jack::heuristics::sph::{shortest_path_heuristic, SphResult, SphWorkspace};
use scip_jack::preprocessing::preprocess_until;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: pool_probe <instance>");
        return;
    }
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
    let (rg, _) = preprocess_until(&instance, &graph, None);
    let (ri, ru) = rg.to_instance();
    let terminals = ri.terminals.clone();
    if terminals.len() < 2 {
        println!("{name}: trivial");
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
    let mut ws = SphWorkspace::new(idx.num_nodes());
    let mut kws = KeyPathWorkspace::new(idx.num_nodes());
    let root = terminals[0];

    // A pool of the same shape the round builds: greedy starts against the true
    // costs and against each ascent's reduced costs, every tree key-path
    // polished.
    let mut pool: Vec<SphResult> = Vec::new();
    let push = |r: SphResult, pool: &mut Vec<SphResult>| pool.push(r);
    let starts: Vec<NodeId> = terminals.iter().copied().take(8).collect();
    for &s in &starts {
        if let Some(r) =
            shortest_path_heuristic(&idx, &active, &true_costs, root, s, &terminals, &is_terminal, &mut ws)
        {
            let r = key_path_exchange(&idx, &active, root, &r, &is_terminal, 6, &mut kws, &mut ws)
                .unwrap_or(r);
            push(r, &mut pool);
        }
    }
    for &r0 in terminals.iter().take(3) {
        let da = dual_ascent_masked(&idx, r0, &terminals, &active);
        for &s in &starts {
            if let Some(r) = shortest_path_heuristic(
                &idx, &active, &da.reduced_costs, root, s, &terminals, &is_terminal, &mut ws,
            ) {
                let r = key_path_exchange(&idx, &active, root, &r, &is_terminal, 6, &mut kws, &mut ws)
                    .unwrap_or(r);
                push(r, &mut pool);
            }
        }
    }
    pool.sort_by(|a, b| a.cost.partial_cmp(&b.cost).unwrap());
    pool.dedup_by(|a, b| (a.cost - b.cost).abs() < 1e-9);
    if pool.is_empty() {
        println!("{name}: no feasible tree");
        return;
    }

    println!(
        "{name}: |V|={} |E|={} |R|={} pool={} best={:.0}",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        pool.len(),
        pool[0].cost
    );
    for take in [2usize, 3, 4, 6, 8] {
        if take > pool.len() {
            break;
        }
        let sub = union_subgraph(&idx, &pool[..take], &is_terminal);
        let nu = sub.edges.len() as i64 - sub.num_nodes as i64 + 1;
        let w = decompose(&sub, 64, None).map(|t| {
            assert!(t.verify(&sub));
            t.width
        });
        println!(
            "  take {take}: |V'|={} |E'|={} nu={} width={}",
            sub.num_nodes,
            sub.edges.len(),
            nu,
            w.map_or(">64".to_string(), |w| w.to_string())
        );
    }
}

/// The subgraph spanned by the edges of every tree in `trees`.
fn union_subgraph(idx: &ArcIndex, trees: &[SphResult], is_terminal: &[bool]) -> UndirectedGraph {
    let mut edges: Vec<(NodeId, NodeId, Cost)> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for t in trees {
        for &a in &t.arcs {
            let (u, v) = (idx.tail(a), idx.head(a));
            let key = (u.min(v), u.max(v));
            if seen.insert(key) {
                edges.push((key.0, key.1, idx.cost(a)));
            }
        }
    }
    let mut nodes: Vec<NodeId> = edges.iter().flat_map(|&(u, v, _)| [u, v]).collect();
    nodes.sort_unstable();
    nodes.dedup();
    let map: std::collections::HashMap<NodeId, NodeId> =
        nodes.iter().enumerate().map(|(i, &v)| (v, i as NodeId + 1)).collect();
    let mut g = UndirectedGraph::new(nodes.len() as u32);
    for &v in &nodes {
        let t = if is_terminal[v as usize] { NodeType::Terminal } else { NodeType::Steiner };
        g.add_node(map[&v], t, 0.0);
    }
    for (u, v, c) in edges {
        g.add_edge(map[&u], map[&v], c);
    }
    g
}
