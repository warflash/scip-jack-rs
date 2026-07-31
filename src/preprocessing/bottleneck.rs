//! The bottleneck Steiner distance (special distance) test.
//!
//! # The rule
//!
//! Write `d` for the shortest-path metric of the current graph and `R` for its
//! terminals. For a sequence `u = w_0, w_1, ..., w_k, w_{k+1} = v` whose interior
//! vertices are all terminals, call `max_i d(w_i, w_{i+1})` its *bottleneck*. The
//! **bottleneck Steiner distance** `s(u,v)` is the least bottleneck over all such
//! sequences. The test is
//!
//! ```text
//! s(u,v) < c({u,v})   =>   no optimal tree uses {u,v}.
//! ```
//!
//! ## Proof
//!
//! Let `T` be an optimal tree containing `e = {u,v}` and let `w_0..w_{k+1}` attain
//! `s(u,v) < c(e)`. Deleting `e` splits `T` into `T_u` containing `u` and `T_v`
//! containing `v`. Every interior `w_i` is a terminal, so it lies in `T`, hence in
//! `T_u` or in `T_v`; `w_0 = u` is in `T_u` and `w_{k+1} = v` is in `T_v`.
//! Therefore some consecutive pair has `w_i` in `T_u` and `w_{i+1}` in `T_v`. The
//! shortest path between them has length at most the bottleneck, so below `c(e)`,
//! and reconnects the two components. So `T - e + P(w_i, w_{i+1})` spans every
//! terminal and costs strictly less than `T`, contradicting optimality.
//!
//! No path involved can traverse `e` itself: such a path has length at least
//! `c(e)`, while all of them are strictly shorter. The strictness also makes it
//! safe to delete every qualifying edge in one pass — each deletion is justified
//! against the graph as it stood at the start of the pass, and no optimal tree of
//! that graph uses any of them.
//!
//! # What this replaces
//!
//! The previous test only allowed `k = 1`: a detour through one terminal, scored
//! as `min_t max(d(u,t), d(v,t))`. Multi-terminal chains are strictly stronger,
//! and matter most on dense instances where a pair of far-apart endpoints is
//! nonetheless linked by a chain of short terminal-to-terminal hops.
//!
//! The old code also compared against `bsd + 0.5` rather than `bsd`, a fudge added
//! to stop it removing edges it should not have. Nothing here needs it: the
//! inequality is strict and the proof above is complete.
//!
//! # Computing it
//!
//! Interior hops run terminal-to-terminal, so their contribution is the bottleneck
//! distance in the complete graph on `R` weighted by `d`. Bottleneck distances in
//! a graph are realised by any minimum spanning tree, so one MST of that metric
//! closure plus a traversal per terminal gives every `B(t,t')`.
//!
//! Endpoint hops are then minimised over terminals. The `k = 1` case is checked
//! against *all* terminals; longer chains are checked against each endpoint's
//! [`NEAREST_TERMINALS`] closest terminals. Restricting the chain endpoints can
//! only raise the computed value, so the test stays conservative and sound.

use crate::graph::{Cost, NodeId};

use super::csr::Csr;
use super::ReducibleGraph;

/// Chain endpoints are searched among this many nearest terminals per vertex.
/// Restricting the search only weakens the test, never invalidates it.
const NEAREST_TERMINALS: usize = 4;

/// Above this many terminals the dense `|R| x |R|` bottleneck matrix is skipped
/// and only the single-terminal case is used.
const MAX_DENSE_TERMINALS: usize = 3000;

pub fn bottleneck_reductions(graph: &mut ReducibleGraph) -> u32 {
    let terminals: Vec<NodeId> = graph
        .terminals
        .iter()
        .copied()
        .filter(|&t| graph.is_node_valid(t))
        .collect();
    if terminals.len() < 2 {
        return 0;
    }
    let mut terminals = terminals;
    terminals.sort_unstable();

    let csr = Csr::build(graph);
    let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();

    let bottleneck = (terminals.len() <= MAX_DENSE_TERMINALS)
        .then(|| terminal_bottleneck(&terminals, &dist));

    // The nearest terminals of each vertex, as indices into `terminals`.
    let nearest = nearest_terminals(&terminals, &dist, csr.num_nodes);

    let candidates: Vec<(u32, NodeId, NodeId, Cost)> = graph
        .edges
        .iter()
        .filter(|e| graph.is_edge_valid(e.id) && !graph.contracted_edges.contains(&e.id))
        .map(|e| (e.id, e.src, e.dst, e.cost))
        .collect();

    let mut removed = 0;
    for (eid, u, v, cost) in candidates {
        if special_distance(u, v, cost, &terminals, &dist, bottleneck.as_ref(), &nearest) {
            graph.remove_edge(eid);
            removed += 1;
        }
    }
    removed
}

/// True when `s(u,v) < cost`, i.e. the edge is provably not in any optimal tree.
fn special_distance(
    u: NodeId,
    v: NodeId,
    cost: Cost,
    terminals: &[NodeId],
    dist: &[Vec<Cost>],
    bottleneck: Option<&Vec<Cost>>,
    nearest: &[Vec<u32>],
) -> bool {
    // Single-terminal detour, checked against every terminal.
    for i in 0..terminals.len() {
        let t = terminals[i];
        if t == u || t == v {
            continue;
        }
        let du = dist[i][u as usize];
        let dv = dist[i][v as usize];
        if du.max(dv) < cost - 1e-9 {
            return true;
        }
    }

    // Longer chains: u -> t1 ~> t2 -> v, with the middle hop's bottleneck taken
    // from the terminal metric closure.
    let Some(b) = bottleneck else { return false };
    let n = terminals.len();
    let (Some(nu), Some(nv)) = (nearest.get(u as usize), nearest.get(v as usize)) else {
        return false;
    };
    for &i in nu {
        let du = dist[i as usize][u as usize];
        if du >= cost - 1e-9 {
            continue;
        }
        for &j in nv {
            if i == j {
                continue;
            }
            let dv = dist[j as usize][v as usize];
            if dv >= cost - 1e-9 {
                continue;
            }
            let mid = b[i as usize * n + j as usize];
            if du.max(dv).max(mid) < cost - 1e-9 {
                return true;
            }
        }
    }
    false
}

/// All-pairs bottleneck distances between terminals in the metric closure.
///
/// Bottleneck (minimax) distances are realised by any minimum spanning tree, so a
/// Prim MST over the dense terminal metric followed by one traversal per terminal
/// yields the whole matrix in `O(|R|^2)`.
fn terminal_bottleneck(terminals: &[NodeId], dist: &[Vec<Cost>]) -> Vec<Cost> {
    let n = terminals.len();
    let w = |i: usize, j: usize| dist[i][terminals[j] as usize];

    // Prim.
    let mut in_tree = vec![false; n];
    let mut best = vec![Cost::INFINITY; n];
    let mut parent = vec![usize::MAX; n];
    let mut adj: Vec<Vec<(usize, Cost)>> = vec![Vec::new(); n];
    best[0] = 0.0;
    for _ in 0..n {
        let mut k = usize::MAX;
        for i in 0..n {
            if !in_tree[i] && (k == usize::MAX || best[i] < best[k]) {
                k = i;
            }
        }
        if k == usize::MAX || !best[k].is_finite() {
            break;
        }
        in_tree[k] = true;
        if parent[k] != usize::MAX {
            adj[k].push((parent[k], best[k]));
            adj[parent[k]].push((k, best[k]));
        }
        for i in 0..n {
            if !in_tree[i] {
                let c = w(k, i);
                if c < best[i] {
                    best[i] = c;
                    parent[i] = k;
                }
            }
        }
    }

    // Max edge on the tree path, by traversal from each terminal.
    let mut out = vec![Cost::INFINITY; n * n];
    let mut stack: Vec<(usize, usize, Cost)> = Vec::new();
    for s in 0..n {
        let mut seen = vec![false; n];
        seen[s] = true;
        out[s * n + s] = 0.0;
        stack.clear();
        stack.push((s, usize::MAX, 0.0));
        while let Some((v, _, acc)) = stack.pop() {
            for &(u, c) in &adj[v] {
                if seen[u] {
                    continue;
                }
                seen[u] = true;
                let m = acc.max(c);
                out[s * n + u] = m;
                stack.push((u, v, m));
            }
        }
    }
    out
}

/// Indices of the nearest terminals of every vertex.
fn nearest_terminals(terminals: &[NodeId], dist: &[Vec<Cost>], num_nodes: usize) -> Vec<Vec<u32>> {
    let mut out = vec![Vec::new(); num_nodes];
    let mut scratch: Vec<(Cost, u32)> = Vec::with_capacity(terminals.len());
    for v in 0..num_nodes {
        scratch.clear();
        for (i, d) in dist.iter().enumerate() {
            let dv = d[v];
            if dv.is_finite() {
                scratch.push((dv, i as u32));
            }
        }
        scratch.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        scratch.truncate(NEAREST_TERMINALS);
        out[v] = scratch.iter().map(|&(_, i)| i).collect();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{NodeType, SteinerInstance, UndirectedGraph};

    fn instance(g: &UndirectedGraph, terminals: Vec<NodeId>) -> SteinerInstance {
        SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: g.num_nodes,
            num_edges: g.edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals,
            root: Some(1),
        }
    }

    #[test]
    fn removes_an_edge_dominated_through_one_terminal() {
        // 1(T) -1- 2(T) -1- 3(T), plus the direct 1-3 edge at cost 5.
        let mut g = UndirectedGraph::new(3);
        for v in 1..=3u32 {
            g.add_node(v, NodeType::Terminal, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 3, 5.0);

        let inst = instance(&g, vec![1, 2, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert!(bottleneck_reductions(&mut rg) >= 1);
        assert!(!rg.is_edge_valid(2), "the cost-5 chord should go");
    }

    #[test]
    fn keeps_the_only_connection() {
        let mut g = UndirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 3.0);

        let inst = instance(&g, vec![1, 2]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert_eq!(bottleneck_reductions(&mut rg), 0);
    }

    #[test]
    fn multi_hop_chain_beats_the_single_terminal_test() {
        // Terminals 1,2,3,4 in a line with unit spacing; a chord 1-4 of cost 4.
        //
        //   single-terminal score: min_t max(d(1,t), d(4,t))
        //     t=2 -> max(1,2) = 2? no: d(4,2) = 2, so max(1,2) = 2 < 4 as well.
        // Make the chain necessary by spacing the terminals so that no single
        // terminal is close to both endpoints, but consecutive hops are short.
        let mut g = UndirectedGraph::new(5);
        for v in 1..=5u32 {
            let t = v != 5;
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        // Path 1 -3- 2 -3- 3 -3- 4 : consecutive terminals are 3 apart, but
        // d(1,4) = 9 and every single terminal is at least 6 from one endpoint.
        g.add_edge(1, 2, 3.0);
        g.add_edge(2, 3, 3.0);
        g.add_edge(3, 4, 3.0);
        // Chord of cost 5: beaten by the chain 1 -> 2 -> 3 -> 4 whose hops are
        // all 3, but not by any single-terminal detour, which costs at least 6.
        g.add_edge(1, 4, 5.0);

        let inst = instance(&g, vec![1, 2, 3, 4]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);

        // Single-terminal scores for the chord {1,4}: via 2 -> max(3, 6) = 6;
        // via 3 -> max(6, 3) = 6. Both exceed 5, so the old rule kept the chord.
        let dists: Vec<Vec<Cost>> = [1u32, 2, 3, 4]
            .iter()
            .map(|&t| Csr::build(&rg).dijkstra(t))
            .collect();
        for (i, _) in [1u32, 2, 3, 4].iter().enumerate() {
            let single = dists[i][1].max(dists[i][4]);
            assert!(single >= 5.0 - 1e-9, "single-terminal detour should not fire");
        }

        assert!(bottleneck_reductions(&mut rg) >= 1, "the chain test should fire");
        assert!(!rg.is_edge_valid(3), "chord 1-4 should be removed");
    }

    #[test]
    fn never_removes_an_edge_of_the_optimum() {
        // Randomised check: brute-force the optimum before and after reduction.
        let mut seed = 0x1234_5678_9ABC_DEF0u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..300 {
            let n = 5 + (rng() % 3) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 2 + (rng() % 3) as u32;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            let mut edges = Vec::new();
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        let c = 1.0 + (rng() % 9) as f64;
                        g.add_edge(u, v, c);
                        edges.push((u, v, c));
                    }
                }
            }
            let Some(before) = brute(n, &edges, &terminals) else { continue };

            let inst = instance(&g, terminals.clone());
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            bottleneck_reductions(&mut rg);

            let kept: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let after = brute(n, &kept, &terminals).unwrap_or(Cost::INFINITY);
            assert!(
                (after - before).abs() < 1e-9,
                "reduction changed the optimum: {before} -> {after}"
            );
        }
    }

    fn brute(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
        let m = edges.len();
        if m > 20 {
            return None;
        }
        let mut best = Cost::INFINITY;
        for mask in 0u32..(1u32 << m) {
            let mut parent: Vec<u32> = (0..=n).collect();
            fn find(p: &mut Vec<u32>, x: u32) -> u32 {
                if p[x as usize] != x {
                    let r = find(p, p[x as usize]);
                    p[x as usize] = r;
                }
                p[x as usize]
            }
            let mut cost = 0.0;
            for (i, &(u, v, c)) in edges.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    cost += c;
                    let (a, b) = (find(&mut parent, u), find(&mut parent, v));
                    parent[a as usize] = b;
                }
            }
            if cost >= best {
                continue;
            }
            let r0 = find(&mut parent, terminals[0]);
            if terminals.iter().all(|&t| find(&mut parent, t) == r0) {
                best = cost;
            }
        }
        if best.is_finite() { Some(best) } else { None }
    }
}
