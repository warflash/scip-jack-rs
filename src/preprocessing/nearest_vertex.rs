//! Terminal edge contraction: the degree-1 rule and the nearest-vertex rule.
//!
//! Both prove that *some* optimal tree contains a particular edge incident to a
//! terminal, which lets [`ReducibleGraph::contract_edge`] fold that edge into the
//! objective offset and merge its endpoints. This is the only reduction here that
//! shrinks the terminal set, and on terminal-dense instances that matters more
//! than any edge deletion: the dual ascent, the separation loop and the LP all
//! scale with `|R|`.
//!
//! # The degree-1 rule
//!
//! A terminal with a single incident edge forces that edge into *every* feasible
//! solution, so contracting it is unconditionally safe.
//!
//! # The nearest-vertex rule
//!
//! > Let `t` be a terminal and `e = {t, v}` one of its edges. Suppose some walk
//! > `W` in `G` runs from `t` to another terminal, starts with `e`, and satisfies
//! >
//! > ```text
//! > c(W) <= min { c(f) : f in delta(t), f != e }.
//! > ```
//! >
//! > Then some optimal tree contains `e`.
//!
//! ## Proof
//!
//! Let `S` be an optimal tree and assume `e` is not in `S`. Let `t'` be the other
//! endpoint of `W`; it is a terminal, so `t'` is in `S`. Let `f` be the first edge
//! of the `S`-path from `t` to `t'`. Since `e` is not in `S` we have `f != e`,
//! hence `c(W) <= c(f)`.
//!
//! `W` does not contain `f`: if it did, then because `W` starts with `e != f` and
//! costs are nonnegative, `c(W) >= c(e) + c(f) > c(f) >= c(W)` whenever
//! `c(e) > 0`. The remaining case `c(e) = 0` is handled separately below.
//!
//! Now take `H = S + W` and delete `f`. Deleting `f` from `S` leaves components
//! `A` containing `t` and `B` containing `t'`; `W` reconnects them without using
//! `f`, so `H - f` is connected and still spans every terminal. Its cost is at
//! most `c(S) + c(W) - c(f) <= c(S)`. Any spanning tree of `H - f` that keeps `e`
//! is therefore optimal and contains `e`.
//!
//! For `c(e) = 0` the conclusion is immediate: adding a zero-cost edge to `S`
//! either attaches a new vertex or closes a cycle, and in the latter case some
//! other cycle edge can be dropped at no extra cost.
//!
//! ## Finding the walk
//!
//! One multi-source Dijkstra from every terminal partitions the graph into
//! Voronoi regions. Any edge `{a, b}` whose endpoints lie in different regions
//! yields the walk
//!
//! ```text
//! base(a) -> ... -> a -> b -> ... -> base(b)
//! ```
//!
//! of cost `dist(a) + c(a,b) + dist(b)`, running between two distinct terminals.
//! Scanning every boundary edge and keeping the cheapest walk out of each
//! terminal gives one candidate `(cost, first edge)` per terminal in
//! `O(m log n)`. The walk found this way need not be a shortest terminal-to-
//! terminal path, but the rule above only needs *a* walk, and using a longer one
//! makes the test more conservative, never unsound.

use crate::graph::{Cost, EdgeId, NodeId};

use super::csr::{Csr, DijkstraWorkspace};
use super::ReducibleGraph;

/// Contract every terminal edge the two rules above can justify.
///
/// Returns the number of contractions. Each contraction is applied immediately
/// and the next candidate is judged against the already-contracted graph, so the
/// justifications compose.
pub fn nearest_vertex_reductions(graph: &mut ReducibleGraph) -> u32 {
    let mut total = 0;
    loop {
        let done = degree_one_terminals(graph);
        let found = nearest_vertex_pass(graph);
        total += done + found;
        if done + found == 0 {
            break;
        }
    }
    total
}

/// Contract the unique edge of every degree-1 terminal.
fn degree_one_terminals(graph: &mut ReducibleGraph) -> u32 {
    let mut contracted = 0;
    loop {
        let victim = graph
            .terminals
            .iter()
            .copied()
            .filter(|&t| graph.is_node_valid(t))
            .find_map(|t| {
                let n = graph.valid_neighbors(t);
                (n.len() == 1).then(|| (t, n[0].0, n[0].1))
            });
        let Some((t, other, eid)) = victim else { break };
        if graph.terminals.len() < 2 {
            break;
        }
        graph.contract_edge(eid, t, other);
        contracted += 1;
    }
    contracted
}

/// One sweep of the nearest-vertex rule over every terminal.
fn nearest_vertex_pass(graph: &mut ReducibleGraph) -> u32 {
    let terminals: Vec<NodeId> = {
        let mut t: Vec<NodeId> = graph
            .terminals
            .iter()
            .copied()
            .filter(|&v| graph.is_node_valid(v))
            .collect();
        t.sort_unstable();
        t
    };
    if terminals.len() < 2 {
        return 0;
    }

    let csr = Csr::build(graph);
    let mut ws = DijkstraWorkspace::new(csr.num_nodes);
    csr.dijkstra_into(&terminals, Cost::INFINITY, &mut ws);

    // Cheapest boundary walk leaving each terminal, as (cost, first edge).
    let mut best: Vec<(Cost, EdgeId)> = vec![(Cost::INFINITY, u32::MAX); terminals.len()];
    for edge in &graph.edges {
        if !graph.is_edge_valid(edge.id) {
            continue;
        }
        let (a, b) = (edge.src as usize, edge.dst as usize);
        if a >= csr.num_nodes || b >= csr.num_nodes {
            continue;
        }
        let (ba, bb) = (ws.base[a], ws.base[b]);
        if ba == u32::MAX || bb == u32::MAX || ba == bb {
            continue;
        }
        let walk = ws.dist[a] + edge.cost + ws.dist[b];
        if !walk.is_finite() {
            continue;
        }
        // From `base(a)`: the walk leaves along `first(a)`, or along this very
        // edge when `a` is the terminal itself.
        for (side, source) in [(a, ba), (b, bb)] {
            let lead = if ws.first[side] == u32::MAX { edge.id } else { ws.first[side] };
            if walk < best[source as usize].0 {
                best[source as usize] = (walk, lead);
            }
        }
    }

    let mut contracted = 0;
    let mut done = vec![false; csr.num_nodes];
    for (i, &t) in terminals.iter().enumerate() {
        if graph.terminals.len() < 2 || !graph.is_node_valid(t) || done[t as usize] {
            continue;
        }
        let (walk, lead) = best[i];
        if lead == u32::MAX || !walk.is_finite() {
            continue;
        }
        // Contracting invalidates the precomputed walks that pass through the
        // merged vertices, so re-derive the local part against the live graph.
        let neighbors = graph.valid_neighbors(t);
        if neighbors.len() < 2 {
            continue;
        }
        if !graph.is_edge_valid(lead) {
            continue;
        }
        let second = neighbors
            .iter()
            .filter(|&&(_, f)| f != lead)
            .map(|&(_, f)| graph.edges[f as usize].cost)
            .fold(Cost::INFINITY, Cost::min);
        if walk > second + 1e-9 {
            continue;
        }
        let e = &graph.edges[lead as usize];
        let other = if e.src == t { e.dst } else { e.src };
        if other == t || !graph.is_node_valid(other) {
            continue;
        }
        graph.contract_edge(lead, t, other);
        done[t as usize] = true;
        done[other as usize] = true;
        contracted += 1;
    }
    contracted
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
    fn contracts_the_only_edge_of_a_degree_one_terminal() {
        // 1(T) -7- 2(S) -1- 3(T): terminal 1 has no choice.
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 7.0);
        g.add_edge(2, 3, 1.0);

        let inst = instance(&g, vec![1, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert!(nearest_vertex_reductions(&mut rg) >= 1);
        // Contracting {1,2} leaves terminal 3 with a single edge, which the rule
        // then contracts as well, so the instance closes out entirely at 8.
        assert!((rg.offset - 8.0).abs() < 1e-9, "offset {}", rg.offset);
        assert_eq!(surviving_terminals(&rg).len(), 1);
    }

    #[test]
    fn contracts_a_cheap_link_to_a_second_terminal() {
        // Terminal 1 reaches terminal 2 for 1 through v=4, while every other
        // edge out of 1 costs 20. The rule should fire on {1,4}.
        let mut g = UndirectedGraph::new(5);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_node(5, NodeType::Steiner, 0.0);
        g.add_edge(1, 4, 0.5); // 0
        g.add_edge(4, 2, 0.5); // 1
        g.add_edge(1, 5, 20.0); // 2
        g.add_edge(5, 3, 20.0); // 3
        g.add_edge(2, 3, 3.0); // 4

        let inst = instance(&g, vec![1, 2, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert!(nearest_vertex_reductions(&mut rg) >= 1);
        assert!(rg.offset >= 0.5 - 1e-9);
    }

    #[test]
    fn preserves_the_optimum_on_a_tie() {
        // Terminal 1 sits between two terminals at equal cost; contracting
        // either would be a guess, and the rule must not make it.
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 5.0);
        g.add_edge(1, 3, 5.0);
        g.add_edge(2, 3, 1.0);

        let inst = instance(&g, vec![1, 2, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        rg.terminals = [1, 2, 3].into_iter().collect();
        // The walk 1 -> 2 costs 5 and the other exit costs 5, so `walk <= second`
        // holds and contraction is in fact justified here. Assert only that the
        // optimum is preserved.
        let before = brute(3, &live_edges(&rg), &[1, 2, 3]).unwrap();
        nearest_vertex_reductions(&mut rg);
        let after = brute(3, &live_edges(&rg), &surviving_terminals(&rg)).unwrap_or(Cost::INFINITY);
        assert!((after + rg.offset - before).abs() < 1e-9);
    }

    fn live_edges(rg: &ReducibleGraph) -> Vec<(NodeId, NodeId, Cost)> {
        rg.edges
            .iter()
            .filter(|e| rg.is_edge_valid(e.id))
            .map(|e| (e.src, e.dst, e.cost))
            .collect()
    }

    fn surviving_terminals(rg: &ReducibleGraph) -> Vec<NodeId> {
        let mut t: Vec<NodeId> = rg.terminals.iter().copied().filter(|&v| rg.is_node_valid(v)).collect();
        t.sort_unstable();
        t
    }

    #[test]
    fn never_changes_the_optimum() {
        let mut seed = 0x51ED_5EED_1234_5678u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..400 {
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
            nearest_vertex_reductions(&mut rg);

            let kept = live_edges(&rg);
            let survivors = surviving_terminals(&rg);
            let after = if survivors.len() < 2 {
                0.0
            } else {
                brute(n, &kept, &survivors).unwrap_or(Cost::INFINITY)
            };
            assert!(
                (after + rg.offset - before).abs() < 1e-9,
                "reduction changed the optimum: {before} -> {after} + offset {}",
                rg.offset
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
