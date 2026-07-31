//! Deleting a Steiner vertex whose star is dominated by a special-distance tree.
//!
//! The bottleneck (special) distance test deletes *edges*. Its natural companion
//! deletes *vertices*, and on dense instances it is by far the stronger of the
//! two: a random graph with average degree twenty has very few removable edges
//! but a great many removable Steiner vertices.
//!
//! # The rule
//!
//! Let `v` be a Steiner vertex with neighbourhood `N(v)`, and write `s` for the
//! special distance **in `G - v`**. If for every `Q` contained in `N(v)` with
//! `|Q| >= 2`
//!
//! ```text
//! mst_s(Q) <= sum over u in Q of c(v, u),
//! ```
//!
//! then some optimal tree avoids `v`, so `v` and its edges may be deleted.
//!
//! Pairs matter as much as triples. Inclusion-minimality only rules out Steiner
//! *leaves*: a Steiner vertex sitting in the middle of a path of an optimal tree
//! has degree two there and is perfectly minimal, so a rule that only checked
//! `|Q| >= 3` would delete vertices that every optimum routes through. The
//! `|Q| = 2` case is exactly the bottleneck test applied to the two-edge path
//! `q1 - v - q2`.
//!
//! # Proof
//!
//! Let `S` be an inclusion-minimal optimal tree containing `v`. Since `v` is a
//! Steiner vertex and `S` is inclusion-minimal, `v` is not a leaf, so
//! `deg_S(v) >= 2`; let `Q` be the set of `S`-neighbours of `v`, so `|Q| >= 2`
//! and `Q` is contained in `N(v)`. Delete `v` and its `|Q|` tree edges. `S` falls
//! into exactly `|Q|` components, each containing exactly one vertex of `Q`, and
//! together they still contain every terminal.
//!
//! **Reconnection lemma.** Let `F` be any subgraph of `G - v` containing every
//! terminal, and let `a, b` lie in different components of `F`. Then `G - v`
//! contains a path of cost at most `s(a, b)` joining two *different* components
//! of `F`.
//!
//! *Proof.* Take a chain `a = w_0, w_1, ..., w_k, w_{k+1} = b` attaining
//! `s(a, b)`, whose interior vertices are terminals. Every `w_i` lies in `F`, and
//! `w_0`, `w_{k+1}` lie in different components, so some consecutive pair
//! `w_i, w_{i+1}` straddles two components. The shortest path between them has
//! cost at most the chain's bottleneck, which is `s(a, b)`. ∎
//!
//! Now merge the `|Q|` components in `|Q| - 1` steps. At each step, among the
//! pairs of `Q` still lying in different components, pick the one minimising `s`,
//! and apply the lemma: some two components merge at cost at most that minimum.
//!
//! **The total is at most `mst_s(Q)`.** Sort the `s`-MST edges of `Q` as
//! `e_1 <= ... <= e_{|Q|-1}`. When `p` components remain, the MST is connected, so
//! at least `p - 1` of its edges cross the current partition; the cheapest
//! crossing MST edge therefore has index at most `|Q| - p + 1`, so its weight is
//! at most `w(e_{|Q|-p+1})`. Step `i` runs with `p = |Q| - i + 1` components and
//! so costs at most `w(e_i)`. Summing over `i = 1, ..., |Q| - 1` gives
//! `mst_s(Q)`.
//!
//! Every path added lives in `G - v`, so the result is a connected subgraph of
//! `G - v` spanning every terminal, of cost at most
//! `c(S) - sum_{u in Q} c(v, u) + mst_s(Q) <= c(S)`. Any spanning tree of it is
//! an optimal tree avoiding `v`. ∎
//!
//! # Why `s` must be computed in `G - v`
//!
//! The replacement paths have to avoid `v`, otherwise the "optimal tree avoiding
//! `v`" that the proof constructs may quietly use `v` again. Computing the
//! distances in `G` and hoping is exactly the kind of shortcut that silently
//! breaks exactness, so this implementation masks `v` out of the graph before
//! running any search.
//!
//! # What is actually computed
//!
//! Any **upper bound** on `s` keeps the test conservative, because it can only
//! make `mst_s(Q)` larger and the condition harder to satisfy. This code uses
//!
//! ```text
//! s(a, b) <= min( d(a, b),  min over terminals t of max( d(a, t), d(b, t) ) )
//! ```
//!
//! with `d` the shortest-path metric of `G - v` — the one- and zero-hop chains.
//! Longer chains would need the terminal-to-terminal bottleneck matrix of `G - v`,
//! which changes with every candidate and is not worth recomputing.
//!
//! All searches are cut off at `sum_{u in N(v)} c(v, u)`, the largest value the
//! test can ever use. Truncation only weakens the test.
//!
//! # Composing the deletions
//!
//! The conclusion is `<=`, not `<`, so "some optimum avoids `v_1`" and "some
//! optimum avoids `v_2`" do not compose into "some optimum avoids both". This
//! pass therefore deletes candidates one at a time and evaluates each against the
//! graph from which the earlier ones are already absent, which does compose: each
//! step preserves the optimum of the graph it was applied to.

use std::time::Instant;

use crate::graph::{Cost, NodeId};

use super::csr::{Csr, DijkstraWorkspace};
use super::ReducibleGraph;

/// Only vertices of degree at most this are examined. The number of subsets to
/// check grows as `2^k` and the star cost grows with `k`, so high-degree
/// vertices are both expensive to test and unlikely to pass.
const MAX_DEGREE: usize = 8;

pub fn vertex_reductions(graph: &mut ReducibleGraph, deadline: Option<Instant>) -> u32 {
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

    let mut csr = Csr::build(graph);
    let mut ws = DijkstraWorkspace::new(csr.num_nodes);
    let mut dist: Vec<Vec<Cost>> = Vec::new();

    let candidates: Vec<NodeId> = graph
        .nodes
        .iter()
        .map(|n| n.id)
        .filter(|&v| graph.is_node_valid(v) && !graph.is_terminal(v))
        .collect();

    let mut removed = 0;
    for (seen, v) in candidates.into_iter().enumerate() {
        // The per-candidate cost is a handful of bounded Dijkstras, so checking
        // the clock every few hundred candidates is granular enough.
        if seen % 256 == 0 && deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        if csr.is_masked(v) {
            continue;
        }
        let star: Vec<(NodeId, Cost)> = csr
            .neighbors(v)
            .filter(|&(u, _, _)| !csr.is_masked(u))
            .map(|(u, c, _)| (u, c))
            .collect();
        // Parallel edges reach the same neighbour twice; keep the cheapest.
        let mut star = star;
        star.sort_by(|a, b| {
            a.0.cmp(&b.0).then(a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal))
        });
        star.dedup_by_key(|&mut (u, _)| u);
        let k = star.len();
        if !(3..=MAX_DEGREE).contains(&k) {
            continue;
        }

        let radius: Cost = star.iter().map(|&(_, c)| c).sum();
        if !radius.is_finite() {
            continue;
        }

        // Distances in `G - v` from each neighbour, truncated at `radius`.
        // Only the entries at terminals and at the other star members are ever
        // read, so the full distance array is never retained.
        let width = terminals.len() + k;
        csr.mask(v);
        dist.clear();
        for &(u, _) in &star {
            csr.dijkstra_into(&[u], radius, &mut ws);
            let mut row = Vec::with_capacity(width);
            row.extend(terminals.iter().map(|&t| ws.dist[t as usize]));
            row.extend(star.iter().map(|&(w, _)| ws.dist[w as usize]));
            dist.push(row);
        }
        csr.unmask(v);

        // Pairwise special-distance upper bounds.
        let base = terminals.len();
        let mut sd = vec![Cost::INFINITY; k * k];
        for i in 0..k {
            for j in (i + 1)..k {
                let mut best = dist[i][base + j];
                for t in 0..base {
                    let (a, b) = (dist[i][t], dist[j][t]);
                    if a.is_finite() && b.is_finite() {
                        best = best.min(a.max(b));
                    }
                }
                sd[i * k + j] = best;
                sd[j * k + i] = best;
            }
        }

        if !star_is_dominated(&star, &sd, k) {
            continue;
        }

        csr.mask(v);
        graph.remove_node(v);
        removed += 1;
    }

    removed
}

/// True when `mst_s(Q) <= sum_{u in Q} c(v, u)` for every `Q` of size at least 2.
fn star_is_dominated(star: &[(NodeId, Cost)], sd: &[Cost], k: usize) -> bool {
    let mut members = Vec::with_capacity(k);
    for mask in 0u32..(1u32 << k) {
        if mask.count_ones() < 2 {
            continue;
        }
        members.clear();
        let mut budget = 0.0;
        for i in 0..k {
            if mask >> i & 1 == 1 {
                members.push(i);
                budget += star[i].1;
            }
        }
        let Some(tree) = mst(&members, sd, k) else { return false };
        if tree > budget + 1e-9 {
            return false;
        }
    }
    true
}

/// Prim's algorithm on the special-distance metric restricted to `members`.
/// Returns `None` when the metric leaves the subset disconnected.
fn mst(members: &[usize], sd: &[Cost], k: usize) -> Option<Cost> {
    let n = members.len();
    let mut in_tree = vec![false; n];
    let mut best = vec![Cost::INFINITY; n];
    best[0] = 0.0;
    let mut total = 0.0;
    for _ in 0..n {
        let mut pick = usize::MAX;
        for i in 0..n {
            if !in_tree[i] && (pick == usize::MAX || best[i] < best[pick]) {
                pick = i;
            }
        }
        if pick == usize::MAX || !best[pick].is_finite() {
            return None;
        }
        in_tree[pick] = true;
        total += best[pick];
        for i in 0..n {
            if !in_tree[i] {
                let w = sd[members[pick] * k + members[i]];
                if w < best[i] {
                    best[i] = w;
                }
            }
        }
    }
    Some(total)
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
    fn deletes_an_expensive_hub() {
        // Terminals 1,2,3 form a unit triangle. Vertex 4 is a Steiner hub joined
        // to all three at cost 10, so its star costs 30 while the triangle's MST
        // under the special distance costs 2.
        let mut g = UndirectedGraph::new(4);
        for v in 1..=3u32 {
            g.add_node(v, NodeType::Terminal, 0.0);
        }
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 3, 1.0);
        g.add_edge(1, 4, 10.0);
        g.add_edge(2, 4, 10.0);
        g.add_edge(3, 4, 10.0);

        let inst = instance(&g, vec![1, 2, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert_eq!(vertex_reductions(&mut rg, None), 1);
        assert!(!rg.is_node_valid(4));
    }

    #[test]
    fn keeps_a_hub_that_is_the_cheap_way_round() {
        // The same shape with the roles reversed: the hub costs 1 per leg and
        // the triangle 10 per side, so the hub belongs to every optimum.
        let mut g = UndirectedGraph::new(4);
        for v in 1..=3u32 {
            g.add_node(v, NodeType::Terminal, 0.0);
        }
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 10.0);
        g.add_edge(2, 3, 10.0);
        g.add_edge(1, 3, 10.0);
        g.add_edge(1, 4, 1.0);
        g.add_edge(2, 4, 1.0);
        g.add_edge(3, 4, 1.0);

        let inst = instance(&g, vec![1, 2, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert_eq!(vertex_reductions(&mut rg, None), 0);
        assert!(rg.is_node_valid(4));
    }

    #[test]
    fn never_changes_the_optimum() {
        let mut seed = 0x0BAD_C0DE_F00D_1111u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..500 {
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
            vertex_reductions(&mut rg, None);

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
