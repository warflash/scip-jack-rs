//! Bound-based reductions from a terminal-regions decomposition.
//!
//! Every elimination the solver had until now went through reduced costs: dual
//! ascent produces a lower bound `LB` and a slack `rho_a` per arc, and an arc
//! dies when `LB + rho_a > UB`. That makes the whole reduction power a function
//! of the LP-style gap `UB - LB`, and on the instances where the search stalls
//! that gap is exactly what refuses to close. The reductions here do not use the
//! dual at all: the lower bound they attach to a vertex or an edge is a purely
//! combinatorial quantity read off the graph, so they still bite when the ascent
//! has nothing left to give.
//!
//! Everything rests on one object.
//!
//! # Terminal-regions decomposition
//!
//! Let `G = (V, E)`, `c >= 0`, terminals `R` with `s = |R| >= 2`, and let
//! `d(x, y)` be the shortest-path distance in `G`.
//!
//! A *terminal-regions decomposition* is a family `H = { H_t : t in R }` of
//! pairwise disjoint vertex sets with
//!
//! - `t in H_t` and `H_t ∩ R = {t}` — each region owns exactly one terminal,
//! - `G[H_t]` connected,
//! - every vertex reachable from `R` lies in some `H_t`.
//!
//! The *radius* of a region is the cost of the cheapest way out of it:
//!
//! ```text
//! r(t) := min { d(t, x) : x not in H_t }.
//! ```
//!
//! This module uses the Voronoi decomposition — `H_t` is the set of vertices
//! whose nearest terminal is `t`, taken from the shortest-path forest of one
//! multi-source Dijkstra, which makes each region connected by construction. Any
//! other decomposition satisfying the three conditions would do; the theorems
//! below never look at how `H` was built.
//!
//! # The one lemma everything else is assembled from
//!
//! Write `R_F = R ∩ V(F)` for the terminals of a subgraph `F`.
//!
//! > **Lemma (subtree bound).** Let `F` be a subtree of `G` (a connected acyclic
//! > subgraph), `u in V(F)`, and `R_F` nonempty. Then there is a terminal
//! > `tau in R_F` with
//! >
//! > ```text
//! > c(F) >= d(u, tau) + sum over t in R_F \ {tau} of r(t).
//! > ```
//!
//! ## Proof
//!
//! Contract regions. For each `t`, the subgraph `F[H_t]` splits into connected
//! components; collect every such component, over every `t`, as the node set of a
//! graph `F*` whose edges are the edges of `F` joining two different components.
//! Contracting connected subgraphs of a tree leaves a tree, so `F*` is a tree.
//!
//! Two remarks that are used repeatedly:
//!
//! - *Every edge of `F*` crosses regions.* An edge of `F` with both endpoints in
//!   the same `H_t` lies inside `F[H_t]`, so its endpoints are in the same
//!   component and it is not an edge of `F*`.
//! - *A region's component holds at most one terminal.* A component of `F[H_t]`
//!   is contained in `H_t`, and `H_t ∩ R = {t}`.
//!
//! Root `F*` at the component `n_0` containing `u`; every other node `q` has a
//! parent edge `e_q`, and the sets `E(q) ∪ {e_q}` are pairwise disjoint and
//! disjoint from `E(n_0)`.
//!
//! *Region charge.* If `q != n_0` is the component holding terminal `t`, let
//! `e_q = {y, z}` with `y in q ⊆ H_t`. Then `z` is outside `H_t` (crossing edge),
//! and the `q`-path from `t` to `y` is a path of `G`, so
//!
//! ```text
//! c(E(q)) + c(e_q) >= d(t, y) + c(y, z) >= d(t, z) >= r(t).
//! ```
//!
//! Now two cases.
//!
//! **A terminal sits in `n_0`.** Only one can, say `t^0`. Take `tau = t^0`. The
//! `F`-path from `u` to `t^0` stays inside the connected set `n_0`, so
//! `c(E(n_0)) >= d(u, t^0)`. Every other terminal of `R_F` has its component
//! outside `n_0` and contributes its region charge on a disjoint edge set.
//!
//! **No terminal sits in `n_0`.** Let `tau` be a terminal of `R_F` whose
//! component `q_tau` is at minimum depth in `F*`. The `F*`-path
//! `n_0 = p_0, ..., p_j = q_tau` has no terminal component in its interior — one
//! would have smaller depth. The `F`-path from `u` to `tau` uses only edges of
//! `E(n_0) ∪ ⋃_{l<=j} (E(p_l) ∪ {e_{p_l}})`, so that edge set costs at least
//! `d(u, tau)`. Every terminal of `R_F` other than `tau` has its component off
//! that path, so its region charge lands on an untouched edge set.
//!
//! In both cases the charges are disjoint subsets of `E(F)` and `c >= 0`, so they
//! sum below `c(F)`. ∎
//!
//! # What the lemma gives
//!
//! Sort the radii `r_(1) <= r_(2) <= ... <= r_(s)` and write
//! `P_j = r_(1) + ... + r_(j)` for the sum of the `j` smallest.
//!
//! A tree is *pruned* if all of its leaves are terminals. Any Steiner tree can be
//! made pruned by repeatedly deleting Steiner leaves, which never increases its
//! cost and never drops a terminal. So it is enough to bound pruned trees: if
//! every pruned tree through `v` costs more than `UB`, then every tree of cost at
//! most `UB` prunes to one that avoids `v`, and `v` may be deleted without
//! raising the cheapest tree below `UB`.
//!
//! ## Theorem 1 (instance bound)
//!
//! `opt >= P_{s-1}`.
//!
//! Apply the lemma to `F = T` and `u = ` any terminal: `c(T) >= d(u, tau) + sum
//! over R \ {tau} of r(t) >= P_{s-1}`. ∎
//!
//! ## Theorem 2 (vertex bound)
//!
//! Let `v` be a Steiner vertex and `d_1(v) <= d_2(v)` the distances from `v` to
//! its nearest and second-nearest terminal. Every pruned tree `T` with
//! `v in V(T)` satisfies
//!
//! ```text
//! c(T) >= d_1(v) + d_2(v) + P_{s-2}.
//! ```
//!
//! ### Proof
//!
//! `v` is not a terminal and `T` is pruned, so `v` is not a leaf: rooting `T` at
//! `v` gives `p >= 2` branches `B_1, ..., B_p` (each including its edge at `v`).
//! The branches are edge-disjoint and cover `E(T)`, and the terminal sets `R_i`
//! partition `R`. Each `R_i` is nonempty, because a branch contains a leaf of `T`
//! and every leaf is a terminal. The lemma applied to `B_i ∪ {v}` at `u = v`
//! gives `tau_i in R_i` with
//!
//! ```text
//! c(B_i) >= d(v, tau_i) + sum over t in R_i \ {tau_i} of r(t),
//! ```
//!
//! and summing over `i`,
//!
//! ```text
//! c(T) >= sum_i d(v, tau_i) + sum over t not in {tau_1..tau_p} of r(t).
//! ```
//!
//! `v` lies in exactly one region, say `H_{t^0}`. For any terminal `t` with
//! `v not in H_t` we have `d(v, t) >= r(t)` directly from the definition of the
//! radius, so `d(v, tau_i) >= r(tau_i)` for every `tau_i != t^0` — that is, for
//! all but at most one index. Number the branches so that the exception, if it
//! exists, is `i = 1`. Trading the terms `i >= 3` back into the radius sum,
//!
//! ```text
//! c(T) >= d(v, tau_1) + d(v, tau_2) + sum over t not in {tau_1, tau_2} of r(t).
//! ```
//!
//! `tau_1 != tau_2` are terminals, so their two distances sum to at least
//! `d_1(v) + d_2(v)`, and a sum of `s - 2` radii is at least `P_{s-2}`. ∎
//!
//! ## Theorem 3 (edge bound)
//!
//! For `e = {a, b}` write
//!
//! ```text
//! delta(a, b) := min { d(a, t) + d(b, t') : t, t' in R, t != t' }.
//! ```
//!
//! Every pruned tree `T` with `e in E(T)` satisfies
//!
//! ```text
//! c(T) >= c(e) + delta(a, b) + P_{s-2}.
//! ```
//!
//! ### Proof
//!
//! `T - e` has components `T_a ∋ a` and `T_b ∋ b`. Each holds a terminal: if
//! `T_a` is the single vertex `a`, then `a` is a leaf of `T`, hence a terminal;
//! otherwise `T_a` has a leaf other than `a`, which is a leaf of `T`. Apply the
//! lemma to `T_a` at `a` and to `T_b` at `b`. The two terminal sets are disjoint,
//! so `tau_a != tau_b`, and
//!
//! ```text
//! c(T) = c(e) + c(T_a) + c(T_b)
//!      >= c(e) + d(a, tau_a) + d(b, tau_b) + sum over R \ {tau_a, tau_b} of r(t),
//! ```
//!
//! which is at least `c(e) + delta(a, b) + P_{s-2}`. ∎
//!
//! `delta` is computable from the two nearest terminals of each endpoint: it is
//! `d_1(a) + d_1(b)` when the two nearest terminals differ, and
//! `min(d_1(a) + d_2(b), d_2(a) + d_1(b))` when they coincide.
//!
//! # Relation to the incumbent
//!
//! The tests fire on a *strict* excess over `UB`, so they preserve every tree of
//! cost at most `UB`. That is stronger than the invariant the ascend-and-prune
//! loop already maintains for reduced-cost fixing, which only preserves trees
//! strictly cheaper than the incumbent. With `UB = infinity` — the standalone
//! preprocessing path — nothing is deleted and the optimum is preserved exactly.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::graph::{cmp_cost, Cost, NodeId};

use super::csr::{Csr, DijkstraWorkspace, Ordered};
use super::ReducibleGraph;

/// Distances from every vertex to its two nearest terminals.
struct TwoNearest {
    d1: Vec<Cost>,
    d2: Vec<Cost>,
    /// Index into the terminal list of the nearest terminal, or `u32::MAX`.
    b1: Vec<u32>,
}

/// Multi-source Dijkstra keeping the two best labels with *distinct* sources.
///
/// Correct because the property is hereditary along shortest paths: if `t` is
/// among the two nearest terminals of `v` and `y` lies on a shortest `t`-`v`
/// path, then `t` is among the two nearest terminals of `y`. Otherwise two
/// terminals `t', t''` would be strictly closer to `y` than `t`, and
/// `d(v, t°) <= d(y, t°) + d(y, v) < d(y, t) + d(y, v) = d(v, t)` for both of
/// them, contradicting `t` being second-nearest at `v`. So the label for `t`
/// survives at every vertex of the path and propagates to `v`.
fn two_nearest(csr: &Csr, terminals: &[NodeId]) -> TwoNearest {
    let n = csr.num_nodes;
    let mut out = TwoNearest {
        d1: vec![Cost::INFINITY; n],
        d2: vec![Cost::INFINITY; n],
        b1: vec![u32::MAX; n],
    };
    let mut b2 = vec![u32::MAX; n];
    let mut heap: BinaryHeap<(Reverse<Ordered>, u32, u32)> = BinaryHeap::new();
    for (i, &t) in terminals.iter().enumerate() {
        if (t as usize) < n && !csr.is_masked(t) {
            heap.push((Reverse(Ordered(0.0)), t, i as u32));
        }
    }

    while let Some((Reverse(Ordered(d)), v, base)) = heap.pop() {
        let vi = v as usize;
        if out.b1[vi] == base || b2[vi] == base {
            continue;
        }
        if out.b1[vi] == u32::MAX {
            out.d1[vi] = d;
            out.b1[vi] = base;
        } else if b2[vi] == u32::MAX {
            out.d2[vi] = d;
            b2[vi] = base;
        } else {
            continue;
        }
        for (u, c, _) in csr.neighbors(v) {
            let ui = u as usize;
            if csr.is_masked(u) || b2[ui] != u32::MAX || out.b1[ui] == base {
                continue;
            }
            heap.push((Reverse(Ordered(d + c)), u, base));
        }
    }
    out
}

/// Region radii, indexed like `terminals`, or `None` if some region has no way
/// out — which means the terminals do not all lie in one component.
///
/// `r(t) = min { d(t, x) : x not in H_t }` equals the minimum of
/// `dist(y) + c(y, z)` over edges leaving the region: any `t`-`x` path with
/// `x` outside crosses the boundary, and conversely each boundary edge exhibits
/// a vertex outside the region at that cost.
fn region_radii(
    csr: &Csr,
    graph: &ReducibleGraph,
    terminals: &[NodeId],
    ws: &DijkstraWorkspace,
) -> Option<Vec<Cost>> {
    let mut radius = vec![Cost::INFINITY; terminals.len()];
    for edge in &graph.edges {
        if !graph.is_edge_valid(edge.id) {
            continue;
        }
        let (a, b) = (edge.src as usize, edge.dst as usize);
        if a >= csr.num_nodes || b >= csr.num_nodes {
            continue;
        }
        let (ra, rb) = (ws.base[a], ws.base[b]);
        if ra == u32::MAX || rb == u32::MAX || ra == rb {
            continue;
        }
        let ca = ws.dist[a] + edge.cost;
        let cb = ws.dist[b] + edge.cost;
        if ca < radius[ra as usize] {
            radius[ra as usize] = ca;
        }
        if cb < radius[rb as usize] {
            radius[rb as usize] = cb;
        }
    }
    radius.iter().all(|r| r.is_finite()).then_some(radius)
}

/// Sorted prefix sums of the radii: `prefix[j]` is the sum of the `j` smallest.
fn radius_prefix(mut radius: Vec<Cost>) -> Vec<Cost> {
    radius.sort_by(|a, b| cmp_cost(*a, *b));
    let mut prefix = Vec::with_capacity(radius.len() + 1);
    prefix.push(0.0);
    let mut acc = 0.0;
    for r in radius {
        acc += r;
        prefix.push(acc);
    }
    prefix
}

/// Lower bound on the optimum of the live graph, from Theorem 1.
///
/// Returns `0.0` when the decomposition cannot be built — a bound of zero is
/// always valid.
pub fn region_lower_bound(graph: &ReducibleGraph) -> Cost {
    let terminals = live_terminals(graph);
    if terminals.len() < 2 {
        return 0.0;
    }
    let csr = Csr::build(graph);
    let mut ws = DijkstraWorkspace::new(csr.num_nodes);
    csr.dijkstra_into(&terminals, Cost::INFINITY, &mut ws);
    let Some(radius) = region_radii(&csr, graph, &terminals, &ws) else {
        return 0.0;
    };
    let prefix = radius_prefix(radius);
    prefix[terminals.len() - 1]
}

fn live_terminals(graph: &ReducibleGraph) -> Vec<NodeId> {
    let mut t: Vec<NodeId> = graph
        .terminals
        .iter()
        .copied()
        .filter(|&v| graph.is_node_valid(v))
        .collect();
    t.sort_unstable();
    t
}

/// Delete every vertex and edge whose region bound exceeds `upper_bound`.
///
/// Returns the number of deletions. All deletions of one sweep are justified
/// against the same graph and may be applied together: each says "no pruned tree
/// of cost at most `UB` uses this element", so a tree of cost at most `UB`
/// avoids all of them simultaneously. Sweeps are repeated to a fixpoint, and
/// since deletion only lengthens distances, every bound is monotone.
pub fn bound_reductions(graph: &mut ReducibleGraph, upper_bound: Cost) -> u32 {
    if !upper_bound.is_finite() {
        return 0;
    }
    let mut total = 0;
    loop {
        let killed = bound_sweep(graph, upper_bound);
        total += killed;
        if killed == 0 {
            break;
        }
    }
    total
}

fn bound_sweep(graph: &mut ReducibleGraph, upper_bound: Cost) -> u32 {
    let terminals = live_terminals(graph);
    let s = terminals.len();
    if s < 2 {
        return 0;
    }

    let csr = Csr::build(graph);
    let mut ws = DijkstraWorkspace::new(csr.num_nodes);
    csr.dijkstra_into(&terminals, Cost::INFINITY, &mut ws);
    let Some(radius) = region_radii(&csr, graph, &terminals, &ws) else {
        return 0;
    };
    let prefix = radius_prefix(radius);
    // Theorems 2 and 3 both consume two of the `s` regions.
    let base = prefix[s - 2];
    if base > upper_bound + 1e-9 {
        // The instance bound alone already exceeds the cutoff. Deleting the whole
        // graph would be formally implied, but that is a statement for the caller
        // to act on, not for a reduction to enact.
        return 0;
    }

    let near = two_nearest(&csr, &terminals);
    let mut killed = 0;

    let mut doomed: Vec<NodeId> = Vec::new();
    for node in &graph.nodes {
        let v = node.id;
        if !graph.is_node_valid(v) || graph.is_terminal(v) || (v as usize) >= csr.num_nodes {
            continue;
        }
        let vi = v as usize;
        let lb = near.d1[vi] + near.d2[vi] + base;
        if lb > upper_bound + 1e-9 {
            doomed.push(v);
        }
    }

    let mut dead_edges: Vec<u32> = Vec::new();
    for edge in &graph.edges {
        if !graph.is_edge_valid(edge.id) {
            continue;
        }
        let (a, b) = (edge.src as usize, edge.dst as usize);
        if a >= csr.num_nodes || b >= csr.num_nodes {
            continue;
        }
        let delta = if near.b1[a] != near.b1[b] || near.b1[a] == u32::MAX {
            near.d1[a] + near.d1[b]
        } else {
            (near.d1[a] + near.d2[b]).min(near.d2[a] + near.d1[b])
        };
        if edge.cost + delta + base > upper_bound + 1e-9 {
            dead_edges.push(edge.id);
        }
    }

    for v in doomed {
        graph.remove_node(v);
        killed += 1;
    }
    for e in dead_edges {
        if graph.is_edge_valid(e) {
            graph.remove_edge(e);
            killed += 1;
        }
    }
    killed
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
    fn deletes_a_vertex_that_no_cheap_tree_can_afford() {
        // 1(T) -1- 2 -1- 3(T), with 4 reachable only by two 50-cost edges.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 4, 50.0);
        g.add_edge(4, 3, 50.0);

        let inst = instance(&g, vec![1, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert!(bound_reductions(&mut rg, 2.0) >= 1);
        assert!(!rg.is_node_valid(4), "vertex 4 costs 100 to visit");
    }

    #[test]
    fn does_nothing_without_an_upper_bound() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        let inst = instance(&g, vec![1, 3]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        assert_eq!(bound_reductions(&mut rg, Cost::INFINITY), 0);
    }

    #[test]
    fn instance_bound_never_exceeds_the_optimum() {
        each_random_instance(|_n, g, rg, terminals, opt| {
            let lb = region_lower_bound(rg);
            assert!(lb <= opt + 1e-9, "region LB {lb} > optimum {opt}");
            let _ = (g, terminals);
        });
    }

    #[test]
    fn reductions_keep_every_tree_at_or_below_the_cutoff() {
        // The cutoff is the true optimum, so the optimum itself must survive.
        each_random_instance(|n, _g, rg, terminals, opt| {
            let mut work = rg.clone();
            bound_reductions(&mut work, opt);
            let after = brute(n, &live_edges(&work), terminals).unwrap_or(Cost::INFINITY);
            assert!(
                (after - opt).abs() < 1e-9,
                "bound reduction moved the optimum {opt} -> {after}"
            );
        });
    }

    fn live_edges(rg: &ReducibleGraph) -> Vec<(NodeId, NodeId, Cost)> {
        rg.edges
            .iter()
            .filter(|e| rg.is_edge_valid(e.id) && rg.is_node_valid(e.src) && rg.is_node_valid(e.dst))
            .map(|e| (e.src, e.dst, e.cost))
            .collect()
    }

    fn each_random_instance(
        mut check: impl FnMut(u32, &UndirectedGraph, &ReducibleGraph, &[NodeId], Cost),
    ) {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..400 {
            let n = 5 + (rng() % 4) as u32;
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
            let Some(opt) = brute(n, &edges, &terminals) else { continue };
            let inst = instance(&g, terminals.clone());
            let rg = ReducibleGraph::from_instance(&inst, &g);
            check(n, &g, &rg, &terminals, opt);
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
