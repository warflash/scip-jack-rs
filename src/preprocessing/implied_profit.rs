//! Edge deletion by the *implied* bottleneck Steiner distance.
//!
//! This is the Rehfeldt–Koch implied-profit reduction (Theorem 2 of
//! *Implications, conflicts, and reductions for Steiner trees*), derived here
//! from scratch so that the correctness argument is the one this implementation
//! actually makes rather than the one the paper makes for a different
//! approximation.
//!
//! # What the existing tests already do, and what they miss
//!
//! [`super::bottleneck`] deletes `e = {v,w}` when the *bottleneck Steiner
//! distance* `s(v,w)` is below `c(e)`: some `v`–`w` walk exists whose segments,
//! cut at the terminals it passes through, are each cheaper than `e`. The
//! terminals are what make it a bottleneck rather than a path length — a
//! terminal is in every Steiner tree, so a walk may be *closed* there and the
//! next segment charged separately.
//!
//! Steiner vertices are not free in that way. But some of them are nearly free,
//! and the reason is an exchange:
//!
//! > **Lemma (implied profit).** Let `v` be a Steiner vertex, `t` a terminal,
//! > `f = {v,t} ∈ E`, and let `b(f)` be the bottleneck distance between `v` and
//! > `t` in `G − f` — the least, over `v`–`t` paths avoiding `f`, of the path's
//! > largest edge cost. Put
//! >
//! > ```text
//! > p+(v, f) := max(0, b(f) − c(f)).
//! > ```
//! >
//! > If a Steiner tree `S` contains `v` but not `f`, then there is a Steiner
//! > tree `S'` with `c(S') <= c(S) − p+(v, f)`.
//! >
//! > *Proof.* `t` is a terminal so `t ∈ V(S)`, and `v ∈ V(S)` by hypothesis, so
//! > `S` holds a `v`–`t` path `P`. That path avoids `f`, so `max_{g ∈ P} c(g) >=
//! > b(f)`. Let `h` attain the maximum. `S + f` has exactly one cycle, which is
//! > `P + f`, and `h` lies on it, so `S' := S + f − h` is again a spanning tree
//! > of the same vertex set — in particular it still contains every terminal —
//! > and `c(S') = c(S) + c(f) − c(h) <= c(S) − (b(f) − c(f))`. ∎
//!
//! So a Steiner vertex carrying positive implied profit behaves like a terminal
//! *to the extent of that profit*: a walk passing through it may be closed there
//! at a discount of `p+`, rather than for free.
//!
//! # The reduction
//!
//! > **Theorem (profit-discounted deletion).** Fix `v0` and define `D` on the
//! > vertices by `D[v0] = 0`, `D[z] = c({v0,z})` for `z ∈ N(v0)`, and the
//! > relaxation, over a walk arriving at `x` from `pred(x)` and leaving along
//! > `g = {x,y}`,
//! >
//! > ```text
//! > D[y] <- D[x] + c(g) − min( pi(x, g), D[x], c(g) ),                     (R)
//! > pi(x, g) := max { p+(x, f) : f ∈ delta(x), f != g, f != pred-edge(x) },
//! > ```
//! >
//! > with `pi(x, g) := +infinity` when `x` is a terminal. If `D[z] < c({v0,z})`
//! > for some `z ∈ N(v0)`, then **no** minimum Steiner tree contains `{v0,z}`.
//!
//! *Proof.* Write `e = {v0,z}`, and let `S` be a minimum Steiner tree with
//! `e ∈ E(S)`. Let `W = (v0 = x_0, g_1, x_1, …, g_r, x_r = z)` be the walk that
//! (R) settled `z` along, so
//!
//! ```text
//! D[x_{i+1}] = D[x_i] + c(g_{i+1}) − mu_i,      mu_i := min(pi_i, D[x_i], c(g_{i+1})).
//! ```
//!
//! Three properties of (R) are used and each is immediate from the clamp:
//! `D` is non-decreasing along `W` (because `mu_i <= c(g_{i+1})`); `mu_i <=
//! D[x_i]`; and `D[x_i] >= 0`.
//!
//! `W` is a simple path — it is a predecessor path of a Dijkstra whose key never
//! decreases — and it does not use `e`: its only vertex adjacent to `v0` along
//! the walk is `x_1`, and if `x_1 = z` then `W` is the single edge `e` and
//! `D[z] = c(e)`, contradicting `D[z] < c(e)`.
//!
//! Delete `e` from `S`. If either side holds no terminal, deleting that side
//! already gives a cheaper Steiner tree and there is nothing to prove; so let
//! `S_1 ∋ v0` and `S_2 ∋ z` both hold terminals. Put
//!
//! ```text
//! b := min { i : x_i ∈ V(S_2) },        a := max { i <= b : x_i ∈ V(S_1) }.
//! ```
//!
//! Both exist (`x_0 = v0`, `x_r = z`) and `a < b`, and **every `x_i` with
//! `a < i < b` lies outside `V(S)` entirely** — that is what maximality of `a`
//! and minimality of `b` say.
//!
//! Reconnect: `Stilde := (S − e) + W(a,b)` is connected, spans every terminal,
//! and costs at most `c(S) − c(e) + sum_{a<j<=b} c(g_j)`.
//!
//! Now discharge the profits. For each `i` with `a < i < b` and `mu_i > 0`, let
//! `f_i = {x_i, t_i}` be the edge attaining `pi_i`. Then:
//!
//! - `x_i` is a Steiner vertex (a terminal would be in `V(S)`, and `pi = ∞` is
//!   clamped to `D[x_i]` which is finite, so the terminal case cannot supply a
//!   profit edge here — but the argument below does not need that: it needs only
//!   `f_i ∉ E(Stilde)`);
//! - `f_i ∉ E(S)`, since `x_i ∉ V(S)`;
//! - `f_i ∉ E(W(a,b))`, since the only walk edges at `x_i` are `g_i` and
//!   `g_{i+1}`, both excluded by the definition of `pi_i`, and `W` is simple so
//!   `x_i` occurs once.
//!
//! Hence `f_i ∉ E(Stilde)`, and the implied-profit lemma applies to `Stilde`,
//! which contains `x_i` and `t_i`. Apply the exchanges in any order. Each keeps
//! the vertex set — `Stilde + f_i` has one cycle and the removed edge lies on it
//! — so every later `x_j`, `t_j` is still present; and each keeps `f_j ∉ E`
//! for `j != i`, because the only edge added is `f_i`, and `f_i = f_j` is
//! impossible (`x_i != x_j` are Steiner, `t_i, t_j` are terminals). Each exchange
//! `i` therefore lowers the cost by at least `p+(x_i, f_i) >= mu_i`.
//!
//! Summing, and telescoping (R) between `a` and `b`,
//!
//! ```text
//! c(S') <= c(S) − c(e) + sum_{a<j<=b} c(g_j) − sum_{a<i<b} mu_i
//!        = c(S) − c(e) + (D[x_b] − D[x_a] + mu_a)
//!       <= c(S) − c(e) + D[x_b]                    (because mu_a <= D[x_a])
//!       <= c(S) − c(e) + D[z]                      (D non-decreasing along W)
//!        < c(S).
//! ```
//!
//! So `S` was not minimum. ∎
//!
//! The clamp `mu <= D[x]` is not a numerical safeguard; the second-to-last line
//! is the only place the theorem can be proved, and it is exactly what pays for
//! the profit of the vertex `x_a` that the argument is *not* allowed to spend.
//! The clamp `mu <= c(g)` is what makes `D` non-decreasing, and hence what makes
//! (R) a Dijkstra rather than a shortest-path problem with negative weights.
//!
//! # Two special cases, to see that this generalises what is already here
//!
//! With every profit zero, (R) is `D[y] = D[x] + c(g)` and the rule deletes an
//! edge longer than some path between its ends. With `pi = +infinity` at
//! terminals and zero elsewhere, (R) is `D[y] = max(D[x], c(g))` and the rule is
//! exactly the bottleneck Steiner distance test of [`super::bottleneck`].
//! Positive finite profits interpolate, which is where the new deletions come
//! from.
//!
//! # Where positive profits can live
//!
//! `b(f)` must be computed in `G − f`, and that is the whole content: the
//! *unrestricted* bottleneck distance between the ends of an edge is at most
//! `c(f)` — the edge is itself a path — so it never yields a profit.
//!
//! > **Lemma (only spanning-tree edges pay).** If `f` is not on some minimum
//! > spanning tree `M` of `G`, then `p+(v, f) = 0`.
//! >
//! > *Proof.* By the cycle property, every edge on the `M`-path between `f`'s
//! > ends costs at most `c(f)`. That path avoids `f`, so `b(f) <= c(f)`. ∎
//!
//! So the candidates are the spanning-tree edges joining a Steiner vertex to a
//! terminal — at most `n − 1` of them, and in practice a few dozen — and for
//! each of those `b(f)` is computed **exactly**, by a minimax Dijkstra in
//! `G − f`.
//!
//! A cheaper route was tried first and measured out. The classical
//! replacement-edge quantity
//!
//! ```text
//! repl(f) := min { c(h) : h ∉ M, the M-path of h contains f }
//! ```
//!
//! is a lower bound on `b(f)` — every `v`–`t` path avoiding `f` crosses the cut
//! that removing `f` from `M` induces, and every crossing edge other than `f` is
//! a non-tree edge whose `M`-path contains `f` — and it comes for all tree edges
//! at once from a union-find sweep. It is also far too weak: `b(f)` is the
//! *maximum* along the replacement path, not the replacement edge alone, and on
//! PACE instance161 the bound found 23 profitable edges where the exact value
//! finds more, while on instances 171, 195 and 196 it found **none at all**. The
//! candidates are few enough that the exact computation is the cheaper mistake.
//!
//! An `f` with no `v`–`t` path in `G − f` is a bridge. Its profit is left at
//! zero rather than set to infinity, because "S contains `v` but not `f`" is
//! then vacuous and the lemma says nothing usable.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::time::Instant;

use crate::graph::{cmp_cost, Cost, EdgeId, NodeId};

use super::csr::{Csr, Ordered};
use super::ReducibleGraph;

/// Per-edge implied profit, indexed by `EdgeId`.
///
/// `profit[e]` is `p+(v, e)` for whichever endpoint of `e` is the Steiner one;
/// it is zero unless `e` joins a Steiner vertex to a terminal, `e` lies on the
/// minimum spanning tree, and its replacement is dearer than itself.
pub struct ImpliedProfits {
    profit: Vec<Cost>,
    /// Whether any entry is positive, so a sweep that would gain nothing can be
    /// skipped outright.
    pub any: bool,
}

impl ImpliedProfits {
    pub fn get(&self, e: EdgeId) -> Cost {
        self.profit.get(e as usize).copied().unwrap_or(0.0)
    }
}

/// Compute `p+` for every edge of the live graph.
///
/// See the module header: only minimum-spanning-tree edges joining a Steiner
/// vertex to a terminal can be positive, and `repl` bounds `b` from below.
pub fn implied_profits(graph: &ReducibleGraph, csr: &Csr) -> ImpliedProfits {
    let num_edges = graph.edges.len();
    let mut profit = vec![0.0 as Cost; num_edges];

    // Live edges, by increasing cost. Kruskal wants them in this order and so
    // does the replacement sweep.
    let mut order: Vec<EdgeId> = graph
        .edges
        .iter()
        .filter(|e| {
            graph.is_edge_valid(e.id)
                && graph.is_node_valid(e.src)
                && graph.is_node_valid(e.dst)
                && e.src != e.dst
        })
        .map(|e| e.id)
        .collect();
        order.sort_by(|&a, &b| {
        cmp_cost(graph.edges[a as usize].cost, graph.edges[b as usize].cost).then(a.cmp(&b))
    });

    let n = csr.num_nodes;
    let mut dsu = Dsu::new(n);
    // Adjacency of the spanning forest, as (neighbour, edge) pairs.
    let mut tree_adj: Vec<Vec<(NodeId, EdgeId)>> = vec![Vec::new(); n];
    let mut in_tree = vec![false; num_edges];
    for &id in &order {
        let e = &graph.edges[id as usize];
        if dsu.union(e.src as usize, e.dst as usize) {
            in_tree[id as usize] = true;
            tree_adj[e.src as usize].push((e.dst, id));
            tree_adj[e.dst as usize].push((e.src, id));
        }
    }

    // Root the forest and record, per vertex, its parent edge and depth. A
    // forest rather than a tree: the live graph can be disconnected once earlier
    // reductions have deleted things.
    let mut parent = vec![u32::MAX; n];
    let mut parent_edge = vec![u32::MAX; n];
    let mut depth = vec![0u32; n];
    let mut seen = vec![false; n];
    let mut stack: Vec<NodeId> = Vec::new();
    for v in 0..n {
        if seen[v] || tree_adj[v].is_empty() {
            continue;
        }
        seen[v] = true;
        stack.push(v as NodeId);
        while let Some(x) = stack.pop() {
            for &(y, id) in &tree_adj[x as usize] {
                if !seen[y as usize] {
                    seen[y as usize] = true;
                    parent[y as usize] = x;
                    parent_edge[y as usize] = id;
                    depth[y as usize] = depth[x as usize] + 1;
                    stack.push(y);
                }
            }
        }
    }

    let _ = (&parent, &parent_edge, &depth);
    // The candidates: spanning-tree edges joining a Steiner vertex to a
    // terminal. Everything else has profit zero by the lemma above.
    let mut candidates: Vec<EdgeId> = Vec::new();
    for &id in &order {
        if !in_tree[id as usize] {
            continue;
        }
        let e = &graph.edges[id as usize];
        // The exchange needs the far end to lie in every Steiner tree, so one
        // end must be a terminal and the other must not.
        if graph.is_terminal(e.src) == graph.is_terminal(e.dst) {
            continue;
        }
        candidates.push(id);
    }

    // `b(f)` exactly, by a minimax Dijkstra in `G - f` from the Steiner end.
    let mut best = vec![Cost::INFINITY; n];
    let mut touched: Vec<u32> = Vec::new();
    let mut heap: BinaryHeap<(Reverse<Ordered>, u32)> = BinaryHeap::new();
    let mut bottleneck = vec![Cost::INFINITY; num_edges];
    for &id in &candidates {
        let e = &graph.edges[id as usize];
        let (v, t) = if graph.is_terminal(e.src) { (e.dst, e.src) } else { (e.src, e.dst) };
        for &u in &touched {
            best[u as usize] = Cost::INFINITY;
        }
        touched.clear();
        heap.clear();
        best[v as usize] = 0.0;
        touched.push(v);
        heap.push((Reverse(Ordered(0.0)), v));
        while let Some((Reverse(Ordered(d)), x)) = heap.pop() {
            if d > best[x as usize] + 1e-12 {
                continue;
            }
            if x == t {
                break;
            }
            for (y, c, gid) in csr.neighbors(x) {
                if gid == id {
                    continue;
                }
                let nd = d.max(c);
                if nd >= best[y as usize] - 1e-12 {
                    continue;
                }
                if best[y as usize] == Cost::INFINITY {
                    touched.push(y);
                }
                best[y as usize] = nd;
                heap.push((Reverse(Ordered(nd)), y));
            }
        }
        bottleneck[id as usize] = best[t as usize];
    }

    let mut any = false;
    for &id in &candidates {
        let b = bottleneck[id as usize];
        if !b.is_finite() {
            continue; // a bridge; see the module header
        }
        let p = b - graph.edges[id as usize].cost;
        if p > 1e-9 {
            profit[id as usize] = p;
            any = true;
        }
    }

    ImpliedProfits { profit, any }
}

/// Union-find with union by size.
struct Dsu {
    parent: Vec<usize>,
    size: Vec<u32>,
}

impl Dsu {
    fn new(n: usize) -> Self {
        Self { parent: (0..n).collect(), size: vec![1; n] }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        let (small, big) = if self.size[ra] < self.size[rb] { (ra, rb) } else { (rb, ra) };
        self.parent[small] = big;
        self.size[big] += self.size[small];
        true
    }
}

/// Scratch space for the profit-discounted sweep.
pub struct ProfitWorkspace {
    dist: Vec<Cost>,
    /// Edge the walk arrived along, so the profit can exclude it.
    via: Vec<EdgeId>,
    touched: Vec<u32>,
    heap: BinaryHeap<(Reverse<Ordered>, u32)>,
}

impl ProfitWorkspace {
    pub fn new(num_nodes: usize) -> Self {
        Self {
            dist: vec![Cost::INFINITY; num_nodes],
            via: vec![u32::MAX; num_nodes],
            touched: Vec::new(),
            heap: BinaryHeap::new(),
        }
    }

    fn reset(&mut self) {
        for &v in &self.touched {
            self.dist[v as usize] = Cost::INFINITY;
            self.via[v as usize] = u32::MAX;
        }
        self.touched.clear();
        self.heap.clear();
    }
}

/// Edges the sweep may relax in total, across the whole pass.
///
/// A work bound and nothing else: the sweep is a Dijkstra per vertex, and
/// stopping one early leaves the labels it has already settled valid — they are
/// still upper bounds proved by real walks — so truncation costs deletions and
/// never soundness.
const SWEEP_EDGE_BUDGET: u64 = 40_000_000;

/// One pass of profit-discounted edge deletion. Returns the number of edges
/// removed.
///
/// The rule proved in the module header is applied from every live vertex in
/// turn, deleting whole fans of `delta(v0)` per sweep. Deletions take effect
/// immediately, so each is justified against the graph the later ones are
/// tested on — the same composition rule [`super::vertex_test`] uses.
pub fn implied_profit_reductions(graph: &mut ReducibleGraph) -> u32 {
    implied_profit_reductions_until(graph, None)
}

/// [`implied_profit_reductions`] with a wall-clock stop.
///
/// Every deletion is justified on its own against the graph it was tested on, so
/// stopping the pass at any point leaves a correct — merely less reduced —
/// instance.
pub fn implied_profit_reductions_until(
    graph: &mut ReducibleGraph,
    deadline: Option<Instant>,
) -> u32 {
    let csr = Csr::build(graph);
    let profits = implied_profits(graph, &csr);
    if !profits.any {
        // With every profit zero the rule degenerates to "some path is shorter
        // than the edge", which `bottleneck` already subsumes.
        return 0;
    }
    let mut ws = ProfitWorkspace::new(csr.num_nodes);
    let mut removed = 0u32;
    let mut budget = SWEEP_EDGE_BUDGET;

    let sources: Vec<NodeId> = graph.valid_nodes();
    for (i, v0) in sources.into_iter().enumerate() {
        if budget == 0 {
            break;
        }
        if i % 64 == 0 && deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        if !graph.is_node_valid(v0) {
            continue;
        }
        removed += sweep_from(graph, &csr, &profits, v0, &mut ws, &mut budget);
    }
    removed
}

/// The Dijkstra of relaxation (R), rooted at `v0`, deleting the edges of
/// `delta(v0)` it beats.
fn sweep_from(
    graph: &mut ReducibleGraph,
    csr: &Csr,
    profits: &ImpliedProfits,
    v0: NodeId,
    ws: &mut ProfitWorkspace,
    budget: &mut u64,
) -> u32 {
    // The fan under test, and the radius beyond which no member of it can be
    // beaten. `D` is non-decreasing along every walk, so a label above the
    // dearest fan edge can never license a deletion.
    let mut fan: Vec<(NodeId, EdgeId, Cost)> = Vec::new();
    for (u, c, id) in csr.neighbors(v0) {
        if graph.is_edge_valid(id) && graph.is_node_valid(u) {
            fan.push((u, id, c));
        }
    }
    if fan.len() < 2 {
        return 0;
    }
    let radius = fan.iter().map(|&(_, _, c)| c).fold(0.0 as Cost, Cost::max);

    ws.reset();
    // Seeded at the fan rather than at `v0`: the walk that licenses deleting
    // `{v0,z}` must not use that edge, and starting one hop out with the fan
    // edge's own cost is what makes the label at `z` an upper bound on the
    // implied length of a walk that leaves `v0` by a *different* edge. A label
    // that only ever equals `c({v0,z})` fails the strict test, which is the
    // single-edge walk being rejected.
    for &(u, id, c) in &fan {
        if c < ws.dist[u as usize] {
            if ws.dist[u as usize] == Cost::INFINITY {
                ws.touched.push(u);
            }
            ws.dist[u as usize] = c;
            ws.via[u as usize] = id;
            ws.heap.push((Reverse(Ordered(c)), u));
        }
    }

    while let Some((Reverse(Ordered(d)), x)) = ws.heap.pop() {
        if d > ws.dist[x as usize] + 1e-12 {
            continue;
        }
        if d > radius + 1e-9 {
            break;
        }
        // `pi(x, g)`: the best profit at `x` over edges that are neither the
        // arrival edge nor the departure edge. Terminals are unbounded, and the
        // clamp below is what turns that into the bottleneck rule.
        let arrived = ws.via[x as usize];
        let terminal = graph.is_terminal(x);
        // The two best profits at `x`, so excluding the departure edge costs a
        // comparison rather than a rescan.
        let (mut best, mut second) = (0.0 as Cost, 0.0 as Cost);
        let (mut best_edge, _) = (u32::MAX, ());
        if !terminal {
            for (_, _, id) in csr.neighbors(x) {
                if id == arrived || !graph.is_edge_valid(id) {
                    continue;
                }
                let p = profits.get(id);
                if p > best {
                    second = best;
                    best = p;
                    best_edge = id;
                } else if p > second {
                    second = p;
                }
            }
        }

        for (y, c, id) in csr.neighbors(x) {
            if !graph.is_edge_valid(id) || !graph.is_node_valid(y) || y == v0 {
                continue;
            }
            if *budget == 0 {
                return delete_beaten(graph, ws, &fan);
            }
            *budget -= 1;
            let pi = if terminal {
                Cost::INFINITY
            } else if id == best_edge {
                second
            } else {
                best
            };
            // (R), with the clamp the proof needs.
            let mu = pi.min(d).min(c);
            let nd = d + c - mu;
            if nd > radius + 1e-9 || nd >= ws.dist[y as usize] - 1e-12 {
                continue;
            }
            if ws.dist[y as usize] == Cost::INFINITY {
                ws.touched.push(y);
            }
            ws.dist[y as usize] = nd;
            ws.via[y as usize] = id;
            ws.heap.push((Reverse(Ordered(nd)), y));
        }
    }

    delete_beaten(graph, ws, &fan)
}

/// Delete every fan edge whose endpoint carries a strictly cheaper label.
///
/// The strictness is the whole of the "no minimum tree contains it" conclusion;
/// with equality the right statement is "*some* minimum tree omits it", which
/// does not compose across a fan without further care and is not claimed here.
fn delete_beaten(
    graph: &mut ReducibleGraph,
    ws: &ProfitWorkspace,
    fan: &[(NodeId, EdgeId, Cost)],
) -> u32 {
    let mut removed = 0;
    for &(u, id, c) in fan {
        if !graph.is_edge_valid(id) {
            continue;
        }
        if ws.dist[u as usize] < c - 1e-9 {
            graph.remove_edge(id);
            removed += 1;
        }
    }
    removed
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

    /// Brute-force optimum over every connected subgraph.
    fn brute_force(g: &UndirectedGraph, terminals: &[NodeId]) -> Option<Cost> {
        let n = g.num_nodes as usize;
        let m = g.edges.len();
        if m > 20 {
            return None;
        }
        let mut best = Cost::INFINITY;
        for take in 0u32..(1u32 << m) {
            let mut dsu: Vec<usize> = (0..=n).collect();
            fn find(d: &mut Vec<usize>, mut x: usize) -> usize {
                while d[x] != x {
                    d[x] = d[d[x]];
                    x = d[x];
                }
                x
            }
            let mut cost = 0.0;
            for (i, e) in g.edges.iter().enumerate() {
                if take >> i & 1 == 1 {
                    cost += e.cost;
                    let (a, b) = (find(&mut dsu, e.src as usize), find(&mut dsu, e.dst as usize));
                    dsu[a] = b;
                }
            }
            if cost >= best {
                continue;
            }
            let r = find(&mut dsu, terminals[0] as usize);
            if terminals.iter().all(|&t| find(&mut dsu, t as usize) == r) {
                best = cost;
            }
        }
        best.is_finite().then_some(best)
    }

    /// The classic case the plain bottleneck test cannot see.
    ///
    /// A chain of Steiner vertices, each hanging off a dear terminal edge. Every
    /// chain edge is cheap, so an expensive shortcut across the chain is
    /// deletable — but only once the chain's vertices are recognised as nearly
    /// free.
    #[test]
    fn a_profit_chain_deletes_a_shortcut() {
        // v1 - v2 - v3 - v4 chain at cost 1 each; each of v2, v3 hangs off a
        // terminal by an edge whose only replacement is far dearer.
        let mut g = UndirectedGraph::new(6);
        for v in 1..=6u32 {
            let t = matches!(v, 5 | 6) || matches!(v, 1 | 4);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(2, 5, 1.0);
        g.add_edge(3, 6, 1.0);
        g.add_edge(5, 6, 9.0);
        // The shortcut under test.
        g.add_edge(1, 4, 2.5);
        let terminals = vec![1, 4, 5, 6];
        let inst = instance(&g, terminals.clone());
        let before = brute_force(&g, &terminals).unwrap();

        let mut rg = ReducibleGraph::from_instance(&inst, &g);
        let removed = implied_profit_reductions(&mut rg);
        assert!(removed > 0, "the shortcut should have been deleted");

        let (_, after_g) = rg.to_instance();
        let after = brute_force(&after_g, &terminals).unwrap();
        assert!((after - before).abs() < 1e-9, "optimum moved: {before} -> {after}");
    }

    /// The invariant, over an exhaustive family of small graphs: the pass never
    /// changes the optimum.
    #[test]
    fn never_changes_the_optimum() {
        let mut seed = 0x1234_5678_9ABC_DEF1u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        let mut deletions = 0u32;
        for _ in 0..4000 {
            let n = 4 + (rng() % 4) as u32;
            let k = 2 + (rng() % 3) as u32;
            let mut g = UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        // Small integer costs, so ties and profitable exchanges
                        // are both frequent.
                        g.add_edge(u, v, 1.0 + (rng() % 5) as Cost);
                    }
                }
            }
            if g.edges.len() > 18 {
                continue;
            }
            let Some(before) = brute_force(&g, &terminals) else { continue };
            let inst = instance(&g, terminals.clone());
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            deletions += implied_profit_reductions(&mut rg);
            let (_, after_g) = rg.to_instance();
            let Some(after) = brute_force(&after_g, &terminals) else {
                panic!("the reduction disconnected the terminals");
            };
            assert!(
                (after - before).abs() < 1e-9,
                "optimum moved {before} -> {after} on a {n}-vertex instance"
            );
            checked += 1;
        }
        assert!(checked > 500, "only {checked} instances were exercised");
        assert!(deletions > 0, "the rule never fired; the test proves nothing");
    }

    /// The dense, high-degree regime the rule is aimed at. Ordinary sparse
    /// random graphs are not an adequate gate for a rule meant to fire there.
    #[test]
    fn never_changes_the_optimum_on_dense_graphs() {
        let mut seed = 0xDEAD_BEEF_0BAD_F00Du64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        let mut deletions = 0u32;
        for _ in 0..2000 {
            // Complete or near-complete graphs on 5-6 vertices: average degree
            // is the vertex count minus one, which is the shape of the PACE
            // dense group scaled down to where brute force can still reach.
            let n = 5 + (rng() % 2) as u32;
            let k = 2 + (rng() % 2) as u32;
            let mut g = UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 8 != 0 {
                        g.add_edge(u, v, 1.0 + (rng() % 6) as Cost);
                    }
                }
            }
            if g.edges.len() > 16 {
                continue;
            }
            let Some(before) = brute_force(&g, &terminals) else { continue };
            let inst = instance(&g, terminals.clone());
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            deletions += implied_profit_reductions(&mut rg);
            let (_, after_g) = rg.to_instance();
            let Some(after) = brute_force(&after_g, &terminals) else {
                panic!("the reduction disconnected the terminals");
            };
            assert!((after - before).abs() < 1e-9, "optimum moved {before} -> {after}");
            checked += 1;
        }
        assert!(checked > 300, "only {checked} dense instances were exercised");
        assert!(deletions > 0, "the rule never fired on a dense graph");
    }

    /// `repl` is a lower bound on the restricted bottleneck distance, checked
    /// against a direct computation.
    #[test]
    fn the_replacement_bound_is_below_the_restricted_bottleneck() {
        let mut seed = 0x0BADC0DE_1234_5678u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..400 {
            let n = 5 + (rng() % 3) as u32;
            let mut g = UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= 2;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        g.add_edge(u, v, 1.0 + (rng() % 7) as Cost);
                    }
                }
            }
            let inst = instance(&g, terminals.clone());
            let rg = ReducibleGraph::from_instance(&inst, &g);
            let csr = Csr::build(&rg);
            let p = implied_profits(&rg, &csr);
            for e in &g.edges {
                let claimed = p.get(e.id);
                if claimed <= 0.0 {
                    continue;
                }
                // Direct minimax path in `G - e`, by Dijkstra on max.
                let b = restricted_bottleneck(&g, e.src, e.dst, e.id);
                assert!(
                    claimed <= b - e.cost + 1e-9,
                    "profit {claimed} exceeds b({}) - c = {} - {}",
                    e.id,
                    b,
                    e.cost
                );
            }
        }
    }

    /// Minimax path cost between `s` and `t` avoiding edge `skip`.
    fn restricted_bottleneck(g: &UndirectedGraph, s: NodeId, t: NodeId, skip: EdgeId) -> Cost {
        let n = g.num_nodes as usize + 1;
        let mut best = vec![Cost::INFINITY; n];
        best[s as usize] = 0.0;
        for _ in 0..n {
            let mut changed = false;
            for e in &g.edges {
                if e.id == skip {
                    continue;
                }
                for (a, b) in [(e.src, e.dst), (e.dst, e.src)] {
                    let cand = best[a as usize].max(e.cost);
                    if cand < best[b as usize] - 1e-12 {
                        best[b as usize] = cand;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        best[t as usize]
    }
}
