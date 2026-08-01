//! Activation-rank inequalities, separated exactly by one min cut per anchor.
//!
//! # The family
//!
//! Write `x_e = y_uv + y_vu` for whether edge `e` is used and `s_v` for whether
//! vertex `v` is active — both are already columns of the model. For a vertex set
//! `U` and an *anchor* `a` in `U`,
//!
//! ```text
//! x(E(U)) + s_a <= s(U),        E(U) = edges with both ends in U,
//!                               s(U) = sum of s_v over U.        (AR)
//! ```
//!
//! ## Validity
//!
//! Take an integral point: a tree `T` with vertex set `W`, and `s_v = 1` exactly
//! on `W`. The edges of `T` inside `U` form a forest on `U ∩ W`; if it has `p`
//! components it has `|U ∩ W| - p = s(U) - p` edges.
//!
//! - If `s_a = 1` then `a` lies in `U ∩ W`, so that set is nonempty, `p >= 1`,
//!   and `x(E(U)) <= s(U) - 1`.
//! - If `s_a = 0` the claim is only `x(E(U)) <= s(U)`, which holds trivially when
//!   `U ∩ W` is empty (both sides are zero) and follows from `p >= 1` otherwise.
//!
//! Every integral point satisfies (AR), so every point of the convex hull does. ∎
//!
//! ## What it generalises
//!
//! The resident tree-cardinality row is exactly (AR) at `U = V` anchored at the
//! root, where `s_root = 1`. The cycle inequalities `x(E(C)) <= |C| - 1` are the
//! special case `U = V(C)` with every `s_v` relaxed to its upper bound of one;
//! (AR) charges the actual activation instead, so it dominates them whenever the
//! cycle's vertices are not fully active — which is the normal state of a
//! fractional point. And unlike the cycle rows, which are found by bounded
//! enumeration and are therefore an incomplete family, (AR) is separated
//! **exactly**.
//!
//! # Exact separation
//!
//! Fix the anchor `a`. Put
//!
//! ```text
//! d(v) = sum of x_e over edges at v,   w_v = d(v)/2 - s_v,   c_e = x_e/2.
//! ```
//!
//! Since `sum_{v in U} d(v) = 2 x(E(U)) + x(delta(U))`,
//!
//! ```text
//! x(E(U)) - s(U) = sum_{v in U} w_v - sum_{e in delta(U)} c_e =: g(U),
//! ```
//!
//! so the most violated (AR) row with anchor `a` maximises `g(U) + s_a` over the
//! sets `U` containing `a`. Maximising a modular function minus a cut is a min
//! cut. Build an auxiliary network on `V + {S, T}`:
//!
//! ```text
//! w_v > 0:  S -> v   with capacity  w_v
//! w_v < 0:  v -> T   with capacity -w_v
//! edge e:   u -> v and v -> u, each with capacity c_e
//! anchor:   S -> a   with infinite capacity
//! ```
//!
//! For a cut whose source side is `U + {S}`, the cut value is
//!
//! ```text
//! sum_{v not in U, w_v > 0} w_v + sum_{v in U, w_v < 0} (-w_v)
//!   + sum_{e in delta(U)} c_e
//!   = C - g(U),          C = sum of the positive w_v.
//! ```
//!
//! So `max_U g(U) = C - mincut`, attained on the source side of the min cut, and
//! the maximum violation with this anchor is `C - mincut + s_a`. One max flow per
//! anchor gives the exactly most violated row for that anchor; there is no
//! enumeration and no truncation anywhere in the argument.
//!
//! The anchor constraint is not decoration. Without it the empty set is feasible
//! with `g = 0`, and `0 + s_a` would look like a violation of a row that does not
//! exist. With it, `U = {a}` gives `g = -s_a` and violation exactly zero, which is
//! the correct floor.
//!
//! # Which anchors
//!
//! Violation is `g(U) + s_a`, so anchors with `s_a = 1` — the terminals and the
//! root, whose columns are fixed at one — dominate. Steiner anchors are legal and
//! would each cost another max flow for a strictly smaller violation, so this
//! separator anchors on terminals only.

use crate::graph::{ArcId, DirectedGraph, NodeId};

/// A violated activation-rank row, kept as the set that proves it.
#[derive(Debug, Clone)]
pub struct ArCut {
    /// The vertices of `U`.
    pub vertices: Vec<NodeId>,
    /// The anchor, an element of `vertices`.
    pub anchor: NodeId,
    pub violation: f64,
}

pub struct ActivationRankSeparator<'a> {
    graph: &'a DirectedGraph,
    /// Undirected edges as `(u, v, forward arc, reverse arc)`.
    edges: Vec<(NodeId, NodeId, ArcId, ArcId)>,
    /// Dense index per vertex id, or `u32::MAX`.
    index: Vec<u32>,
    /// Vertex id per dense index.
    vertex: Vec<NodeId>,
    pub violation_tolerance: f64,
}

impl<'a> ActivationRankSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph) -> Self {
        let max_id = graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let mut index = vec![u32::MAX; max_id + 1];
        let mut vertex = Vec::with_capacity(graph.nodes.len());
        for node in &graph.nodes {
            index[node.id as usize] = vertex.len() as u32;
            vertex.push(node.id);
        }

        // The arc list pairs each edge as `2p` and `2p + 1`; rebuilding the
        // pairing from tails and heads would be quadratic.
        let mut edges = Vec::with_capacity(graph.arcs.len() / 2);
        for p in 0..graph.arcs.len() / 2 {
            let f = &graph.arcs[2 * p];
            let r = &graph.arcs[2 * p + 1];
            debug_assert_eq!((f.tail, f.head), (r.head, r.tail));
            if f.tail != f.head {
                edges.push((f.tail, f.head, f.id, r.id));
            }
        }

        Self { graph, edges, index, vertex, violation_tolerance: 1e-4 }
    }

    /// Separate (AR) over the given anchors.
    ///
    /// `y` is the arc part of the LP solution and `s` is indexed by vertex id.
    pub fn find_violated_cuts(
        &mut self,
        y: &[f64],
        s: &[f64],
        anchors: &[NodeId],
    ) -> Vec<ArCut> {
        let n = self.vertex.len();
        if n == 0 || self.edges.is_empty() {
            return Vec::new();
        }

        // x_e, then the vertex weights of the reduction.
        let x: Vec<f64> = self
            .edges
            .iter()
            .map(|&(_, _, f, r)| {
                y.get(f as usize).copied().unwrap_or(0.0) + y.get(r as usize).copied().unwrap_or(0.0)
            })
            .collect();

        let mut degree = vec![0.0f64; n];
        for (i, &(u, v, _, _)) in self.edges.iter().enumerate() {
            degree[self.index[u as usize] as usize] += x[i];
            degree[self.index[v as usize] as usize] += x[i];
        }
        let w: Vec<f64> = (0..n)
            .map(|i| degree[i] / 2.0 - s.get(self.vertex[i] as usize).copied().unwrap_or(0.0))
            .collect();
        let positive: f64 = w.iter().filter(|&&v| v > 0.0).sum();

        let mut out = Vec::new();
        for &a in anchors {
            let Some(&ai) = self.index.get(a as usize) else { continue };
            if ai == u32::MAX {
                continue;
            }
            let s_a = s.get(a as usize).copied().unwrap_or(0.0);
            let (flow, source_side) = self.min_cut(&x, &w, ai as usize);
            let violation = positive - flow + s_a;
            if violation <= self.violation_tolerance {
                continue;
            }
            let vertices: Vec<NodeId> =
                (0..n).filter(|&i| source_side[i]).map(|i| self.vertex[i]).collect();
            // `U = {a}` has violation zero, so a positive violation forces a
            // larger set; this only guards against a degenerate flow result.
            if vertices.len() < 2 {
                continue;
            }
            out.push(ArCut { vertices, anchor: a, violation });
        }
        out.sort_by(|p, q| q.violation.partial_cmp(&p.violation).unwrap_or(std::cmp::Ordering::Equal));
        out
    }

    /// The row implied by a cut, as `(column, coefficient)` pairs with the given
    /// upper bound, using the LP's activation columns.
    ///
    /// Returns `None` when some vertex of `U` has no activation column.
    pub fn row(&self, cut: &ArCut, node_col: &[Option<u32>]) -> Option<(Vec<(u32, f64)>, f64)> {
        let mut inside = vec![false; self.index.len()];
        for &v in &cut.vertices {
            inside[v as usize] = true;
        }
        let mut entries: Vec<(u32, f64)> = Vec::new();
        for &(u, v, f, r) in &self.edges {
            if inside[u as usize] && inside[v as usize] {
                entries.push((f, 1.0));
                entries.push((r, 1.0));
            }
        }
        if entries.is_empty() {
            return None;
        }
        for &v in &cut.vertices {
            let col = *node_col.get(v as usize)?;
            let col = col?;
            let coeff = if v == cut.anchor { -1.0 + 1.0 } else { -1.0 };
            // The anchor appears on both sides: `+ s_a` on the left and `- s_a`
            // from `s(U)` on the right, which cancel.
            if coeff != 0.0 {
                entries.push((col, coeff));
            }
        }
        Some((entries, 0.0))
    }

    /// Min cut of the auxiliary network with `anchor` forced to the source side.
    /// Returns the flow value and the source side, as dense vertex flags.
    fn min_cut(&self, x: &[f64], w: &[f64], anchor: usize) -> (f64, Vec<bool>) {
        let n = self.vertex.len();
        let source = n;
        let sink = n + 1;
        let mut net = Dinic::new(n + 2);

        // An "infinite" capacity that cannot be part of a finite min cut.
        let big = w.iter().map(|v| v.abs()).sum::<f64>() + x.iter().sum::<f64>() + 1.0;

        for (i, &wi) in w.iter().enumerate() {
            if wi > 0.0 {
                net.add(source, i, wi);
            } else if wi < 0.0 {
                net.add(i, sink, -wi);
            }
        }
        for (i, &(u, v, _, _)) in self.edges.iter().enumerate() {
            let c = x[i] / 2.0;
            if c > 0.0 {
                let (a, b) = (self.index[u as usize] as usize, self.index[v as usize] as usize);
                // One undirected pair: capacity `c` in each direction.
                net.add_undirected(a, b, c);
            }
        }
        net.add(source, anchor, big);

        let flow = net.max_flow(source, sink);
        let reach = net.source_side(source);
        (flow, reach[..n].to_vec())
    }

    pub fn graph(&self) -> &DirectedGraph {
        self.graph
    }
}

/// Dinic max flow on a small auxiliary network with real capacities.
struct Dinic {
    head: Vec<usize>,
    cap: Vec<f64>,
    next: Vec<Vec<usize>>,
    level: Vec<i32>,
    iter: Vec<usize>,
}

impl Dinic {
    fn new(n: usize) -> Self {
        Self {
            head: Vec::new(),
            cap: Vec::new(),
            next: vec![Vec::new(); n],
            level: vec![-1; n],
            iter: vec![0; n],
        }
    }

    fn add(&mut self, u: usize, v: usize, c: f64) {
        self.next[u].push(self.head.len());
        self.head.push(v);
        self.cap.push(c);
        self.next[v].push(self.head.len());
        self.head.push(u);
        self.cap.push(0.0);
    }

    fn add_undirected(&mut self, u: usize, v: usize, c: f64) {
        self.next[u].push(self.head.len());
        self.head.push(v);
        self.cap.push(c);
        self.next[v].push(self.head.len());
        self.head.push(u);
        self.cap.push(c);
    }

    fn bfs(&mut self, s: usize, t: usize) -> bool {
        self.level.iter_mut().for_each(|l| *l = -1);
        let mut queue = std::collections::VecDeque::new();
        self.level[s] = 0;
        queue.push_back(s);
        while let Some(u) = queue.pop_front() {
            for idx in 0..self.next[u].len() {
                let e = self.next[u][idx];
                let v = self.head[e];
                if self.cap[e] > 1e-12 && self.level[v] < 0 {
                    self.level[v] = self.level[u] + 1;
                    queue.push_back(v);
                }
            }
        }
        self.level[t] >= 0
    }

    fn dfs(&mut self, u: usize, t: usize, limit: f64) -> f64 {
        if u == t {
            return limit;
        }
        while self.iter[u] < self.next[u].len() {
            let e = self.next[u][self.iter[u]];
            let v = self.head[e];
            if self.cap[e] > 1e-12 && self.level[v] == self.level[u] + 1 {
                let d = self.dfs(v, t, limit.min(self.cap[e]));
                if d > 1e-12 {
                    self.cap[e] -= d;
                    self.cap[e ^ 1] += d;
                    return d;
                }
            }
            self.iter[u] += 1;
        }
        0.0
    }

    fn max_flow(&mut self, s: usize, t: usize) -> f64 {
        let mut total = 0.0;
        while self.bfs(s, t) {
            self.iter.iter_mut().for_each(|i| *i = 0);
            loop {
                let f = self.dfs(s, t, f64::INFINITY);
                if f <= 1e-12 {
                    break;
                }
                total += f;
            }
        }
        total
    }

    /// Vertices reachable from `s` in the residual network: the source side of a
    /// minimum cut.
    fn source_side(&mut self, s: usize) -> Vec<bool> {
        let mut seen = vec![false; self.next.len()];
        let mut queue = std::collections::VecDeque::new();
        seen[s] = true;
        queue.push_back(s);
        while let Some(u) = queue.pop_front() {
            for idx in 0..self.next[u].len() {
                let e = self.next[u][idx];
                let v = self.head[e];
                if self.cap[e] > 1e-9 && !seen[v] {
                    seen[v] = true;
                    queue.push_back(v);
                }
            }
        }
        seen
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{NodeType, UndirectedGraph};
    use std::collections::VecDeque;

    fn directed(g: &UndirectedGraph) -> DirectedGraph {
        DirectedGraph::from_undirected(g)
    }

    /// Every emitted row must hold at every Steiner tree of the instance.
    ///
    /// This is the same discipline as the partition harness: enumerate all
    /// integral points and check the row that would actually be installed.
    #[test]
    fn every_emitted_row_holds_for_every_steiner_tree() {
        let mut seed = 0x1234_5678_9ABC_DEF1u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        let mut checked = 0usize;
        let mut violations = Vec::new();

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
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 4 != 0 {
                        g.add_edge(u, v, 1.0);
                    }
                }
            }
            if g.edges.len() > 15 {
                continue;
            }
            let dg = directed(&g);
            let root = terminals[0];
            let trees = all_trees(&dg, root, &terminals);
            if trees.is_empty() {
                continue;
            }

            // A convex combination of trees can never violate a valid row, so
            // testing on one proves nothing about validity. What is needed is a
            // point outside the integer hull, which is what the LP hands the
            // separator in practice.
            let mut y = vec![0.0; dg.arcs.len()];
            for v in y.iter_mut() {
                *v = (rng() % 61) as f64 / 100.0;
            }
            let mut s = vec![0.0; n as usize + 1];
            for v in 1..=n as usize {
                s[v] = (rng() % 101) as f64 / 100.0;
            }
            for &t in &terminals {
                s[t as usize] = 1.0;
            }

            let mut sep = ActivationRankSeparator::new(&dg);
            for cut in sep.find_violated_cuts(&y, &s, &terminals) {
                checked += 1;
                let inside: Vec<bool> = {
                    let mut f = vec![false; n as usize + 1];
                    for &v in &cut.vertices {
                        f[v as usize] = true;
                    }
                    f
                };
                for tree in &trees {
                    // Left-hand side at this tree: edges inside U, plus s_anchor.
                    let mut used = vec![false; n as usize + 1];
                    used[root as usize] = true;
                    let mut lhs = 0.0;
                    for (i, &val) in tree.iter().enumerate() {
                        if val > 0.5 {
                            let (t_, h) = (dg.arcs[i].tail, dg.arcs[i].head);
                            used[t_ as usize] = true;
                            used[h as usize] = true;
                            if inside[t_ as usize] && inside[h as usize] {
                                lhs += 1.0;
                            }
                        }
                    }
                    lhs += if used[cut.anchor as usize] { 1.0 } else { 0.0 };
                    let rhs: f64 =
                        cut.vertices.iter().filter(|&&v| used[v as usize]).count() as f64;
                    if lhs > rhs + 1e-6 {
                        violations.push(format!(
                            "|U|={} anchor {} : lhs {lhs} > rhs {rhs}",
                            cut.vertices.len(),
                            cut.anchor
                        ));
                        break;
                    }
                }
            }
        }

        assert!(checked > 0, "no rows were emitted; the test proves nothing");
        eprintln!("checked {checked} emitted activation-rank rows");
        assert!(violations.is_empty(), "invalid rows: {:#?}", &violations[..violations.len().min(4)]);
    }

    /// The separator is exact, so a brute-force scan over all `U` must not find a
    /// larger violation than the min cut reports.
    #[test]
    fn separation_matches_brute_force() {
        let mut seed = 0xFEED_FACE_C0DE_0001u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..200 {
            let n = 4 + (rng() % 4) as u32;
            let mut g = UndirectedGraph::new(n);
            for v in 1..=n {
                g.add_node(v, if v <= 2 { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        g.add_edge(u, v, 1.0);
                    }
                }
            }
            if g.edges.is_empty() {
                continue;
            }
            let dg = directed(&g);
            let mut y = vec![0.0; dg.arcs.len()];
            for v in y.iter_mut() {
                *v = (rng() % 51) as f64 / 100.0;
            }
            let mut s = vec![0.0; n as usize + 1];
            for v in 1..=n as usize {
                s[v] = (rng() % 101) as f64 / 100.0;
            }

            let sep = ActivationRankSeparator::new(&dg);
            let anchor: NodeId = 1;

            // Brute force over every U containing the anchor.
            let mut best = f64::NEG_INFINITY;
            for mask in 0u32..(1u32 << n) {
                if mask & 1 == 0 {
                    continue; // vertex 1 is bit 0
                }
                let inside = |v: NodeId| mask >> (v - 1) & 1 == 1;
                let mut lhs = 0.0;
                for p in 0..dg.arcs.len() / 2 {
                    let a = &dg.arcs[2 * p];
                    if inside(a.tail) && inside(a.head) {
                        lhs += y[2 * p] + y[2 * p + 1];
                    }
                }
                let rhs: f64 = (1..=n).filter(|&v| inside(v)).map(|v| s[v as usize]).sum();
                best = best.max(lhs + s[anchor as usize] - rhs);
            }

            let mut sep = sep;
            let cuts = sep.find_violated_cuts(&y, &s, &[anchor]);
            let found = cuts.first().map(|c| c.violation).unwrap_or(f64::NEG_INFINITY);
            if best > sep.violation_tolerance {
                assert!(
                    (found - best).abs() < 1e-6,
                    "separator reported {found}, brute force says {best}"
                );
            } else {
                assert!(cuts.is_empty(), "separator invented a violation of {found}");
            }
        }
    }

    fn all_trees(g: &DirectedGraph, root: NodeId, terminals: &[NodeId]) -> Vec<Vec<f64>> {
        let mut edges: Vec<(NodeId, NodeId, ArcId, ArcId)> = Vec::new();
        for p in 0..g.arcs.len() / 2 {
            let f = &g.arcs[2 * p];
            let r = &g.arcs[2 * p + 1];
            edges.push((f.tail, f.head, f.id, r.id));
        }
        let m = edges.len();
        let n = g.nodes.iter().map(|x| x.id).max().unwrap_or(0) as usize + 1;
        let mut out = Vec::new();
        for mask in 0u32..(1u32 << m) {
            let chosen: Vec<&(NodeId, NodeId, ArcId, ArcId)> =
                (0..m).filter(|i| mask >> i & 1 == 1).map(|i| &edges[i]).collect();
            let mut adj: Vec<Vec<(NodeId, ArcId)>> = vec![Vec::new(); n];
            for &&(u, v, f, b) in &chosen {
                adj[u as usize].push((v, f));
                adj[v as usize].push((u, b));
            }
            let mut seen = vec![false; n];
            let mut vector = vec![0.0; g.arcs.len()];
            let mut used = 0usize;
            let mut queue = VecDeque::new();
            seen[root as usize] = true;
            queue.push_back(root);
            while let Some(x) = queue.pop_front() {
                for &(y, forward) in &adj[x as usize] {
                    if seen[y as usize] {
                        continue;
                    }
                    seen[y as usize] = true;
                    vector[forward as usize] = 1.0;
                    used += 1;
                    queue.push_back(y);
                }
            }
            if used != chosen.len() || !terminals.iter().all(|&t| seen[t as usize]) {
                continue;
            }
            out.push(vector);
        }
        out
    }
}
