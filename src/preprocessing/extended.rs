//! Extended reductions: rule out *trees*, not edges.
//!
//! # Why the arsenal needed this and not another test
//!
//! §59 and §62 closed two individually strong implication mechanisms for the
//! same reason. The standalone implied-profit deletion finds large profits on 63
//! of 76 reduced graphs and deletes **zero** edges; Proposition 8 at `|P| = 2`
//! coincides with the reduced-cost fixing already present. Neither is weak — both
//! are starved of the same input, which is *a supply of trees to rule out*. A
//! criterion that can only be asked about a single edge is being asked the
//! easiest question it knows.
//!
//! This module is the supply. It enumerates trees `Y` growing out of a candidate
//! edge and asks, of each, whether any minimum Steiner tree can contain it in
//! the peripheral sense below. If every extension along some non-terminal leaf
//! is ruled out, `Y` itself is; if `Y` is the single candidate edge, that edge is
//! deleted.
//!
//! # Status: correct, gated, measured — and **not wired in**
//!
//! Two real faults were found here and fixed: an extension-set cap applied as a
//! truncation rather than a refusal, and retired terminal ids reaching
//! `SdClosure::build` and turning its over-estimate of the special distance into
//! an under-estimate. §70 of the research notes records both, and the wrong
//! answer on PACE Track 1's instance135 that exposed them. Wired in afterwards it
//! produces **no wrong answer on any benchmark slice**, and Track 1 [1..140]
//! returns 140/140.
//!
//! It is off for a measured reason and not a mathematical one: it takes Track 2
//! from 110–111 to **106**, because the classical fixpoint stops converging in
//! 0.10 s of its 1.67 s share and starts using all of it, and the instances that
//! pay are ones the width DP was closing in 0.06 s. §72 has the numbers and names
//! the next experiment — dispatch it only where the downstream cannot use the
//! time, which needs the decomposition width measured *before* the reduction and
//! therefore belongs to `solver::solve` and not to this layer.
//!
//! What it *does* is not in doubt: on the 42 Track 2 instances at width 14 to 20
//! where the existing arsenal deletes nothing at all, it fires on 31, and three
//! of them cross the width DP's cap.
//!
//! # Definitions, stated once
//!
//! For a tree `Y ⊆ G`, `L(Y)` is its leaf set. `Y'` is **peripherally contained**
//! in a tree `S` when `Y' ⊆ S` and every vertex of `V(Y') \ L(Y')` has the same
//! degree in `S` as in `Y'` — that is, `S` may hang extra branches off `Y'` only
//! at its leaves. For a single edge `e`, `L(Y) = e`, so peripheral containment is
//! just `e ∈ S`.
//!
//! For a pruning set `P ⊆ V(Y)`, `Y_P` is the union of the `Y`-paths between
//! members of `P`, and `Y_p` is the part of `Y` that hangs off `p`. Throughout
//! this module `P = L(Y)`, which is a **strict** pruning set: for a tree, the
//! union of the leaf-to-leaf paths is the whole tree, so `Y_P = Y`, every `Y_p`
//! is the single vertex `p`, and the contracted graph `G_{Y,P}` of Theorem 3 is
//! `G` itself. That is what makes the criteria below cheap enough to run inside
//! an enumeration: the "contracted distance network" is the ordinary special
//! distance network, and nothing has to be contracted at all.
//!
//! The hypothesis `V(Y_P) ∩ T ⊆ L(Y_P)` — every terminal of `Y` is a leaf of `Y`
//! — is an invariant of the enumeration: the seed satisfies it and extension
//! happens only at *non-terminal* leaves, so an interior vertex is never a
//! terminal.
//!
//! # The criteria
//!
//! > **Corollary 3 (contracted-distance pruning).** Let `F'` be a minimum
//! > spanning tree of the complete graph on `P` under the special distance `s`,
//! > of weight `z'`. Let `F''` be a minimum spanning tree of the complete graph
//! > on the *terminals* under `s`, its edges listed in nonincreasing `s`, and let
//! > `z''` be the sum of the `|P''|` largest for a partition `(P', P'')` of `P`.
//! > If `z' + z'' < c(E(Y))` then `Y` is not `P`-peripherally contained in any
//! > minimum Steiner tree.
//!
//! The proof is the paper's and is not restated. What matters for the
//! implementation is *which direction the inequality tolerates error*: `s` may be
//! replaced anywhere by an **over-estimate**. Both `z'` and `z''` then only grow,
//! so the criterion only becomes harder to satisfy, and every deletion it makes
//! is still justified. That licence is used twice — the special distance here is
//! the terminal-chain closure minimised against a *radius-bounded* shortest path,
//! and both are over-estimates of the true `s`.
//!
//! > **Proposition 7 (pruned-tree bottlenecks).** For `v, w ∈ V(Y)`, let
//! > `b_{Y,P}(v,w)` be the greatest cost of a subpath `Q(a,b)` of the `Y`-path
//! > from `v` to `w` whose interior vertices have `Y`-degree two, lie outside
//! > `P`, and are not terminals, and with `V(Q) ∩ T ⊆ {a,b}`. If
//! > `s(v,w) < b_{Y,P}(v,w)` then `Y` is not `P`-peripherally contained in any
//! > minimum Steiner tree.
//!
//! Again an over-estimate of `s` is safe: the criterion fires less often. At
//! `|E(Y)| = 1` this *is* the classical special-distance test — the path is the
//! edge and `b = c(e)` — which is the sense in which the whole module is a
//! generalisation of what the pipeline already had, rather than a new gamble.
//!
//! # The exchange argument for the extension step, and where zero costs bite
//!
//! > **Proposition (extension).** Let `v` be a non-terminal leaf of `Y` and
//! > suppose that for every non-empty `γ ⊆ δ(v) \ E(Y)` in the extension set,
//! > `Y + γ` is not peripherally contained in any leaf-pruned minimum Steiner
//! > tree. Then neither is `Y`.
//!
//! *Proof.* Suppose `Y` is peripherally contained in a leaf-pruned minimum tree
//! `S`. `v` is a leaf of `Y` and not a terminal, so it is not a leaf of `S`,
//! hence `deg_S(v) ≥ 2` and the extra edges `γ := δ_S(v) \ E(Y)` are non-empty.
//! Peripheral containment of `Y` in `S` says `S` branches off `Y` only at leaves,
//! and `Y + γ` differs from `Y` only at the leaf `v`, so `Y + γ` is peripherally
//! contained in `S` too. Algorithm 2 guarantees every `γ` it drops is already
//! ruled out, so `γ` is in the extension set and `Y + γ` is ruled out —
//! contradiction. ∎
//!
//! **"Leaf-pruned" is load-bearing and is why zero-cost edges are excluded.**
//! The step needs *some* minimum Steiner tree with no non-terminal leaf. With
//! nonnegative costs one always exists — prune the leaf, the cost does not rise —
//! so the conclusion delivered is "no *leaf-pruned* minimum tree contains `e`",
//! and deleting `e` preserves that tree. That is exactly the invariant this
//! pipeline is stated in (`reduced optimum + offset = original optimum`), which
//! asks for *an* optimum to survive and not for all of them. The base criteria
//! prove the stronger "no minimum tree at all", so nothing is lost by mixing them.
//!
//! # No double counting
//!
//! Every criterion here is a statement about one enumerated tree `Y` and is
//! discharged against `c(E(Y))`, a sum over the *distinct* edges of `Y`; the
//! enumeration adds each edge once and `TreeState::push` refuses an edge already
//! present. The reconnection costs `z'` and `z''` are read off two different
//! spanning trees and added once each, exactly as Corollary 3 states. Nothing in
//! a deletion is charged to a second deletion: each is derived from the graph as
//! it stands when the deletion is made, and the driver re-derives the distance
//! oracle whenever the graph changes.

use std::collections::HashMap;

use crate::graph::{Cost, EdgeId, NodeId};

use super::csr::{Csr, DijkstraWorkspace};
use super::sd_closure::SdClosure;
use super::ReducibleGraph;

/// Bound on the enumerated trees per candidate, and on how far they may grow.
///
/// Both are work bounds and neither can change an answer: abandoning the
/// enumeration returns `false`, which deletes nothing.
#[derive(Debug, Clone, Copy)]
pub struct ExtendedLimits {
    /// Edges an enumerated tree may hold.
    pub max_edges: usize,
    /// Trees the enumeration may visit per candidate edge.
    pub max_nodes: u64,
    /// Extension sets a leaf may have before it is refused outright.
    ///
    /// It is a *refusal* threshold and not a truncation, because ruling out a
    /// subset of the extensions rules out nothing — see `extension_sets`, and
    /// see §70 for the wrong answer that established it the hard way.
    pub max_extensions: usize,
    /// Degree above which a leaf is not extended at all. `2^deg` subsets is the
    /// size of the extension set's power set.
    pub max_leaf_degree: usize,
}

impl Default for ExtendedLimits {
    fn default() -> Self {
        Self { max_edges: 4, max_nodes: 400, max_extensions: 16, max_leaf_degree: 8 }
    }
}

/// Counters, so the driver can report what the enumeration actually did rather
/// than what it was configured to do.
#[derive(Debug, Clone, Default)]
pub struct ExtendedStats {
    pub candidates: u64,
    pub trees_visited: u64,
    pub deleted: u64,
    pub ruled_out_by_corollary3: u64,
    pub ruled_out_by_proposition7: u64,
    pub budget_exhausted: u64,
    pub dijkstras: u64,
}

/// The tree under enumeration, with the incremental state the criteria need.
struct TreeState {
    edges: Vec<EdgeId>,
    /// Endpoints of `edges`, parallel.
    ends: Vec<(NodeId, NodeId)>,
    cost: Cost,
    /// Degree in `Y`, for vertices of `Y` only.
    deg: HashMap<NodeId, u32>,
    /// Adjacency inside `Y`: vertex -> (neighbour, edge cost).
    adj: HashMap<NodeId, Vec<(NodeId, Cost)>>,
}

impl TreeState {
    fn new() -> Self {
        TreeState {
            edges: Vec::new(),
            ends: Vec::new(),
            cost: 0.0,
            deg: HashMap::new(),
            adj: HashMap::new(),
        }
    }

    fn contains_edge(&self, e: EdgeId) -> bool {
        self.edges.contains(&e)
    }

    fn contains_vertex(&self, v: NodeId) -> bool {
        self.deg.contains_key(&v)
    }

    /// Add `e = {u,v}`; `u` must already be in the tree unless the tree is empty.
    fn push(&mut self, e: EdgeId, u: NodeId, v: NodeId, c: Cost) {
        debug_assert!(!self.contains_edge(e));
        self.edges.push(e);
        self.ends.push((u, v));
        self.cost += c;
        *self.deg.entry(u).or_insert(0) += 1;
        *self.deg.entry(v).or_insert(0) += 1;
        self.adj.entry(u).or_default().push((v, c));
        self.adj.entry(v).or_default().push((u, c));
    }

    fn pop(&mut self) {
        let Some(e) = self.edges.pop() else { return };
        let (u, v) = self.ends.pop().expect("parallel");
        let _ = e;
        let c = {
            let a = self.adj.get_mut(&u).expect("adjacency");
            let c = a.pop().expect("edge").1;
            c
        };
        self.adj.get_mut(&v).expect("adjacency").pop();
        self.cost -= c;
        for x in [u, v] {
            let d = self.deg.get_mut(&x).expect("degree");
            *d -= 1;
            if *d == 0 {
                self.deg.remove(&x);
                self.adj.remove(&x);
            }
        }
    }

    fn leaves(&self) -> Vec<NodeId> {
        let mut l: Vec<NodeId> =
            self.deg.iter().filter(|&(_, &d)| d == 1).map(|(&v, _)| v).collect();
        // Container order must not decide anything; see §32.
        l.sort_unstable();
        l
    }

    fn vertices(&self) -> Vec<NodeId> {
        let mut v: Vec<NodeId> = self.deg.keys().copied().collect();
        v.sort_unstable();
        v
    }

    /// The `Y`-path from `v` to `w`, as a vertex list.
    fn path(&self, v: NodeId, w: NodeId) -> Option<Vec<NodeId>> {
        if v == w {
            return Some(vec![v]);
        }
        let mut prev: HashMap<NodeId, NodeId> = HashMap::new();
        let mut stack = vec![v];
        prev.insert(v, v);
        while let Some(x) = stack.pop() {
            if x == w {
                let mut out = vec![w];
                let mut cur = w;
                while cur != v {
                    cur = prev[&cur];
                    out.push(cur);
                }
                out.reverse();
                return Some(out);
            }
            for &(y, _) in self.adj.get(&x)? {
                if !prev.contains_key(&y) {
                    prev.insert(y, x);
                    stack.push(y);
                }
            }
        }
        None
    }

    fn edge_cost(&self, a: NodeId, b: NodeId) -> Cost {
        self.adj
            .get(&a)
            .map(|l| {
                l.iter().filter(|&&(x, _)| x == b).map(|&(_, c)| c).fold(Cost::INFINITY, Cost::min)
            })
            .unwrap_or(Cost::INFINITY)
    }
}

/// An over-estimate of the special (bottleneck Steiner) distance.
///
/// Two sources, both over-estimates of the true `s`, minimised together:
///
/// - the exact terminal-chain closure [`SdClosure`], which is `s` restricted to
///   walks broken at terminals — a min over a *subset* of the admissible walks,
///   hence `>= s`; and
/// - a radius-bounded shortest path in the live graph, which is one admissible
///   walk, hence `>= s`, and is `+inf` when the radius cut it off.
///
/// Over-estimating is the safe direction throughout this module (see the header),
/// so the radius may be chosen for cost alone.
struct SpecialDistance<'a> {
    sd: Option<&'a SdClosure>,
    /// `rows[i] = (source, dist)` for a bounded Dijkstra, stacked with the DFS.
    rows: Vec<(NodeId, Vec<Cost>)>,
}

impl<'a> SpecialDistance<'a> {
    fn value(&self, u: NodeId, v: NodeId) -> Cost {
        let mut best = self.sd.map(|s| s.value(u, v)).unwrap_or(Cost::INFINITY);
        for (src, row) in &self.rows {
            if *src == u {
                best = best.min(row[v as usize]);
            } else if *src == v {
                best = best.min(row[u as usize]);
            }
        }
        best
    }
}

/// Minimum spanning tree weight of the complete graph on `pts` under `s`.
///
/// Returns `None` when the points cannot be connected under a finite `s`, which
/// with a radius-bounded oracle simply means the bound is unusable here.
fn mst_weight(pts: &[NodeId], s: &SpecialDistance) -> Option<Cost> {
    let n = pts.len();
    if n <= 1 {
        return Some(0.0);
    }
    let mut in_tree = vec![false; n];
    let mut key = vec![Cost::INFINITY; n];
    key[0] = 0.0;
    let mut total = 0.0;
    for _ in 0..n {
        let mut best = usize::MAX;
        for i in 0..n {
            if !in_tree[i] && (best == usize::MAX || key[i] < key[best]) {
                best = i;
            }
        }
        if !key[best].is_finite() {
            return None;
        }
        in_tree[best] = true;
        total += key[best];
        for j in 0..n {
            if !in_tree[j] {
                let d = s.value(pts[best], pts[j]);
                if d < key[j] {
                    key[j] = d;
                }
            }
        }
    }
    Some(total)
}

/// The extended reduction, over one live graph.
pub struct Extended<'a> {
    graph: &'a ReducibleGraph,
    csr: &'a Csr,
    sd: Option<&'a SdClosure>,
    is_terminal: Vec<bool>,
    /// `s`-weights of a minimum spanning tree over all terminals, nonincreasing.
    /// This is the `F''` of Corollary 3 and does not depend on `Y`.
    terminal_mst_desc: Vec<Cost>,
    limits: ExtendedLimits,
    pub stats: ExtendedStats,
}

impl<'a> Extended<'a> {
    pub fn new(
        graph: &'a ReducibleGraph,
        csr: &'a Csr,
        sd: Option<&'a SdClosure>,
        limits: ExtendedLimits,
    ) -> Self {
        let n = csr.num_nodes;
        let mut is_terminal = vec![false; n];
        for &t in &graph.terminals {
            if (t as usize) < n && graph.is_node_valid(t) {
                is_terminal[t as usize] = true;
            }
        }
        // `F''`: a spanning tree of the terminals under `s`. Built from the same
        // closure the criteria use, so the two are consistent; absent when the
        // closure was not affordable, in which case Corollary 3 runs with
        // `P'' = ∅` only.
        let mut terminal_mst_desc = Vec::new();
        if let Some(sd) = sd {
            let ts = &sd.terminals;
            let k = ts.len();
            if k >= 2 {
                let mut in_tree = vec![false; k];
                let mut key = vec![Cost::INFINITY; k];
                key[0] = 0.0;
                for _ in 0..k {
                    let mut best = usize::MAX;
                    for i in 0..k {
                        if !in_tree[i] && (best == usize::MAX || key[i] < key[best]) {
                            best = i;
                        }
                    }
                    if best == usize::MAX || !key[best].is_finite() {
                        break;
                    }
                    in_tree[best] = true;
                    if key[best] > 0.0 {
                        terminal_mst_desc.push(key[best]);
                    }
                    for j in 0..k {
                        if !in_tree[j] {
                            let d = sd.value(ts[best], ts[j]);
                            if d < key[j] {
                                key[j] = d;
                            }
                        }
                    }
                }
                terminal_mst_desc.sort_by(|a, b| b.total_cmp(a));
            }
        }
        Extended {
            graph,
            csr,
            sd,
            is_terminal,
            terminal_mst_desc,
            limits,
            stats: ExtendedStats::default(),
        }
    }

    /// Whether edge `e` can be deleted: `Extended-RuledOut(I, {e})`.
    pub fn edge_is_ruled_out(&mut self, e: EdgeId, ws: &mut DijkstraWorkspace) -> bool {
        let edge = &self.graph.edges[e as usize];
        if edge.src == edge.dst || !self.graph.is_edge_valid(e) {
            return false;
        }
        // Nonnegative costs are what makes a leaf-pruned minimum tree exist; see
        // the header.
        if self.graph.edges.iter().any(|x| self.graph.is_edge_valid(x.id) && x.cost < 0.0) {
            return false;
        }
        self.stats.candidates += 1;
        let mut y = TreeState::new();
        y.push(e, edge.src, edge.dst, edge.cost);
        let mut s = SpecialDistance { sd: self.sd, rows: Vec::new() };
        let mut budget = self.limits.max_nodes;
        let out = self.ruled_out(&mut y, &mut s, &mut budget, ws);
        if budget == 0 {
            self.stats.budget_exhausted += 1;
        }
        out
    }

    /// Algorithm 1, depth-first.
    ///
    /// Extension happens from the leaf **farthest from the seed**, measured by
    /// the `Y`-distance to the first edge's endpoints. That is the paper's own
    /// order and it is not cosmetic: extending near the seed regrows the same
    /// shallow trees along every branch, while extending at the frontier makes
    /// `c(E(Y))` — the quantity every criterion is discharged against — grow as
    /// fast as the enumeration does.
    fn ruled_out(
        &mut self,
        y: &mut TreeState,
        s: &mut SpecialDistance<'a>,
        budget: &mut u64,
        ws: &mut DijkstraWorkspace,
    ) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        self.stats.trees_visited += 1;

        let p = y.leaves();
        if self.rule_out_strict(y, &p, s) {
            return true;
        }
        if y.edges.len() >= self.limits.max_edges {
            return false;
        }

        // Farthest leaf first.
        let seed = y.ends[0];
        let mut order: Vec<(usize, NodeId)> = p
            .iter()
            .map(|&v| {
                let d = y
                    .path(seed.0, v)
                    .map(|q| q.len())
                    .unwrap_or(0)
                    .max(y.path(seed.1, v).map(|q| q.len()).unwrap_or(0));
                (d, v)
            })
            .collect();
        order.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));

        for (_, v) in order {
            if self.is_terminal[v as usize] {
                continue;
            }
            let sets = self.extension_sets(y, v, s, budget, ws);
            let Some(sets) = sets else { continue };
            if sets.is_empty() {
                // Every single-edge extension at `v` was ruled out, so no
                // extension at all survives and `Y` is ruled out along this leaf.
                return true;
            }
            let mut success = true;
            for set in &sets {
                let before = y.edges.len();
                let mut ok = true;
                for &(e, from, to, c) in set {
                    if y.contains_edge(e) || y.contains_vertex(to) {
                        // Closing a cycle. `Y + γ` is then not a forest, so it is
                        // not a subgraph of any tree, and the extension
                        // proposition's `γ = δ_S(v) \ E(Y)` can never equal it.
                        // Skipping it is sound and not merely convenient.
                        ok = false;
                        break;
                    }
                    y.push(e, from, to, c);
                }
                if ok {
                    let pushed = self.push_row(to_source(set), s, y.cost, ws);
                    let ruled = self.ruled_out(y, s, budget, ws);
                    if pushed {
                        s.rows.pop();
                    }
                    if !ruled {
                        success = false;
                    }
                }
                while y.edges.len() > before {
                    y.pop();
                }
                if !ok {
                    // An extension that closes a cycle is vacuously ruled out.
                    continue;
                }
                if !success {
                    break;
                }
            }
            if success {
                return true;
            }
        }
        false
    }

    /// One bounded Dijkstra from the newest leaf, radius the current tree cost.
    ///
    /// A path longer than `c(E(Y))` cannot make any of the criteria fire — every
    /// one of them compares a sum of `s` values against `c(E(Y))` — so cutting
    /// the search there loses nothing that would have been used, and the entries
    /// it leaves at infinity are over-estimates, which is the safe direction.
    fn push_row(
        &mut self,
        src: Option<NodeId>,
        s: &mut SpecialDistance<'a>,
        radius: Cost,
        ws: &mut DijkstraWorkspace,
    ) -> bool {
        let Some(src) = src else { return false };
        self.stats.dijkstras += 1;
        self.csr.dijkstra_into(&[src], radius, ws);
        s.rows.push((src, ws.dist.clone()));
        true
    }

    /// Algorithm 2: the extension sets at `v`.
    ///
    /// Returns the subsets of `δ(v) \ E(Y)` that still have to be examined.
    /// `None` when the leaf is too high-degree to enumerate; an empty vector
    /// means every single-edge extension was ruled out, which rules out every
    /// non-empty subset with it.
    #[allow(clippy::type_complexity)]
    fn extension_sets(
        &mut self,
        y: &mut TreeState,
        v: NodeId,
        s: &mut SpecialDistance<'a>,
        budget: &mut u64,
        ws: &mut DijkstraWorkspace,
    ) -> Option<Vec<Vec<(EdgeId, NodeId, NodeId, Cost)>>> {
        let mut cand: Vec<(EdgeId, NodeId, Cost)> = Vec::new();
        for (w, c, e) in self.csr.neighbors(v) {
            if y.contains_edge(e) || y.contains_vertex(w) {
                continue;
            }
            cand.push((e, w, c));
        }
        cand.sort_by(|a, b| a.2.total_cmp(&b.2).then(a.0.cmp(&b.0)));
        if cand.is_empty() || cand.len() > self.limits.max_leaf_degree {
            return None;
        }

        // Lines 3–12: classify each single-edge extension.
        let mut q: Vec<(EdgeId, NodeId, Cost)> = Vec::new();
        let mut r: Vec<(EdgeId, NodeId, Cost)> = Vec::new();
        // `L(Y) ∪ {w}`, not `L(Y + e)`.
        //
        // The difference matters and is the paper's own choice. Algorithm 2 has
        // to guarantee something about every *superset* `γ ∋ e`, and a pruning
        // set for `Y + {e}` transfers to `Y + γ` only if the extra branches of
        // `γ` hang off a member of it. They hang off `v`, which is in `L(Y)` and
        // is **not** in `L(Y + e)` — adding `e` made it interior. Using the new
        // leaf set would prove a statement about `Y + {e}` alone and discard `e`
        // on the strength of it, which is exactly the gap Observation 3 closes.
        let p_old = y.leaves();
        for &(e, w, c) in &cand {
            y.push(e, v, w, c);
            let pushed = self.push_row(Some(w), s, y.cost, ws);
            let p_extended = {
                let mut p = p_old.clone();
                if !p.contains(&w) {
                    p.push(w);
                }
                p.sort_unstable();
                p
            };
            let out = self.rule_out(y, &p_extended, s);
            let strict = if out { false } else { self.rule_out_strict(y, &p_extended, s) };
            if pushed {
                s.rows.pop();
            }
            y.pop();
            if *budget == 0 {
                return None;
            }
            if out {
                continue;
            }
            if strict {
                r.push((e, w, c));
            } else {
                q.push((e, w, c));
            }
        }
        if q.is_empty() && r.is_empty() {
            return Some(Vec::new());
        }

        // `(P(Q) \ ∅) ∪ R`, cheapest first so a cap keeps the cheap ones.
        let mut sets: Vec<Vec<(EdgeId, NodeId, NodeId, Cost)>> = Vec::new();
        if q.len() <= 6 {
            for mask in 1u32..(1u32 << q.len()) {
                let mut set = Vec::new();
                for (i, &(e, w, c)) in q.iter().enumerate() {
                    if mask >> i & 1 == 1 {
                        set.push((e, v, w, c));
                    }
                }
                sets.push(set);
            }
        } else {
            return None;
        }
        for &(e, w, c) in &r {
            sets.push(vec![(e, v, w, c)]);
        }
        sets.sort_by(|a, b| {
            let ca: Cost = a.iter().map(|x| x.3).sum();
            let cb: Cost = b.iter().map(|x| x.3).sum();
            ca.total_cmp(&cb).then(a.len().cmp(&b.len()))
        });
        // **Not truncated.** Ruling out a subset of the extensions rules out
        // nothing: `success` at a leaf asserts that *every* surviving `γ` is
        // impossible, and a cap that silently drops the rest turns that into a
        // claim about the ones that were cheap enough to look at. The first
        // version of this module truncated here — the doc comment on
        // `max_extensions` even said a capped leaf could not establish success —
        // and it deleted an edge of PACE Track 1's instance135, which then
        // reported `Optimal 9187` against a reference of 9143.
        //
        // The cap is now applied by *refusing the leaf outright* when there are
        // more sets than may be examined, which is conservative in the only
        // direction that is safe.
        if sets.len() > self.limits.max_extensions {
            return None;
        }
        Some(sets)
    }

    /// `RuledOut(I, Y, P)` — criteria valid for an arbitrary pruning set.
    fn rule_out(&mut self, y: &TreeState, p: &[NodeId], s: &SpecialDistance) -> bool {
        self.corollary3(y, p, s) || self.proposition7(y, p, s)
    }

    /// `RuledOutStrict(I, Y, P)`. Every criterion valid for `RuledOut` is valid
    /// here; the strict-only ones (Proposition 8) are not implemented in this
    /// module — see §62 and the round notes for why they belong to the
    /// reduced-cost side of the pipeline.
    fn rule_out_strict(&mut self, y: &TreeState, p: &[NodeId], s: &SpecialDistance) -> bool {
        self.rule_out(y, p, s)
    }

    /// Corollary 3, minimised over the partitions `(P', P'')` obtained by peeling
    /// the costliest members of `P` off the spanning tree one at a time.
    ///
    /// Every choice of partition gives a valid bound, so taking the least over a
    /// subset of the choices is sound; enumerating all `2^{|P|}` of them is not
    /// worth its cost at these sizes and is not needed for validity.
    fn corollary3(&mut self, y: &TreeState, p: &[NodeId], s: &SpecialDistance) -> bool {
        if p.len() < 2 {
            return false;
        }
        let mut pts: Vec<NodeId> = p.to_vec();
        let mut j = 0usize;
        while pts.len() >= 2 {
            let Some(z1) = mst_weight(&pts, s) else { break };
            let z2: Cost = self.terminal_mst_desc.iter().take(j).sum();
            if z1 + z2 < y.cost - 1e-9 {
                self.stats.ruled_out_by_corollary3 += 1;
                return true;
            }
            // Peel the point whose cheapest connection into the rest is dearest;
            // that is the one whose removal drops `z'` the most.
            let mut worst = 0usize;
            let mut worst_key = -1.0;
            for (i, &a) in pts.iter().enumerate() {
                let k = pts
                    .iter()
                    .filter(|&&b| b != a)
                    .map(|&b| s.value(a, b))
                    .fold(Cost::INFINITY, Cost::min);
                if k > worst_key {
                    worst_key = k;
                    worst = i;
                }
            }
            pts.remove(worst);
            j += 1;
            if j > self.terminal_mst_desc.len() {
                break;
            }
        }
        false
    }

    /// Proposition 7.
    fn proposition7(&mut self, y: &TreeState, p: &[NodeId], s: &SpecialDistance) -> bool {
        let verts = y.vertices();
        for (i, &v) in verts.iter().enumerate() {
            for &w in verts.iter().skip(i + 1) {
                let Some(path) = y.path(v, w) else { continue };
                let b = self.pruned_bottleneck(y, p, &path);
                if b > 0.0 && s.value(v, w) < b - 1e-9 {
                    self.stats.ruled_out_by_proposition7 += 1;
                    return true;
                }
            }
        }
        false
    }

    /// `b_{Y,P}(v,w)`: the costliest admissible subpath of the `Y`-path.
    ///
    /// A vertex may be interior to the subpath only if it has `Y`-degree two,
    /// lies outside `P`, and is not a terminal. Terminals may sit at the two
    /// ends and nowhere else, which is what `V(Q) ∩ T ⊆ {a,b}` says.
    fn pruned_bottleneck(&self, y: &TreeState, p: &[NodeId], path: &[NodeId]) -> Cost {
        let ok_interior = |u: NodeId| {
            y.deg.get(&u).copied().unwrap_or(0) == 2
                && !p.contains(&u)
                && !self.is_terminal[u as usize]
        };
        let mut best: Cost = 0.0;
        let mut i = 0usize;
        while i + 1 < path.len() {
            // Grow a maximal segment starting at `path[i]`.
            let mut j = i;
            let mut acc = 0.0;
            while j + 1 < path.len() {
                acc += y.edge_cost(path[j], path[j + 1]);
                j += 1;
                if acc > best {
                    best = acc;
                }
                if !ok_interior(path[j]) {
                    break;
                }
            }
            i += 1;
        }
        best
    }
}

/// The vertex a single-edge extension set reaches, when it is a single edge.
fn to_source(set: &[(EdgeId, NodeId, NodeId, Cost)]) -> Option<NodeId> {
    (set.len() == 1).then(|| set[0].2)
}

/// Run the extended reduction to a fixpoint over the live edges.
///
/// Returns the number of edges deleted. The loop is watched in the sense §39
/// asks for: an edge is re-tested only when the graph has changed since it was
/// last refused, and a pass that deletes nothing stops.
pub fn extended_reductions(
    graph: &mut ReducibleGraph,
    limits: ExtendedLimits,
    deadline: Option<std::time::Instant>,
) -> (u32, ExtendedStats) {
    let mut total = 0u32;
    let mut stats = ExtendedStats::default();
    loop {
        let csr = Csr::build(graph);
        // **Live** terminals only.
        //
        // `ReducibleGraph::terminals` is never pruned: `remove_node` and
        // `contract_edge` leave the ids they retire in the set. Handing those to
        // `SdClosure::build` gives it distance rows that are infinite everywhere,
        // the metric-closure spanning tree over the terminals becomes a forest,
        // and the half-closure it derives from that forest is not the special
        // distance of anything. A special distance that is too *small* makes
        // every criterion here fire when it should not — the one direction the
        // over-estimate licence does not cover.
        //
        // This is what deleted an edge of PACE Track 1's instance135 and reported
        // `Optimal 9187` against a reference of 9143. The three brute-force gates
        // could not see it: they build a `ReducibleGraph` from a fresh instance,
        // so nothing has been retired and the two sets coincide. In
        // `preprocess_bounded` they do not.
        let terminals: Vec<NodeId> = {
            let mut t: Vec<NodeId> =
                graph.terminals.iter().copied().filter(|&v| graph.is_node_valid(v)).collect();
            t.sort_unstable();
            t
        };
        let n = csr.num_nodes;
        let sd = if SdClosure::affordable(n, terminals.len()) {
            let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();
            SdClosure::build(&terminals, &dist, n)
        } else {
            None
        };
        let mut ws = DijkstraWorkspace::new(n);
        let mut victims: Vec<EdgeId> = Vec::new();
        {
            let snapshot = &*graph;
            let mut ext = Extended::new(snapshot, &csr, sd.as_ref(), limits);
            let mut live: Vec<EdgeId> = snapshot
                .edges
                .iter()
                .filter(|e| snapshot.is_edge_valid(e.id) && e.src != e.dst)
                .map(|e| e.id)
                .collect();
            // Dearest first: an expensive edge has the largest `c(E(Y))` to
            // discharge against and is the likeliest to be ruled out.
            live.sort_by(|&a, &b| {
                snapshot.edges[b as usize].cost.total_cmp(&snapshot.edges[a as usize].cost)
            });
            for e in live {
                if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                    break;
                }
                if ext.edge_is_ruled_out(e, &mut ws) {
                    victims.push(e);
                }
            }
            stats.candidates += ext.stats.candidates;
            stats.trees_visited += ext.stats.trees_visited;
            stats.ruled_out_by_corollary3 += ext.stats.ruled_out_by_corollary3;
            stats.ruled_out_by_proposition7 += ext.stats.ruled_out_by_proposition7;
            stats.budget_exhausted += ext.stats.budget_exhausted;
            stats.dijkstras += ext.stats.dijkstras;
        }
        if victims.is_empty() {
            break;
        }
        // Deletions are derived independently of one another from the graph as it
        // stood, so applying them together is sound only if each is still
        // justified afterwards. It is: every criterion above rules `Y` out of
        // *every* leaf-pruned minimum tree of the graph it was derived on, and
        // removing other edges cannot create a new minimum tree containing `Y`
        // that was not one before — the trees of a subgraph are a subset of the
        // trees of the graph, and the surviving optimum is one of them.
        //
        // One exception has to be respected: the deletions must not disconnect
        // the terminals. They cannot — each is justified by a *cheaper*
        // reconnection that exists in the graph — but the check is cheap and the
        // consequence of being wrong is unbounded, so it is made.
        for &e in &victims {
            graph.remove_edge(e);
        }
        if !terminals_connected(graph) {
            for &e in &victims {
                graph.restore_edge(e);
            }
            break;
        }
        total += victims.len() as u32;
        stats.deleted += victims.len() as u64;
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            break;
        }
    }
    (total, stats)
}

fn terminals_connected(graph: &ReducibleGraph) -> bool {
    let mut ts: Vec<NodeId> = graph.terminals.iter().copied().collect();
    ts.sort_unstable();
    let Some(&r) = ts.first() else { return true };
    let csr = Csr::build(graph);
    let d = csr.dijkstra(r);
    ts.iter().all(|&t| d.get(t as usize).is_some_and(|x| x.is_finite()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{NodeType, SteinerInstance, UndirectedGraph};

    fn build(
        n: u32,
        edges: &[(NodeId, NodeId, Cost)],
        terminals: &[NodeId],
    ) -> (SteinerInstance, UndirectedGraph) {
        let mut g = UndirectedGraph::new(n);
        for v in 1..=n {
            let t = terminals.contains(&v);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        for &(u, v, c) in edges {
            g.add_edge(u, v, c);
        }
        let inst = SteinerInstance {
            name: String::from("t"),
            comment: String::new(),
            num_nodes: n,
            num_edges: edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: terminals.to_vec(),
            root: None,
        };
        (inst, g)
    }

    fn brute_force(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
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
        best.is_finite().then_some(best)
    }

    /// The optimum may not move, on every graph the generator can make.
    ///
    /// This is the gate the correctness standard asks for and it is stated over
    /// the *reduced optimum plus offset*: the module contracts nothing, so the
    /// offset is zero and the reduced optimum must equal the original one
    /// exactly.
    #[test]
    fn never_changes_the_optimum() {
        let mut seed = 0x2718_2818_2845_9045u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        let mut deletions = 0u64;
        for _ in 0..900 {
            let n = 5 + (rng() % 5) as u32;
            let k = 2 + (rng() % 3) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut edges = Vec::new();
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            for w in perm.windows(2) {
                edges.push((w[0], w[1], 1.0 + (rng() % 9) as f64));
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < 35 && !edges.iter().any(|&(a, b, _)| (a, b) == (u, v)) {
                        edges.push((u, v, 1.0 + (rng() % 9) as f64));
                    }
                }
            }
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };
            let (inst, g) = build(n, &edges, &terminals);
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            let (deleted, _) = extended_reductions(&mut rg, ExtendedLimits::default(), None);
            deletions += deleted as u64;
            assert!((rg.offset - 0.0).abs() < 1e-12, "the module contracts nothing");
            let after: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let Some(red) = brute_force(n, &after, &terminals) else {
                panic!("terminals disconnected on n={n} edges={edges:?}");
            };
            assert!(
                (red - opt).abs() < 1e-6,
                "reduced optimum {red} != {opt} after {deleted} deletions on n={n} edges={edges:?}"
            );
            ran += 1;
        }
        assert!(ran > 400, "only {ran} cases ran");
        assert!(deletions > 0, "the rule never fired, so the test proves nothing");
    }

    /// The same, on graphs dense enough for high-degree leaves — the regime
    /// where the extension sets are power sets and the branching is real.
    #[test]
    fn never_changes_the_optimum_on_dense_graphs() {
        let mut seed = 0x1414_2135_6237_3095u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        let mut deletions = 0u64;
        for _ in 0..500 {
            let n = 6 + (rng() % 2) as u32;
            let k = 2 + (rng() % 3) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut edges = Vec::new();
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < 85 {
                        edges.push((u, v, 1.0 + (rng() % 6) as f64));
                    }
                }
            }
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };
            let (inst, g) = build(n, &edges, &terminals);
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            let (deleted, _) = extended_reductions(&mut rg, ExtendedLimits::default(), None);
            deletions += deleted as u64;
            let after: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let Some(red) = brute_force(n, &after, &terminals) else {
                panic!("terminals disconnected on n={n} edges={edges:?}");
            };
            assert!(
                (red - opt).abs() < 1e-6,
                "reduced optimum {red} != {opt} after {deleted} deletions on n={n} edges={edges:?}"
            );
            ran += 1;
        }
        assert!(ran > 200, "only {ran} cases ran");
        assert!(deletions > 0, "the rule never fired, so the test proves nothing");
    }

    /// Bigger graphs than brute force can reach, against Dreyfus-Wagner.
    ///
    /// The three generators above cap at ten vertices and twenty edges, because
    /// that is where subset enumeration stops. PACE Track 1's instance135 was
    /// deleted wrongly by a version of this module that passed all three, so the
    /// regime that matters is evidently past them: more vertices, higher degree,
    /// parallel edges, and long degree-two chains — the shapes a reduced graph
    /// actually has.
    #[test]
    fn never_changes_the_optimum_against_dreyfus_wagner() {
        use crate::graph::algorithms::dreyfus_wagner;
        let mut seed = 0x3141_5926_5358_9793u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        let mut deletions = 0u64;
        for round in 0..1500 {
            let n = 18 + (rng() % 22) as u32;
            let k = 2 + (rng() % 5) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut edges: Vec<(NodeId, NodeId, Cost)> = Vec::new();
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            let unit = round % 3 == 0;
            for w in perm.windows(2) {
                let c = if unit { 1.0 } else { 1.0 + (rng() % 9) as f64 };
                edges.push((w[0], w[1], c));
            }
            let density = 5 + (rng() % 25) as u64;
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < density {
                        let c = if unit { 1.0 } else { 1.0 + (rng() % 9) as f64 };
                        edges.push((u, v, c));
                    }
                }
            }
            // Parallel edges: a reduced graph has them, from degree-two
            // contraction, and they are what a distance oracle keyed by endpoint
            // pair is most likely to confuse.
            let extra = (rng() % 4) as usize;
            for _ in 0..extra {
                if edges.is_empty() {
                    break;
                }
                let i = (rng() % edges.len() as u64) as usize;
                let (a, b, c) = edges[i];
                edges.push((a, b, c + (rng() % 3) as f64));
            }
            let (inst, g) = build(n, &edges, &terminals);
            let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
            let opt = dw.optimal_cost;
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            let (deleted, _) = extended_reductions(&mut rg, ExtendedLimits::default(), None);
            deletions += deleted as u64;
            let (_, g2) = rg.to_instance();
            let Some(after) = dreyfus_wagner(&g2, &{
                let mut t: Vec<NodeId> = rg.terminals.iter().copied().collect();
                t.sort_unstable();
                // `to_instance` renumbers, so ask it for the terminals it emitted.
                let map = rg.node_renumbering();
                t.iter().map(|x| map[x]).collect::<Vec<_>>()
            }) else {
                panic!("terminals disconnected on n={n} edges={edges:?}");
            };
            assert!(
                (after.optimal_cost + rg.offset - opt).abs() < 1e-6,
                "reduced optimum {} + offset {} != {opt} after {deleted} deletions \
                 on n={n} edges={edges:?}",
                after.optimal_cost,
                rg.offset
            );
            ran += 1;
        }
        assert!(ran > 300, "only {ran} cases ran");
        assert!(deletions > 0, "the rule never fired, so the test proves nothing");
    }

    /// Unit costs, where every tie the criteria can face actually happens and
    /// the strict inequalities are the only thing separating a valid deletion
    /// from one that removes the last optimum.
    #[test]
    fn never_changes_the_optimum_under_ties() {
        let mut seed = 0x6180_3398_8749_8948u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        for _ in 0..600 {
            let n = 5 + (rng() % 4) as u32;
            let k = 2 + (rng() % 3) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut edges = Vec::new();
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            for w in perm.windows(2) {
                edges.push((w[0], w[1], 1.0));
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < 40 && !edges.iter().any(|&(a, b, _)| (a, b) == (u, v)) {
                        edges.push((u, v, 1.0));
                    }
                }
            }
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };
            let (inst, g) = build(n, &edges, &terminals);
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            extended_reductions(&mut rg, ExtendedLimits::default(), None);
            let after: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let Some(red) = brute_force(n, &after, &terminals) else {
                panic!("terminals disconnected on n={n} edges={edges:?}");
            };
            assert!((red - opt).abs() < 1e-6, "reduced optimum {red} != {opt}");
            ran += 1;
        }
        assert!(ran > 300, "only {ran} cases ran");
    }
}
