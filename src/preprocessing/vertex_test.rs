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
//! make `mst_s(Q)` larger and the condition harder to satisfy. The zero- and
//! one-hop chains are always available:
//!
//! ```text
//! s(a, b) <= min( d(a, b),  min over terminals t of max( d(a, t), d(b, t) ) )
//! ```
//!
//! with `d` the shortest-path metric of `G - v`.
//!
//! # Longer chains, without recomputing anything per candidate
//!
//! Chains of length two and above need the terminal-to-terminal bottleneck matrix
//! **of `G - v`**, and the obvious way to get it — `|R|` Dijkstras per candidate —
//! costs more than the test is worth. The matrix of `G` is no substitute: deleting
//! a vertex can only *lengthen* paths, so `B_G <= B_{G-v}`, and using `B_G` would
//! be an upper bound on the wrong side.
//!
//! > **Lemma (transplanted hops).** Fix, once per sweep, a minimum spanning tree
//! > `M` of the terminal metric closure of `G`, and for each of its edges
//! > `{t, t'}` fix one shortest `t`-`t'` path `P_{tt'}` in `G` realising
//! > `d_G(t,t')`. Let `X` be any set of vertices and let `M_X` be the sub-forest
//! > of `M` whose edges have `P_{tt'} \cap X = {}`. Then for terminals `t, t'` in
//! > the same component of `M_X`, the maximum edge weight on their `M_X` path is
//! > an upper bound on `B_{G-X}(t, t')`.
//!
//! *Proof.* Every edge of the `M_X` path is realised by a path of `G` disjoint
//! from `X`, hence a path of `G - X`, of exactly its weight. Concatenating them
//! gives a terminal chain of `G - X` from `t` to `t'` whose bottleneck is the
//! path's maximum weight, and `B_{G-X}` is the minimum bottleneck over all such
//! chains. ∎
//!
//! Terminals in different components of `M_X` get no bound, which is sound —
//! infinity is an upper bound — and costs only deletions. `X` here is the
//! candidate `v` together with every vertex this sweep has already deleted, which
//! is exactly the graph the candidate is being judged against.
//!
//! With `M_X` in hand, [`super::sd_closure::BottleneckForest`] turns the
//! `|R|`-term minimisation into two linear passes, so the whole strengthening
//! costs `O(|R|)` per star member per candidate and no extra Dijkstra at all:
//!
//! ```text
//! s(a, b) <= min over terminals t' of max( g_a(t'), d(b, t') ),
//! g_a(t') = min over terminals t of max( d(a, t), B_{M_X}(t, t') ).
//! ```
//!
//! Setting `t = t'` recovers the one-hop bound, so this dominates it outright.
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
//!
//! # Not re-testing what cannot have changed
//!
//! The reduction loop runs this pass once per round, and a round removes a few
//! dozen elements out of tens of thousands. Re-scanning every vertex each time is
//! what the loop actually spends its life doing: on PACE instance189 the fixpoint
//! takes 74 rounds and this test alone costs 2.1 of the 3.3 seconds, for about
//! twenty deletions a round.
//!
//! Almost all of that work is provably wasted.
//!
//! > **Monotonicity.** Let `G'` be obtained from `G` by any sequence of the other
//! > reductions in this module, and let `v` be a vertex whose star — its
//! > neighbours and the costs to them — is identical in `G` and `G'`. Suppose the
//! > terminal set did not change. If `v` failed the test in `G`, it fails in `G'`.
//!
//! *Proof.* The test quantifies over subsets `Q` of `N(v)`, and `N(v)` and the
//! budgets `sum_{u in Q} c(v, u)` are unchanged by hypothesis, so the same
//! witness `Q` with `mst_s(Q) > budget(Q)` is still available. It remains to show
//! `s` does not decrease. Each of the other rules either deletes elements —
//! degree-0/1 removal, parallel-edge removal, bottleneck edge deletion, and this
//! test's own deletions — which cannot shorten any path, or is a degree-2
//! contraction, which replaces `n_1 - w - n_2` by a single edge of cost
//! `c(n_1,w) + c(w,n_2)` and so leaves `d(x, y)` unchanged for every surviving
//! pair. In both cases `d` is non-decreasing on the surviving vertices, and since
//! the terminal set is unchanged the bound
//! `s(a,b) <= min(d(a,b), min_t max(d(a,t), d(b,t)))` is non-decreasing too.
//! Hence `mst_s(Q)` is non-decreasing and the witness survives. ∎
//!
//! So a vertex only needs re-testing when its own star changed. [`StarWatch`]
//! records a hash of the star of every vertex that failed and skips it until that
//! hash moves.
//!
//! The transplanted-hop bound above weakens that lemma in one direction and only
//! one: the surviving forest `M_X` depends on which shortest paths were fixed,
//! and a different sweep can fix different ones, so the computed bound is monotone
//! only for a fixed choice. A vertex skipped by the watch can therefore in
//! principle miss a deletion a full recomputation would find. It cannot produce an
//! unsound one — every deletion is still evaluated against the live graph — and
//! the watch additionally forgets everything when the strengthening switches on or
//! off, so a failure recorded under the weak bound is never reused under the
//! strong one.
//!
//! The two hypotheses are real and both are checked by the caller rather than
//! assumed. Terminal *contraction* merges two vertices, which is a shortcut and
//! can shorten `d` anywhere in the graph; cut-vertex promotion *adds* terminals,
//! which gives `min_t` more to minimise over and can only lower `s`. Neither is
//! covered by the lemma, so [`preprocess_bounded`](super::preprocess_bounded)
//! calls [`StarWatch::invalidate_all`] whenever either fires.

use std::time::Instant;

use crate::graph::{Cost, NodeId};

use super::csr::{Csr, DijkstraWorkspace};
use super::sd_closure::{closure_mst, BottleneckForest, SdClosure};
use super::ReducibleGraph;

/// Per-vertex memory of the star last seen to fail the test.
///
/// `None` means "must be tested". See the module comment for why a matching
/// signature is a proof that the test would fail again.
pub struct StarWatch {
    failed_signature: Vec<Option<u64>>,
    /// Whether the recorded failures were produced with the multi-hop chain
    /// bound. A failure under the weak bound proves nothing about the strong one.
    chains: bool,
}

impl StarWatch {
    pub fn new(num_nodes: usize) -> Self {
        Self { failed_signature: vec![None; num_nodes + 1], chains: false }
    }

    /// Forget everything. Required after any reduction that can shorten
    /// distances or enlarge the terminal set.
    pub fn invalidate_all(&mut self) {
        self.failed_signature.iter_mut().for_each(|s| *s = None);
    }

    /// Drop the memory when the bound about to be used is not the one that
    /// produced it.
    fn set_mode(&mut self, chains: bool) {
        if self.chains != chains {
            self.chains = chains;
            self.invalidate_all();
        }
    }

    fn is_clean(&self, v: NodeId, signature: u64) -> bool {
        self.failed_signature.get(v as usize).copied().flatten() == Some(signature)
    }

    fn mark_failed(&mut self, v: NodeId, signature: u64) {
        if let Some(slot) = self.failed_signature.get_mut(v as usize) {
            *slot = Some(signature);
        }
    }
}

/// FNV-1a over the sorted `(neighbour, cost)` pairs of `v`'s live star.
///
/// A collision costs a skipped re-test, never an unsound deletion: the test
/// itself is unchanged, this only decides whether to run it.
fn star_signature(csr: &Csr, v: NodeId, scratch: &mut Vec<(NodeId, u64)>) -> u64 {
    scratch.clear();
    scratch.extend(
        csr.neighbors(v).filter(|&(u, _, _)| !csr.is_masked(u)).map(|(u, c, _)| (u, c.to_bits())),
    );
    scratch.sort_unstable();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &(u, c) in scratch.iter() {
        h = (h ^ u as u64).wrapping_mul(0x0000_0100_0000_01b3);
        h = (h ^ c).wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// Only vertices of degree at most this are examined. The number of subsets to
/// check grows as `2^k` and the star cost grows with `k`, so high-degree
/// vertices are both expensive to test and unlikely to pass.
const MAX_DEGREE: usize = 8;

/// One sweep with no memory of previous sweeps.
pub fn vertex_reductions(graph: &mut ReducibleGraph, deadline: Option<Instant>) -> u32 {
    let mut watch = StarWatch::new(graph.nodes.iter().map(|n| n.id as usize).max().unwrap_or(0));
    vertex_reductions_watched(graph, deadline, &mut watch, &mut None)
}

pub fn vertex_reductions_watched(
    graph: &mut ReducibleGraph,
    deadline: Option<Instant>,
    watch: &mut StarWatch,
    hops_cache: &mut Option<ChainHops>,
) -> u32 {
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

    // The transplanted-hop machinery, or nothing. See the module comment; the
    // work bound is shared with the edge test so the two agree about what fits.
    //
    // Whether it *will* be built is a pure size predicate, so the watch can be
    // told before it is consulted; the `|R|` Dijkstras it needs are deferred
    // until a candidate actually survives the watch. Most rounds of a long
    // fixpoint have none, and paying for them unconditionally cost PACE
    // instance197 its whole reduction budget.
    let chains = SdClosure::affordable(csr.num_nodes, terminals.len());
    watch.set_mode(chains);
    if !chains {
        *hops_cache = None;
    }
    let mut hops_ready = !chains;
    let mut chain_scratch = ChainScratch::default();

    let candidates: Vec<NodeId> = graph
        .nodes
        .iter()
        .map(|n| n.id)
        .filter(|&v| graph.is_node_valid(v) && !graph.is_terminal(v))
        .collect();

    let mut removed = 0;
    let mut scratch: Vec<(NodeId, u64)> = Vec::new();
    for (seen, v) in candidates.into_iter().enumerate() {
        // The per-candidate cost is a handful of bounded Dijkstras, so checking
        // the clock every few hundred candidates is granular enough.
        if seen % 256 == 0 && deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        if csr.is_masked(v) {
            continue;
        }
        let signature = star_signature(&csr, v, &mut scratch);
        if watch.is_clean(v, signature) {
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
        // Both of these depend on the star alone, so they are failures the
        // signature fully accounts for.
        if !(3..=MAX_DEGREE).contains(&k) {
            watch.mark_failed(v, signature);
            continue;
        }

        let radius: Cost = star.iter().map(|&(_, c)| c).sum();
        if !radius.is_finite() {
            watch.mark_failed(v, signature);
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
        // Chains of length two and above, when the sweep is carrying the forest.
        if !hops_ready {
            hops_ready = true;
            ChainHops::refresh(hops_cache, graph, &csr, &terminals);
        }
        if let Some(ref h) = *hops_cache {
            h.tighten(v, &dist, base, k, &mut sd, &mut chain_scratch);
        }

        if !star_is_dominated(&star, &sd, k) {
            watch.mark_failed(v, signature);
            continue;
        }

        csr.mask(v);
        graph.remove_node(v);
        // The fixed shortest paths are paths of `G`; the ones running through a
        // vertex this sweep has deleted are no longer available to any later
        // candidate, so they leave the forest permanently.
        if let Some(ref mut h) = *hops_cache {
            h.retire(v);
        }
        removed += 1;
    }

    removed
}

/// Scratch buffers for [`ChainHops::tighten`], reused across candidates.
#[derive(Default)]
struct ChainScratch {
    edges: Vec<(Cost, usize, usize)>,
    forest: Option<BottleneckForest>,
    uf: Vec<u32>,
    blocked: Vec<bool>,
    /// Terminal indices each star member can actually reach inside the truncation
    /// radius.
    reach: Vec<Vec<u32>>,
    g: Vec<Cost>,
    m: Vec<Cost>,
    acc: Vec<Cost>,
}

/// The fixed spanning tree of the terminal metric closure, with one realising
/// path recorded per edge, indexed by the vertices those paths pass through.
///
/// See the module comment for the lemma this implements.
pub struct ChainHops {
    /// The terminals this was built for, in index order. A changed terminal set
    /// changes what the leaves mean, so it forces a rebuild.
    terminals: Vec<NodeId>,
    /// MST edges as `(weight, i, j)` over terminal indices, sorted by weight.
    edges: Vec<(Cost, usize, usize)>,
    /// The realising path of each MST edge: its interior vertices and the graph
    /// edges it traverses. Kept so the witness can be *re-checked* against a
    /// later graph rather than recomputed.
    path: Vec<Path>,
    /// Edge indices whose realising path passes through a given vertex.
    through: Vec<Vec<u32>>,
    /// Edges whose witness is gone: the path met a deleted vertex or edge, or it
    /// could not be reconstructed. Permanently unusable until the next rebuild.
    retired: Vec<bool>,
    live: usize,
}

#[derive(Default, Clone)]
struct Path {
    nodes: Vec<u32>,
    edges: Vec<u32>,
}

/// Path entries recorded across all realising paths. Exceeding this abandons the
/// structure: the bound is optional and a sweep must not be dominated by
/// bookkeeping for it.
const MAX_PATH_ENTRIES: usize = 4_000_000;

impl ChainHops {
    /// Reuse the cached forest if its witnesses still exist in `graph`, rebuild
    /// otherwise.
    ///
    /// # Why the cache is sound
    ///
    /// The lemma needs each surviving MST edge to be realised by a path *of the
    /// current graph* of exactly the recorded weight. [`ChainHops::revalidate`]
    /// checks precisely that — every vertex and every edge of the recorded path
    /// still live — and retires the edges that fail. Costs never change, so a
    /// path that still exists still costs what it cost.
    ///
    /// # Why it is rebuilt when it is
    ///
    /// Rebuilding costs `|R|` Dijkstras and re-validating costs one pass over the
    /// recorded paths, so the cache is what makes this test affordable at all: on
    /// PACE instance197 the reduction fixpoint calls the vertex test 109 times,
    /// and rebuilding every time cost 4.2 of the 5.5 seconds it then took. A
    /// rebuild is forced only when the terminal set changed — which invalidates
    /// the leaf indexing outright — or when at least half the forest has been
    /// retired, so the rebuilds a fixpoint pays for are bounded by the halvings
    /// the forest can undergo rather than by the number of rounds.
    fn refresh(cache: &mut Option<Self>, graph: &ReducibleGraph, csr: &Csr, terminals: &[NodeId]) {
        if let Some(h) = cache.as_mut() {
            if h.terminals == terminals {
                h.revalidate(graph);
                if h.live * 2 >= h.edges.len() {
                    return;
                }
            }
        }
        *cache = Self::build(csr, terminals);
    }

    /// Retire every MST edge whose recorded witness no longer lies in `graph`.
    fn revalidate(&mut self, graph: &ReducibleGraph) {
        self.live = 0;
        for e in 0..self.edges.len() {
            if self.retired[e] {
                continue;
            }
            let p = &self.path[e];
            let ok = p.nodes.iter().all(|&v| graph.is_node_valid(v))
                && p.edges.iter().all(|&f| graph.is_edge_valid(f));
            if ok {
                self.live += 1;
            } else {
                self.retired[e] = true;
            }
        }
    }

    fn build(csr: &Csr, terminals: &[NodeId]) -> Option<Self> {
        let k = terminals.len();
        // Same predicate as the edge test's, so the two strengthenings switch on
        // and off together and a single work bound governs both.
        if !SdClosure::affordable(csr.num_nodes, k) {
            return None;
        }
        let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();
        let edges = closure_mst(k, |i, j| dist[i][terminals[j] as usize]);

        let mut through: Vec<Vec<u32>> = vec![Vec::new(); csr.num_nodes];
        let mut retired = vec![false; edges.len()];
        let mut path = vec![Path::default(); edges.len()];
        let mut entries = 0usize;
        let mut live = 0usize;
        for (e, &(_, i, j)) in edges.iter().enumerate() {
            // Walk back from `terminals[j]` along the distance function of
            // `terminals[i]`, which is the standard shortest-path reconstruction.
            let d = &dist[i];
            let (src, dst) = (terminals[i], terminals[j]);
            let mut x = dst;
            let mut steps = 0usize;
            let ok = loop {
                if x == src {
                    break true;
                }
                // Zero-cost edges make the distance function non-strictly
                // decreasing, so a step counter is the termination guarantee.
                if steps > csr.num_nodes {
                    break false;
                }
                steps += 1;
                let mut next = u32::MAX;
                let mut via = u32::MAX;
                for (y, c, f) in csr.neighbors(x) {
                    if csr.is_masked(y) {
                        continue;
                    }
                    if (d[y as usize] + c - d[x as usize]).abs() < 1e-9 {
                        next = y;
                        via = f;
                        break;
                    }
                }
                if next == u32::MAX {
                    break false;
                }
                path[e].edges.push(via);
                entries += 1;
                if next != src {
                    through[next as usize].push(e as u32);
                    path[e].nodes.push(next);
                    entries += 1;
                }
                if entries > MAX_PATH_ENTRIES {
                    return None;
                }
                x = next;
            };
            if ok {
                live += 1;
            } else {
                // No reconstruction means no witness, so the edge may never be
                // transplanted. Dropping it only weakens the bound.
                retired[e] = true;
            }
        }

        Some(Self { terminals: terminals.to_vec(), edges, path, through, retired, live })
    }

    /// Mark every edge whose path used `v` as permanently unusable.
    fn retire(&mut self, v: NodeId) {
        for &e in &self.through[v as usize] {
            if !self.retired[e as usize] {
                self.retired[e as usize] = true;
                self.live -= 1;
            }
        }
    }

    /// Lower every `sd[i * k + j]` to the multi-hop chain bound for candidate `v`.
    ///
    /// `dist[i][0..base]` must hold `d_{G-v}(star_i, terminal_t)`.
    fn tighten(
        &self,
        v: NodeId,
        dist: &[Vec<Cost>],
        base: usize,
        k: usize,
        sd: &mut [Cost],
        scratch: &mut ChainScratch,
    ) {
        debug_assert_eq!(base, self.terminals.len());
        // Every search was truncated at the star's own cost, so on a sparse graph
        // most terminals are simply out of range and contribute nothing but an
        // infinity. Collecting the reachable ones first turns the `O(k^2 |R|)`
        // minimisation below into `O(k^2 |reachable|)`, and lets a candidate that
        // reaches no terminal at all skip the forest entirely — which is the
        // common case, and the difference between this test costing a fifth of the
        // reduction budget and costing five times it.
        scratch.reach.clear();
        scratch.reach.resize(k, Vec::new());
        let mut any = false;
        for i in 0..k {
            let r = &mut scratch.reach[i];
            r.clear();
            for t in 0..base {
                if dist[i][t].is_finite() {
                    r.push(t as u32);
                }
            }
            any |= !r.is_empty();
        }
        if !any {
            return;
        }

        // The forest of hops that survive both this candidate and every earlier
        // deletion. `edges` is already weight-sorted, and filtering preserves it.
        scratch.blocked.clear();
        scratch.blocked.resize(self.edges.len(), false);
        for &e in &self.through[v as usize] {
            scratch.blocked[e as usize] = true;
        }
        scratch.edges.clear();
        for (e, &edge) in self.edges.iter().enumerate() {
            if !self.retired[e] && !scratch.blocked[e] {
                scratch.edges.push(edge);
            }
        }
        let forest = scratch.forest.get_or_insert_with(|| BottleneckForest::build(0, &[]));
        forest.rebuild(base, &scratch.edges, &mut scratch.uf);

        scratch.g.clear();
        scratch.g.resize(k * base, Cost::INFINITY);
        for i in 0..k {
            // A star member that reaches no terminal has an all-infinite row, and
            // the half-closure of an all-infinite row is all infinite.
            if scratch.reach[i].is_empty() {
                continue;
            }
            forest.half_closure(
                &dist[i][..base],
                &mut scratch.g[i * base..(i + 1) * base],
                &mut scratch.m,
                &mut scratch.acc,
            );
        }
        for i in 0..k {
            if scratch.reach[i].is_empty() {
                continue;
            }
            for j in 0..k {
                if j == i {
                    continue;
                }
                // `max(g_i(t), d(b, t))` is infinite unless `b` reaches `t`, so
                // only `b`'s own reachable set can contribute.
                let mut best = sd[i * k + j];
                for &t in &scratch.reach[j] {
                    let cand = scratch.g[i * base + t as usize].max(dist[j][t as usize]);
                    if cand < best {
                        best = cand;
                    }
                }
                if best < sd[i * k + j] {
                    sd[i * k + j] = best;
                    sd[j * k + i] = best;
                }
            }
        }
    }
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

    /// The transplanted-hop bound must delete a vertex the zero/one-hop bound
    /// keeps, or it is not buying anything.
    ///
    /// Terminals 1-2-3-4 lie on a path with unit-4 spacing; `5`, `6` and `7` hang
    /// off terminals 1, 4 and 2 at cost 4; and the Steiner hub `8` joins all three
    /// at cost 5. The pair `{5,6}` has budget 10, one-hop special distance 12 —
    /// no single terminal is within 10 of both — and chain special distance 4,
    /// through the terminal path. So the hub survives the old bound and falls to
    /// the new one.
    #[test]
    fn a_chain_deletes_a_hub_the_one_hop_bound_keeps() {
        let mut g = UndirectedGraph::new(8);
        for v in 1..=4u32 {
            g.add_node(v, NodeType::Terminal, 0.0);
        }
        for v in 5..=8u32 {
            g.add_node(v, NodeType::Steiner, 0.0);
        }
        g.add_edge(1, 2, 4.0);
        g.add_edge(2, 3, 4.0);
        g.add_edge(3, 4, 4.0);
        g.add_edge(5, 1, 4.0);
        g.add_edge(6, 4, 4.0);
        g.add_edge(7, 2, 4.0);
        g.add_edge(8, 5, 5.0);
        g.add_edge(8, 6, 5.0);
        g.add_edge(8, 7, 5.0);

        let inst = instance(&g, vec![1, 2, 3, 4]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);

        // The one-hop bound on the pair that decides it, in `G - 8`.
        let mut csr = Csr::build(&rg);
        csr.mask(8);
        let (d5, d6) = (csr.dijkstra(5), csr.dijkstra(6));
        let one_hop = (1..=4u32)
            .map(|t| d5[t as usize].max(d6[t as usize]))
            .fold(d5[6], Cost::min);
        assert!(one_hop > 10.0 + 1e-9, "one-hop bound {one_hop} should not reach the budget 10");

        assert_eq!(vertex_reductions(&mut rg, None), 1, "the hub should go");
        assert!(!rg.is_node_valid(8));
    }

    /// The same exhaustive gate as [`never_changes_the_optimum`], on graphs large
    /// enough that chains of length two and above are actually reachable: up to
    /// ten vertices and six terminals, which the one-hop-only regime never
    /// exercised.
    #[test]
    fn chains_never_change_the_optimum() {
        let mut seed = 0xC4A1_0F5D_2026_0801u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        let mut ran = 0;
        for _ in 0..4000 {
            let n = 7 + (rng() % 4) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 3 + (rng() % 4) as u32;
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
                    // Sparse enough that brute force stays inside its 20-edge
                    // ceiling most of the time.
                    if rng() % 5 == 0 {
                        let c = 1.0 + (rng() % 9) as f64;
                        g.add_edge(u, v, c);
                        edges.push((u, v, c));
                    }
                }
            }
            let Some(before) = brute(n, &edges, &terminals) else { continue };
            ran += 1;

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
        assert!(ran > 500, "only {ran} cases were actually checked");
    }

    /// Deleting vertices one at a time must keep the cached witness forest
    /// honest: a hop whose recorded path runs through a deleted vertex may not be
    /// transplanted again.
    #[test]
    fn a_retired_hop_is_not_reused() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        for _ in 0..600 {
            let n = 8 + (rng() % 3) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 3 + (rng() % 3) as u32;
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
                    if rng() % 6 != 0 && edges.len() < 15 {
                        let c = 1.0 + (rng() % 5) as f64;
                        g.add_edge(u, v, c);
                        edges.push((u, v, c));
                    }
                }
            }
            let Some(before) = brute(n, &edges, &terminals) else { continue };
            ran += 1;

            let inst = instance(&g, terminals.clone());
            let mut rg = ReducibleGraph::from_instance(&inst, &g);
            // Several sweeps through one cache, which is how the reduction loop
            // uses it.
            let mut watch = StarWatch::new(n as usize);
            let mut hops = None;
            for _ in 0..4 {
                watch.invalidate_all();
                vertex_reductions_watched(&mut rg, None, &mut watch, &mut hops);
            }

            let kept: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let after = brute(n, &kept, &terminals).unwrap_or(Cost::INFINITY);
            assert!(
                (after - before).abs() < 1e-9,
                "repeated sweeps changed the optimum: {before} -> {after}"
            );
        }
        assert!(ran > 100, "only {ran} cases were actually checked");
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
