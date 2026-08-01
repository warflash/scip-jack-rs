//! Goal-directed exact Steiner tree search: Dijkstra-Steiner with A* guidance.
//!
//! Dreyfus-Wagner computes `l(v, I)` — the cheapest tree containing `v` and the
//! terminal set `I` — for *every* one of the `n * 2^k` states. That is the wrong
//! shape for an instance where only a thin corridor of states can possibly lie
//! on an optimal tree. Hougardy, Silvanus and Vygen's Dijkstra-Steiner algorithm
//! keeps the same recurrence but settles states in order of `l + L`, where `L`
//! estimates the cost still to come, and stops the moment the goal state is
//! settled. With a good `L` the explored fraction of the state space collapses.
//!
//! This matters here because of what the unproved instances actually look like.
//! Of the thirteen PACE Track 1 instances in [1..140] the solver could not close
//! at a 3 s limit, twelve have **at most 24 terminals** after reduction, and
//! three of them have nine. Those are not branch-and-cut problems.
//!
//! # The recurrence
//!
//! Fix a root terminal `r0` and write `K = R \ {r0}`. For `v` in `V` and `I` a
//! subset of `K`, `l(v, I)` is the cost of a cheapest tree containing `{v} ∪ I`.
//! Then `smt(R) = l(r0, K)`, and
//!
//! ```text
//! l(v, I) = min ( min over edges {u,v} of  l(u, I) + c(u,v),          [grow]
//!                 min over 0 != J ⊊ I of   l(v, J) + l(v, I \ J) ).   [merge]
//! ```
//!
//! Read as a shortest-path problem on states, `grow` is an ordinary arc and
//! `merge` is a hyperarc with two tails. Settling states in nondecreasing key
//! order makes both correct for the same reason Dijkstra is.
//!
//! # Valid lower bounds
//!
//! Following the paper, `L(v, I)` — with `I` here the set of terminals *still
//! outstanding*, always containing `r0` — is a **valid lower bound** when
//! `L(r0, {r0}) = 0` and
//!
//! ```text
//! L(v, I) <= L(w, I') + smt((I \ I') ∪ {v, w})   for {r0} ⊆ I' ⊆ I ⊆ R.
//! ```
//!
//! Taking `I' = {r0}` and `w = r0` gives `L(v, I) <= smt(I ∪ {v})`, so a valid
//! lower bound really does bound the remaining cost; taking `I' = I` and `w`
//! adjacent to `v` gives `L(v, I) <= L(w, I) + c(v, w)`, which is the
//! consistency condition that makes the search settle states in nondecreasing
//! key order. The maximum of two valid lower bounds is valid, so they compose.
//!
//! Two are used here.
//!
//! ## The farthest-outstanding bound
//!
//! ```text
//! L_far(v, I) = max over t in I of d(v, t).
//! ```
//!
//! *Valid.* `L_far(r0, {r0}) = 0`. For the inequality, let `t*` attain the
//! maximum on the left. If `t*` lies in `I'` then
//! `d(v, t*) <= d(v, w) + d(w, t*) <= smt((I\I') ∪ {v,w}) + L_far(w, I')`,
//! because any tree containing `v` and `w` costs at least `d(v, w)`. Otherwise
//! `t*` lies in `I \ I'`, so it is one of the vertices the tree
//! `smt((I\I') ∪ {v,w})` must contain along with `v`, and that tree already
//! costs at least `d(v, t*)`. ∎
//!
//! ## The 1-tree bound
//!
//! ```text
//! L_1tree(v, I) = min over i != j in I of (d(v,i) + d(v,j)) / 2  +  mst(I) / 2,
//! ```
//!
//! with `mst(I)` the minimum spanning tree of `I` in the metric closure, and the
//! pair `i = j` allowed when `|I| = 1`.
//!
//! *It bounds the remaining cost.* Let `T` be any tree containing `{v} ∪ I`.
//! Doubling every edge of `T` gives a closed walk of cost `2 c(T)` visiting
//! every vertex of `T`; shortcutting it to the vertices of `I ∪ {v}` cannot
//! increase the cost, because shortest-path distances obey the triangle
//! inequality. The result is a tour on `I ∪ {v}` of cost at most `2 c(T)`. That
//! tour enters and leaves `v` by two distinct vertices `i, j` of `I`, and
//! deleting `v` from it leaves a Hamiltonian path on `I` — a spanning tree of
//! `I` — so
//!
//! ```text
//! 2 c(T) >= d(v,i) + d(v,j) + mst(I) >= 2 L_1tree(v, I).
//! ```
//!
//! For `|I| = 1` the tour is the doubled edge `v-r0` and the formula reduces to
//! `d(v, r0)`, which is right. ∎
//!
//! That `L_1tree` satisfies the full valid-lower-bound inequality, and not only
//! the bound above, is Lemma 8 of the paper. The randomised tests at the bottom
//! of this module check the consequence that matters — that the search returns
//! the true optimum — against brute-force enumeration and against the
//! Dreyfus-Wagner implementation next door.
//!
//! `mst(I)` depends only on `I`, so it is cached per outstanding set and the
//! per-state cost of `L` is a single pass over the outstanding terminals.
//!
//! # Pruning against an incumbent
//!
//! If `U >= smt(R)` and a label has `l(v, I) + L(v, R \ I) > U`, no optimal tree
//! contains its tree as the `(v, I)` side of a split, so the label may be
//! dropped (Lemma 14 of the paper: any completion costs at least
//! `smt({v} ∪ (R\I)) >= L(v, R\I)`). The solver always has an incumbent from the
//! primal heuristics by the time this runs, so the cutoff is real.
//!
//! # The dual bound this yields when it does *not* finish
//!
//! The search is given a label budget and a deadline, and abandons itself when
//! either runs out. That is not a wasted run:
//!
//! > **Proposition.** At any point at which the goal state is unsettled, the
//! > minimum key in the open queue is a lower bound on `smt(R)`.
//!
//! *Proof.* Consider an optimal tree and the derivation of `(r0, K)` that builds
//! it. If every state of that derivation were settled, the goal would be too, so
//! some state is unsettled; take one, `s`, all of whose predecessors are
//! settled. Each predecessor was settled with its correct `l`, and settling
//! performs every grow and merge out of it, so `s` was inserted with its
//! correct `l(s)`. Since `L` bounds the remaining cost,
//! `key(s) = l(s) + L(s) <= smt(R)`. The pruning rule cannot have removed `s`,
//! because it only removes labels with key above `U >= smt(R)`. So `s` is in the
//! queue and the minimum key is at most `smt(R)`. ∎
//!
//! So an abandoned search still hands back a combinatorial dual bound, computed
//! without an LP and without dual ascent.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::hash::{BuildHasherDefault, Hasher};
use std::time::Instant;

/// Multiply-shift hasher for the packed `(subset, vertex)` label keys.
///
/// The label maps are the hot structure of the whole search and the keys are
/// already dense integers, so the default SipHash is pure overhead.
#[derive(Default)]
pub struct LabelHasher(u64);

impl Hasher for LabelHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0 ^ b as u64).wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    fn write_u64(&mut self, value: u64) {
        self.0 = value.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        self.0 ^= self.0 >> 29;
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

type LabelMap<V> = HashMap<u64, V, BuildHasherDefault<LabelHasher>>;

/// Storage for the label costs.
///
/// The state space is `n * 2^(k-1)`. When that fits in memory a flat array is
/// the right structure and the search becomes pointer arithmetic; when it does
/// not, the search only ever touches a small corner of it and a hash map is the
/// only option. Both are exact and the choice is invisible to the algorithm.
enum Labels {
    Dense { cost: Vec<Cost>, settled: Vec<bool>, num_nodes: usize },
    Sparse(LabelMap<(Cost, bool)>),
}

impl Labels {
    /// Entries a dense table may hold. Beyond this the table costs more than the
    /// hashing it saves, and the search would not finish anyway.
    const DENSE_CAP: usize = 12_000_000;

    fn new(num_nodes: usize, num_masks: usize) -> Self {
        match num_nodes.checked_mul(num_masks) {
            Some(cells) if cells <= Self::DENSE_CAP => Labels::Dense {
                cost: vec![Cost::INFINITY; cells],
                settled: vec![false; cells],
                num_nodes,
            },
            _ => Labels::Sparse(LabelMap::default()),
        }
    }

    #[inline]
    fn get(&self, mask: u32, v: NodeId) -> Option<(Cost, bool)> {
        match self {
            Labels::Dense { cost, settled, num_nodes } => {
                let i = mask as usize * *num_nodes + v as usize;
                let c = cost[i];
                c.is_finite().then(|| (c, settled[i]))
            }
            Labels::Sparse(map) => map.get(&pack(mask, v)).copied(),
        }
    }

    #[inline]
    fn put(&mut self, mask: u32, v: NodeId, value: Cost, done: bool) {
        match self {
            Labels::Dense { cost, settled, num_nodes } => {
                let i = mask as usize * *num_nodes + v as usize;
                cost[i] = value;
                settled[i] = done;
            }
            Labels::Sparse(map) => {
                map.insert(pack(mask, v), (value, done));
            }
        }
    }
}

#[inline]
fn pack(mask: u32, v: NodeId) -> u64 {
    ((mask as u64) << 32) | v as u64
}

use crate::graph::{Cost, NodeId, UndirectedGraph};

/// Largest terminal count the bitmask state can address.
const MAX_TERMINALS: usize = 32;

#[derive(Debug, Clone)]
pub struct DijkstraSteinerResult {
    /// The optimum, when the search ran to completion.
    pub optimal: Option<Cost>,
    /// A valid lower bound on the optimum, whether or not it completed.
    pub lower_bound: Cost,
    pub labels_settled: u64,
}

/// Ordering shim for `f64` keys in the priority queue.
#[derive(PartialEq, PartialOrd)]
struct Key(Cost);
impl Eq for Key {}
#[allow(clippy::derive_ord_xor_partial_ord)]
impl Ord for Key {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// A cut packing turned into an A* potential.
///
/// # The bound
///
/// Dual ascent produces non-negative weights `y_W` on vertex sets `W` with
/// `r0 ∉ W`, satisfying the packing condition
///
/// ```text
/// sum { y_W : a enters W } <= c(a)      for every arc a,
/// ```
///
/// which is what makes `sum_W y_W` a lower bound on the whole instance. The
/// observation here is that the same packing bounds every *sub*-requirement too.
/// For a vertex `v` and a set `S` of vertices that still have to be joined to
/// `v`, define
///
/// ```text
/// L_pack(v, S) = sum { y_W : W meets S ∪ {v} }.
/// ```
///
/// **Claim.** `L_pack(v, S) <= smt(S ∪ {v})` whenever `r0 ∈ S`.
///
/// *Proof.* Let `T` be a tree containing `S ∪ {v}`, oriented away from `r0`.
/// Every `W` counted by `L_pack` meets `S ∪ {v} ⊆ V(T)` and misses `r0 ∈ V(T)`,
/// so `T` has a vertex inside `W` and a vertex outside it, hence an arc entering
/// `W`. Charging each such `W` to one such arc,
///
/// ```text
/// sum { y_W : W meets S ∪ {v} }
///   <= sum over a in T of sum { y_W : a enters W }
///   <= sum over a in T of c(a) = c(T).   ∎
/// ```
///
/// This is far stronger than any metric-closure bound. The 1-tree bound gives up
/// a factor of two by construction, because it goes through a tour; dual ascent
/// routinely reaches 90-99% of the optimum, and that strength transfers directly
/// to every state of the search.
///
/// # Why it is a *valid* lower bound and not merely a bound
///
/// A* needs more than admissibility: it needs the key to be monotone along both
/// kinds of transition. Both follow from the packing condition, and neither needs
/// anything else.
///
/// **Growth,** `(v, I) -> (u, I)` at cost `c(v,u)`. The outstanding set `S` is
/// unchanged, so
/// `L_pack(v, S) - L_pack(u, S) = sum { y_W : W misses S, v ∈ W, u ∉ W }`.
/// Every such `W` is entered by the arc `(u, v)`, so the sum is at most
/// `c(u, v)` by the packing condition. Hence
/// `L_pack(v, S) <= c(v,u) + L_pack(u, S)`.
///
/// **Merge,** `(v, I)` and `(v, J)` into `(v, I ∪ J)`, whose outstanding sets
/// satisfy `S(I) = S(I ∪ J) ∪ J`. Then
/// `L_pack(v, S(I)) - L_pack(v, S(I∪J)) = sum { y_W : W meets J, W misses
/// S(I∪J), v ∉ W }`. Each such `W` is met by the tree behind `(v, J)` — it
/// contains a terminal of `J` — and missed by `v`, so that tree crosses into `W`
/// and the same charging argument bounds the sum by `l(v, J)`.
///
/// **At the goal,** `S = {r0}` and no raised set contains `r0`, so the potential
/// is zero. ∎
///
/// # Evaluation
///
/// Splitting on whether a set is witnessed by a terminal or by `v` alone,
///
/// ```text
/// L_pack(v, S) = sum { y_W : mask(W) meets S }        [depends only on S]
///              + sum { y_W : mask(W) misses S, v ∈ W }.
/// ```
///
/// The first term is grouped by the distinct terminal masks of the raised sets,
/// of which there are few, and the second runs over the sets containing `v`,
/// which is a short list per vertex. Both are a handful of operations.
pub struct PackingPotential {
    /// Distinct terminal masks among the raised sets, with their total weight.
    by_mask: Vec<(u32, Cost)>,
    /// For each vertex, the `(terminal mask, weight)` of every raised set that
    /// contains it.
    at_vertex: Vec<Vec<(u32, Cost)>>,
}

impl PackingPotential {
    /// Build from a dual-ascent packing. `terminal_index[v]` is the index of `v`
    /// in the terminal list, or `u32::MAX`.
    /// `root` is the search's root terminal, and every hypothesis of the proof
    /// above depends on no raised set containing it: the bound charges each set
    /// to an arc of a tree that has a vertex inside the set and the root
    /// outside, and the goal state's potential is zero only because no set
    /// witnesses the root.
    ///
    /// A dual ascent rooted at `root` never produces such a set, but the caller
    /// is free to hand over a packing from any ascent, and one rooted elsewhere
    /// silently breaks both. Rather than trust the caller, sets containing
    /// `root` are dropped here. A sub-family of a packing is still a packing, so
    /// dropping them costs strength and never validity.
    ///
    /// This is not hypothetical. Feeding a packing rooted at the solver's
    /// preferred ascent root, which is chosen for bound strength and is usually
    /// *not* the first terminal, produced dual bounds above the optimum on seven
    /// PACE instances and reported them as proved.
    pub fn new(
        sets: &[(Cost, Vec<NodeId>)],
        terminal_index: &[u32],
        num_nodes: usize,
        root: NodeId,
    ) -> Self {
        let mut grouped: HashMap<u32, Cost> = HashMap::new();
        let mut at_vertex: Vec<Vec<(u32, Cost)>> = vec![Vec::new(); num_nodes];
        for (weight, members) in sets {
            if *weight <= 0.0 || members.contains(&root) {
                continue;
            }
            let mut mask = 0u32;
            for &v in members {
                if let Some(&i) = terminal_index.get(v as usize) {
                    if i != u32::MAX {
                        mask |= 1u32 << i;
                    }
                }
            }
            *grouped.entry(mask).or_insert(0.0) += *weight;
            for &v in members {
                if (v as usize) < num_nodes {
                    at_vertex[v as usize].push((mask, *weight));
                }
            }
        }
        // Sets containing `v` that share a terminal mask are tested by the same
        // predicate and contribute additively, so summing them is exact. It also
        // bounds the per-vertex list by the number of distinct masks instead of
        // by the number of raised sets, which on a dense graph is the difference
        // between a handful of operations per state and thousands.
        for list in at_vertex.iter_mut() {
            if list.len() < 2 {
                continue;
            }
            list.sort_unstable_by_key(|&(m, _)| m);
            let mut merged: Vec<(u32, Cost)> = Vec::with_capacity(list.len());
            for &(m, w) in list.iter() {
                match merged.last_mut() {
                    Some(last) if last.0 == m => last.1 += w,
                    _ => merged.push((m, w)),
                }
            }
            *list = merged;
        }
        Self { by_mask: grouped.into_iter().collect(), at_vertex }
    }

    /// The part of the bound that depends only on the outstanding set. Every
    /// neighbour reached by a growth step shares it, and on a graph of average
    /// degree several hundred that is the whole cost of the evaluation.
    fn shared(&self, outstanding: u32) -> Cost {
        let mut total = 0.0;
        for &(mask, weight) in &self.by_mask {
            if mask & outstanding != 0 {
                total += weight;
            }
        }
        total
    }

    fn value(&self, v: NodeId, outstanding: u32, shared: Cost) -> Cost {
        let mut total = shared;
        if let Some(list) = self.at_vertex.get(v as usize) {
            for &(mask, weight) in list {
                if mask & outstanding == 0 {
                    total += weight;
                }
            }
        }
        total
    }
}

struct Csr {
    start: Vec<u32>,
    head: Vec<u32>,
    cost: Vec<Cost>,
    num_nodes: usize,
}

impl Csr {
    fn build(graph: &UndirectedGraph) -> Self {
        let num_nodes = graph.nodes.iter().map(|n| n.id as usize).max().unwrap_or(0) + 1;
        let mut degree = vec![0u32; num_nodes + 1];
        for e in &graph.edges {
            if e.src == e.dst {
                continue;
            }
            degree[e.src as usize + 1] += 1;
            degree[e.dst as usize + 1] += 1;
        }
        for i in 0..num_nodes {
            degree[i + 1] += degree[i];
        }
        let start = degree.clone();
        let mut fill = start.clone();
        let mut head = vec![0u32; graph.edges.len() * 2];
        let mut cost = vec![0.0; graph.edges.len() * 2];
        for e in &graph.edges {
            if e.src == e.dst {
                continue;
            }
            let i = fill[e.src as usize] as usize;
            head[i] = e.dst;
            cost[i] = e.cost;
            fill[e.src as usize] += 1;
            let j = fill[e.dst as usize] as usize;
            head[j] = e.src;
            cost[j] = e.cost;
            fill[e.dst as usize] += 1;
        }
        Self { start, head, cost, num_nodes }
    }

    fn neighbors(&self, v: NodeId) -> impl Iterator<Item = (NodeId, Cost)> + '_ {
        let (s, e) = (self.start[v as usize] as usize, self.start[v as usize + 1] as usize);
        (s..e).map(move |i| (self.head[i], self.cost[i]))
    }

    fn dijkstra(&self, source: NodeId) -> Vec<Cost> {
        let mut dist = vec![Cost::INFINITY; self.num_nodes];
        let mut heap: BinaryHeap<(Reverse<Key>, u32)> = BinaryHeap::new();
        dist[source as usize] = 0.0;
        heap.push((Reverse(Key(0.0)), source));
        while let Some((Reverse(Key(d)), v)) = heap.pop() {
            if d > dist[v as usize] + 1e-12 {
                continue;
            }
            for (u, c) in self.neighbors(v) {
                let nd = d + c;
                if nd < dist[u as usize] - 1e-12 {
                    dist[u as usize] = nd;
                    heap.push((Reverse(Key(nd)), u));
                }
            }
        }
        dist
    }
}

/// Estimated number of label settlings the search will need.
///
/// This is a *shape* estimate used only to decide whether to attempt the search
/// at all; the search itself is bounded and abandons safely, so an optimistic
/// estimate costs time and never correctness.
pub fn work_estimate(num_terminals: usize, num_nodes: u32, num_edges: usize) -> f64 {
    // The `k` Dijkstras of the preprocessing step are unavoidable and are
    // usually what dominates on a sparse graph with few terminals.
    let k = num_terminals as f64;
    let n = num_nodes as f64;
    let m = num_edges as f64;
    k * (m + n * n.max(2.0).log2())
}

/// Exact Steiner tree by goal-directed search.
///
/// Returns `None` when the instance is out of the addressable range or the
/// terminals are not all in one component. Otherwise the result always carries a
/// valid `lower_bound`, and carries `optimal` when the search finished.
pub fn dijkstra_steiner(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    upper_bound: Cost,
    label_budget: u64,
    deadline: Option<Instant>,
) -> Option<DijkstraSteinerResult> {
    dijkstra_steiner_guided(graph, terminals, upper_bound, label_budget, deadline, None)
}

/// [`dijkstra_steiner`] with a dual-ascent packing supplying the potential.
pub fn dijkstra_steiner_guided(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    upper_bound: Cost,
    label_budget: u64,
    deadline: Option<Instant>,
    packing: Option<&[(Cost, Vec<NodeId>)]>,
) -> Option<DijkstraSteinerResult> {
    let k = terminals.len();
    if !(2..=MAX_TERMINALS).contains(&k) {
        return None;
    }
    let csr = Csr::build(graph);
    if terminals.iter().any(|&t| (t as usize) >= csr.num_nodes) {
        return None;
    }

    // Distances from every terminal. These serve the lower bound, the terminal
    // metric closure, and nothing else.
    let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();
    for i in 1..k {
        if !dist[0][terminals[i] as usize].is_finite() {
            return None; // terminals split across components
        }
    }

    // Terminal metric closure, for the spanning trees inside the 1-tree bound.
    let mut td = vec![vec![0.0 as Cost; k]; k];
    for i in 0..k {
        for j in 0..k {
            td[i][j] = dist[i][terminals[j] as usize];
        }
    }

    let potential = packing.map(|sets| {
        let mut terminal_index = vec![u32::MAX; csr.num_nodes];
        for (i, &t) in terminals.iter().enumerate() {
            terminal_index[t as usize] = i as u32;
        }
        PackingPotential::new(sets, &terminal_index, csr.num_nodes, terminals[0])
    });

    let root_bit = 1u32;
    let all_labels: u32 = if k == 32 { !1u32 } else { ((1u32 << k) - 1) & !1 };
    let goal_key = ((all_labels as u64) << 32) | terminals[0] as u64;

    let mut state = Search {
        csr: &csr,
        dist: &dist,
        td: &td,
        k,
        root_bit,
        potential,
        mask_cache: HashMap::new(),
        mst_cache: HashMap::new(),
        label: Labels::new(csr.num_nodes, 1usize << (k - 1)),
        settled_masks: vec![Vec::new(); csr.num_nodes],
        heap: BinaryHeap::new(),
        upper_bound,
    };

    // Base labels: the singleton tree at each non-root terminal.
    for (i, &t) in terminals.iter().enumerate().skip(1) {
        let mask = 1u32 << i;
        state.offer(t, mask, 0.0);
    }

    let mut settled_count = 0u64;
    let mut lower_bound: Cost = 0.0;
    let mut optimal = None;

    while let Some((Reverse(Key(key)), packed)) = state.heap.pop() {
        let mask = (packed >> 32) as u32;
        let v = (packed & 0xFFFF_FFFF) as u32;
        let g = match state.label.get(mask >> 1, v) {
            Some((_, true)) => continue, // already settled
            Some((g, false)) => g,
            None => continue,
        };
        // Stale heap entry from a superseded relaxation.
        if key > g + state.heuristic(v, mask) + 1e-9 {
            continue;
        }

        // Everything still in the queue has key at least this one, so this is
        // the frontier value the proposition above refers to.
        lower_bound = lower_bound.max(key);

        if packed == goal_key {
            optimal = Some(g);
            break;
        }

        state.label.put(mask >> 1, v, g, true);
        state.settled_masks[v as usize].push((mask, g));
        settled_count += 1;

        if settled_count >= label_budget
            || (settled_count % 4096 == 0 && deadline.is_some_and(|d| Instant::now() >= d))
        {
            break;
        }

        // Grow along an edge.
        for (u, c) in state.csr.neighbors(v) {
            state.offer(u, mask, g + c);
        }

        // Merge with every disjoint set already settled at this vertex.
        // No de-duplication is needed or wanted: `other` was settled strictly
        // earlier, so this is the first and only moment at which both halves of
        // the pair are settled. Filtering on which half owns the lowest bit --
        // the Dreyfus-Wagner trick -- silently drops every merge whose partner
        // happens to hold it.
        let partners = std::mem::take(&mut state.settled_masks[v as usize]);
        for &(other, g_other) in &partners {
            if other & mask == 0 {
                state.offer(v, mask | other, g + g_other);
            }
        }
        state.settled_masks[v as usize] = partners;
    }

    // A completed search proves its own value; an abandoned one still leaves the
    // frontier, and the optimum is never below zero.
    if let Some(opt) = optimal {
        lower_bound = opt;
    }

    Some(DijkstraSteinerResult { optimal, lower_bound, labels_settled: settled_count })
}

struct Search<'a> {
    csr: &'a Csr,
    dist: &'a [Vec<Cost>],
    td: &'a [Vec<Cost>],
    k: usize,
    root_bit: u32,
    potential: Option<PackingPotential>,
    /// `(mst(out) / 2, packing shared term)` per outstanding set.
    mask_cache: HashMap<u32, (Cost, Cost)>,
    mst_cache: HashMap<u32, Cost>,
    /// Cost of each reached label, and whether it has been settled.
    label: Labels,
    /// Settled labels per vertex, carrying their cost so the merge loop needs no
    /// lookup at all. This is the inner loop of the entire search: every
    /// settlement scans it, so it is quadratic in the labels settled at a vertex
    /// and a hash probe per entry is what made a 125-vertex instance take
    /// seconds.
    settled_masks: Vec<Vec<(u32, Cost)>>,
    heap: BinaryHeap<(Reverse<Key>, u64)>,
    upper_bound: Cost,
}

impl Search<'_> {
    /// Offer `value` as the cost of the label `(v, mask)`.
    fn offer(&mut self, v: NodeId, mask: u32, value: Cost) {
        if self.label.get(mask >> 1, v).is_some_and(|(old, done)| done || old <= value + 1e-12) {
            return;
        }
        let h = self.heuristic(v, mask);
        // Lemma 14: no optimal tree can use a label whose own cost plus a lower
        // bound on the rest already exceeds a known feasible value.
        if value + h > self.upper_bound + 1e-9 {
            return;
        }
        self.label.put(mask >> 1, v, value, false);
        self.heap.push((Reverse(Key(value + h)), pack(mask, v)));
    }

    /// The outstanding terminal set of a label: the root plus everything the
    /// label has not yet collected.
    fn outstanding(&self, mask: u32) -> u32 {
        let all: u32 = if self.k == 32 { u32::MAX } else { (1u32 << self.k) - 1 };
        (all & !mask) | self.root_bit
    }

    fn heuristic(&mut self, v: NodeId, mask: u32) -> Cost {
        let out = self.outstanding(mask);
        let mut first = Cost::INFINITY;
        let mut second = Cost::INFINITY;
        let mut farthest: Cost = 0.0;
        let mut count = 0usize;
        let mut bits = out;
        while bits != 0 {
            let i = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            count += 1;
            let d = self.dist[i][v as usize];
            if !d.is_finite() {
                return Cost::INFINITY;
            }
            if d < first {
                second = first;
                first = d;
            } else if d < second {
                second = d;
            }
            if d > farthest {
                farthest = d;
            }
        }
        let (mst_half, shared) = match self.mask_cache.get(&out) {
            Some(&pair) => pair,
            None => {
                let mst_half = self.mst(out) / 2.0;
                let shared = self.potential.as_ref().map_or(0.0, |p| p.shared(out));
                self.mask_cache.insert(out, (mst_half, shared));
                (mst_half, shared)
            }
        };
        // The 1-tree bound. With one outstanding terminal the tour degenerates
        // to the doubled edge and the pair `i = j` is the right reading.
        let pair = if count <= 1 { first } else { (first + second) / 2.0 };
        let mut best = (pair + mst_half).max(farthest);
        // The maximum of valid lower bounds is a valid lower bound, so the
        // packing bound simply joins the others.
        if let Some(p) = &self.potential {
            best = best.max(p.value(v, out, shared));
        }
        best
    }

    /// Minimum spanning tree of a terminal subset in the metric closure.
    fn mst(&mut self, mask: u32) -> Cost {
        if let Some(&cached) = self.mst_cache.get(&mask) {
            return cached;
        }
        let members: Vec<usize> = (0..self.k).filter(|&i| mask >> i & 1 == 1).collect();
        let mut total = 0.0;
        if members.len() > 1 {
            // Prim over a handful of terminals; the closure is dense and tiny.
            let n = members.len();
            let mut in_tree = vec![false; n];
            let mut best = vec![Cost::INFINITY; n];
            best[0] = 0.0;
            for _ in 0..n {
                let mut pick = usize::MAX;
                for i in 0..n {
                    if !in_tree[i] && (pick == usize::MAX || best[i] < best[pick]) {
                        pick = i;
                    }
                }
                if pick == usize::MAX || !best[pick].is_finite() {
                    break;
                }
                in_tree[pick] = true;
                total += best[pick];
                for i in 0..n {
                    if !in_tree[i] {
                        let w = self.td[members[pick]][members[i]];
                        if w < best[i] {
                            best[i] = w;
                        }
                    }
                }
            }
        }
        self.mst_cache.insert(mask, total);
        total
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::dreyfus_wagner;
    use crate::graph::NodeType;

    fn random_instance(rng: &mut impl FnMut() -> u64, max_n: u32) -> (UndirectedGraph, Vec<NodeId>) {
        let n = 4 + (rng() % max_n as u64) as u32;
        let mut g = UndirectedGraph::new(n);
        let k = 2 + (rng() % 4) as u32;
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
                    g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
                }
            }
        }
        (g, terminals)
    }

    fn rng_from(mut seed: u64) -> impl FnMut() -> u64 {
        move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }
    }

    fn brute(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
        let m = edges.len();
        if m > 18 {
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

    /// The packing potential must not change the answer, and must not do so for
    /// *any* packing the caller hands over -- including one rooted at the wrong
    /// terminal, which is the mistake that produced dual bounds above the
    /// optimum on seven PACE instances.
    #[test]
    fn guidance_never_changes_the_answer() {
        use crate::graph::algorithms::{dual_ascent_packing, ArcIndex};
        use crate::graph::DirectedGraph;

        let mut rng = rng_from(0x7E57_C0DE_1234_ABCD);
        let mut checked = 0;
        for _ in 0..300 {
            let (g, terminals) = random_instance(&mut rng, 5);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                g.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            let Some(expected) = brute(g.num_nodes, &edges, &terminals) else { continue };

            let directed = DirectedGraph::from_undirected(&g);
            let idx = ArcIndex::new(&directed);
            let active = vec![true; idx.num_arcs()];

            // Every terminal as the ascent root, so the misrooted cases are
            // exercised deliberately rather than by luck.
            for &ascent_root in &terminals {
                let da = dual_ascent_packing(&idx, ascent_root, &terminals, &active, 1 << 20);
                let r = dijkstra_steiner_guided(
                    &g,
                    &terminals,
                    Cost::INFINITY,
                    u64::MAX,
                    None,
                    Some(&da.sets),
                );
                let got = r.as_ref().and_then(|r| r.optimal);
                assert!(
                    got.is_some_and(|c| (c - expected).abs() < 1e-9),
                    "ascent root {ascent_root}: expected {expected}, got {got:?}"
                );
                // And every intermediate bound must stay below the optimum.
                for budget in [1u64, 3, 10, 50] {
                    let Some(part) = dijkstra_steiner_guided(
                        &g,
                        &terminals,
                        Cost::INFINITY,
                        budget,
                        None,
                        Some(&da.sets),
                    ) else {
                        continue;
                    };
                    assert!(
                        part.lower_bound <= expected + 1e-9,
                        "ascent root {ascent_root}, budget {budget}: bound {} exceeds optimum {expected}",
                        part.lower_bound
                    );
                }
            }
            checked += 1;
        }
        assert!(checked > 80, "only {checked} instances exercised");
    }

    #[test]
    fn matches_brute_force() {
        let mut rng = rng_from(0xA5A5_1234_DEAD_0001);
        let mut checked = 0;
        for _ in 0..400 {
            let (g, terminals) = random_instance(&mut rng, 4);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                g.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            let Some(expected) = brute(g.num_nodes, &edges, &terminals) else { continue };
            let got = dijkstra_steiner(&g, &terminals, Cost::INFINITY, u64::MAX, None)
                .and_then(|r| r.optimal);
            assert!(
                got.is_some_and(|c| (c - expected).abs() < 1e-9),
                "expected {expected}, got {got:?}"
            );
            checked += 1;
        }
        assert!(checked > 100, "only {checked} instances exercised");
    }

    /// The incumbent cutoff must never change the answer when it is valid.
    #[test]
    fn pruning_against_a_valid_incumbent_is_exact() {
        let mut rng = rng_from(0x1357_9BDF_0246_8ACE);
        for _ in 0..400 {
            let (g, terminals) = random_instance(&mut rng, 4);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                g.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            let Some(expected) = brute(g.num_nodes, &edges, &terminals) else { continue };
            // Exactly the optimum is the tightest valid cutoff there is.
            let got = dijkstra_steiner(&g, &terminals, expected, u64::MAX, None)
                .and_then(|r| r.optimal);
            assert!(
                got.is_some_and(|c| (c - expected).abs() < 1e-9),
                "cutoff {expected} lost the optimum, got {got:?}"
            );
        }
    }

    /// An abandoned search must still hand back a bound below the optimum.
    #[test]
    fn abandoned_search_yields_a_valid_lower_bound() {
        let mut rng = rng_from(0x0F0F_0F0F_1122_3344);
        let mut nontrivial = 0;
        for _ in 0..400 {
            let (g, terminals) = random_instance(&mut rng, 5);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                g.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            let Some(expected) = brute(g.num_nodes, &edges, &terminals) else { continue };
            for budget in [1u64, 2, 5, 20] {
                let Some(r) = dijkstra_steiner(&g, &terminals, Cost::INFINITY, budget, None) else {
                    continue;
                };
                assert!(
                    r.lower_bound <= expected + 1e-9,
                    "bound {} exceeds optimum {expected}",
                    r.lower_bound
                );
                if r.optimal.is_none() && r.lower_bound > 0.0 {
                    nontrivial += 1;
                }
            }
        }
        assert!(nontrivial > 0, "no abandoned run produced a positive bound");
    }

    /// Cross-check against the Dreyfus-Wagner implementation on bigger graphs
    /// than brute force can reach.
    #[test]
    fn agrees_with_dreyfus_wagner() {
        let mut rng = rng_from(0xCAFE_BABE_5EED_0007);
        let mut checked = 0;
        for _ in 0..120 {
            let (g, terminals) = random_instance(&mut rng, 12);
            let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
            let got = dijkstra_steiner(&g, &terminals, Cost::INFINITY, u64::MAX, None)
                .and_then(|r| r.optimal);
            assert!(
                got.is_some_and(|c| (c - dw.optimal_cost).abs() < 1e-6),
                "Dreyfus-Wagner says {}, search says {got:?}",
                dw.optimal_cost
            );
            checked += 1;
        }
        assert!(checked > 50, "only {checked} instances exercised");
    }
}
