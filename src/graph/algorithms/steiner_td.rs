//! Exact Steiner tree by dynamic programming over a tree decomposition.
//!
//! This is the exact algorithm whose running time is exponential in the *width*
//! and polynomial in everything else — in particular it does not care how many
//! terminals there are, which is the property Dijkstra-Steiner and
//! Dreyfus-Wagner do not have. It is dispatched on a width that has been
//! computed for the graph it is about to run on, never on any property of where
//! that graph came from.
//!
//! The reduced PACE instances themselves decompose at width 58 to 66, so this
//! never runs on one (see the notes). Where it does run is on graphs *derived*
//! from an instance that are provably near-trees — the subgraph spanned by a
//! pool of elite primal solutions, whose cyclomatic number is the number of
//! edges by which those solutions disagree.
//!
//! # The state
//!
//! Fix a *root terminal* `r` and place it in every bag. For a node `t` of the
//! decomposition write `X_t` for its bag and `V_t` for the union of the bags in
//! its subtree. A **partial solution** at `t` is a forest `F` in `G[V_t]` with
//!
//! - every terminal of `V_t \ X_t` a vertex of `F`,
//! - every connected component of `F` containing at least one vertex of `X_t`,
//!
//! and its **signature** is the pair `(S, P)` where `S = V(F) ∩ X_t` and `P` is
//! the partition of `S` by which component of `F` each vertex lies in. The
//! table `c_t(S, P)` holds the least cost of a partial solution with that
//! signature.
//!
//! A partial solution is an **edge set, not a forest**. That is a deliberate
//! choice and not a relaxation of the answer: with nonnegative costs the
//! cheapest connected subgraph spanning the terminals is a tree, so minimising
//! over the larger class returns the same number. It is forced on us — the
//! forest restriction is *provably incompatible* with the rank-based reduction
//! that makes the tables small, and the witness is recorded in
//! [`rankreduce::tests::forest_completions_are_not_preserved`]. See the join
//! recurrence below.
//!
//! The second bullet is not a restriction on optimal solutions:
//!
//! > **Lemma 1.** Let `T` be any tree in `G` containing every terminal, and let
//! > `F = T ∩ G[V_t]`. Then every component of `F` meets `X_t`.
//!
//! *Proof.* `X_t` separates `V_t \ X_t` from `V \ V_t` — that is exactly axiom 3
//! of a tree decomposition, applied to the tree edge above `t`. Let `C` be a
//! component of `F` missing `X_t`, so `C subset V_t \ X_t`. `T` is connected and
//! contains `r in X_t`, so if `C` is not all of `T` there is an edge of `T`
//! leaving `C`; its far endpoint is outside `V_t` (or it would be in `C`), so
//! that edge crosses the separator without touching it — impossible. And `C` is
//! not all of `T` because `r notin C`. QED
//!
//! # The recurrences
//!
//! The decomposition is first made *nice*: every node is a leaf with an empty
//! bag, an introduce-vertex, a forget-vertex, an introduce-edge, or a join of
//! two children with equal bags, and every edge of `G` is introduced exactly
//! once. Each recurrence is a statement about how a partial solution at a node
//! restricts to its children, and each is exhaustive in one direction and sound
//! in the other.
//!
//! - **Leaf**, `X = {}`. The only partial solution is the empty forest:
//!   `c(∅, ∅) = 0`.
//!
//! - **Introduce vertex `v`**, `X_t = X_{t'} + v`, `V_t = V_{t'} + v`. No edge
//!   of `G[V_t]` is incident to `v` yet, so `v` is isolated in `F`. Hence
//!   `c_t(S,P) = c_{t'}(S,P)` when `v notin S`, and `c_t(S,P) = c_{t'}(S-v, P-v)`
//!   when `v in S` and `{v}` is a block of `P`; otherwise the state is
//!   unreachable.
//!
//! - **Introduce edge `{u,w}`**, `u,w in X_t`, `V_t = V_{t'}`. A partial
//!   solution either omits the edge — giving `c_{t'}(S,P)` — or uses it, which
//!   requires `u,w in S` and merges their blocks. Taking it when `u` and `w`
//!   already share a block is skipped: it leaves the signature unchanged and
//!   adds `c(u,w) >= 0`, so the entry it would write is never cheaper than the
//!   one already there. Nonnegativity is checked, not assumed.
//!
//! - **Forget vertex `v`**, `X_t = X_{t'} - v`, `V_t = V_{t'}`. A partial
//!   solution at `t` is one at `t'` with `v` no longer exposed. If `v` is a
//!   terminal it must lie in `F`, so states with `v notin S'` are dropped. And
//!   if `v` is alone in its block of `P'`, its component meets `X_t` nowhere and
//!   the second bullet fails — that state is dropped too. Dropping it costs
//!   nothing: a component that is the isolated vertex `v` alone is already
//!   accounted for by the state with `v notin S'` at equal cost, and any larger
//!   orphaned component cannot occur in a tree by Lemma 1.
//!
//! - **Join**, `X_t = X_{t_1} = X_{t_2}` and `V_{t_1} ∩ V_{t_2} = X_t`. A
//!   partial solution splits as `F_1 = F ∩ G[V_{t_1}]`, `F_2 = F ∩ G[V_{t_2}]`,
//!   which share exactly their vertices in `X_t` and no edges (each edge is
//!   introduced once, below exactly one side). So `S_1 = S_2 = S`, the cost adds,
//!   and `P` is the join `P_1 ⊔ P_2` in the partition lattice of `S`. **Every**
//!   such pair is accepted.
//!
//!   The union of two forests need not be a forest, and it is exactly the
//!   cyclic unions that this recurrence used to reject, by the criterion
//!
//!   ```text
//!   |P_1| + |P_2| = |S| + |P_1 ⊔ P_2|,
//!   ```
//!
//!   which is a correct characterisation of when `F_1 ∪ F_2` is a forest:
//!   contract each component of `F_i` to a spanning tree of its trace on `S`, so
//!   side `i` contributes `|S| - |P_i|` connections; the union is a graph on `S`
//!   with `(|S|-|P_1|) + (|S|-|P_2|)` edges and `|P_1 ⊔ P_2|` components, and a
//!   graph with `n` vertices and `k` components is a forest iff it has exactly
//!   `n - k` edges. **Correct, and unusable.** Imposing it makes the table's
//!   query "which `P_1` complete this `P_2` into a *forest* spanning `S`", and
//!   the rank-based reduction below preserves the least cost of the query
//!   "which `P_1` complete this `P_2` into a *connected* spanning subgraph". The
//!   two are different questions and the reduction answers only the second; on
//!   `S = {a,b,c}` the discrete partition is the sum of the three two-block
//!   partitions in cut space, so it is discarded as dependent, and it is the
//!   unique forest-completion of the one-block query. The witness is a test.
//!
//!   Keeping the cyclic joins is what repairs it, and it costs nothing:
//!
//!   > **Lemma 2.** Let `OPT` be the Steiner minimum tree cost. Every state this
//!   > DP reaches denotes a real edge set of its stated cost, and the optimal
//!   > tree's restrictions are among the states reached. Hence the value read at
//!   > the root is exactly `OPT`.
//!
//!   *Proof.* Soundness: each recurrence builds an actual edge set from actual
//!   edge sets, joins union edge-disjoint sides, and the root state's defining
//!   property — every component meets `{r}` — forces a single component covering
//!   every terminal, so its cost is at least `OPT`. Completeness: restrict the
//!   optimal tree `T` to each `V_t`. Lemma 1 says every component meets the bag,
//!   so no forget-drop fires on it; `T` has no cycle, so the introduce-edge skip
//!   never fires on it; and the join accepts unconditionally. So `T`'s
//!   restrictions survive, giving at most `OPT`. QED
//!
//! # The answer
//!
//! The decomposition of a connected graph produced by the elimination game has
//! a single root bag; forgetting down from it leaves the bag `{r}`, and the
//! entry `c(S={r}, P={{r}})` is the cost of a least-cost edge set in `G` in
//! which every terminal appears and every component meets `{r}` — that is, a
//! least-cost connected subgraph containing every terminal, whose value is the
//! Steiner minimum tree cost by Lemma 2.
//!
//! When the caller wants the tree and not only its value, the edge set read
//! back from the backpointers is reduced to a spanning tree of itself. That
//! cannot change the cost: an edge closing a cycle can be deleted without
//! disconnecting anything, and if it had positive cost the remaining set would
//! be a cheaper connected subgraph spanning the terminals, contradicting
//! minimality. So every discarded edge has cost zero, and this is asserted
//! rather than assumed.
//!
//! # What is bounded
//!
//! The table at a node has at most `Bell(|X_t| + 1)` entries and is stored
//! sparsely, so unreachable signatures cost nothing. Both a per-node and a total
//! state cap are enforced; exceeding either abandons the run and returns `None`,
//! which is always safe because every caller treats the DP as an *optional*
//! improvement.

use std::collections::HashMap;

use crate::graph::algorithms::tree_decomposition::TreeDecomposition;
use crate::graph::{Cost, EdgeId, NodeId, UndirectedGraph};

/// Largest bag the encoding admits. A signature packs one 4-bit block index per
/// bag position into a `u64`, and 15 is reserved to mean "not in `S`".
pub const MAX_BAG: usize = 15;
const OUT: u8 = 15;

/// Bell numbers `B(0) .. B(15)`: `B(k)` is the number of partitions of a
/// `k`-set, and a bag of size `b` therefore carries at most `B(b+1)` signatures
/// — one partition per subset, which is `sum_j C(b,j) B(j) = B(b+1)`.
const BELL: [f64; 17] = [
    1.0, 1.0, 2.0, 5.0, 15.0, 52.0, 203.0, 877.0, 4140.0, 21147.0, 115975.0, 678570.0, 4213597.0,
    27644437.0, 190899322.0, 1382958545.0, 10480142147.0,
];

/// An upper bound on the work the dynamic programme will do on `td`, in units
/// of one table entry touched.
///
/// **Why a width cap is not enough.** The DP is `3^w`-ish per *bag*, and the
/// number of bags is the number of vertices. A width of six on a 250-vertex
/// ground set is `B(8) = 4140` signatures per bag and `4140^2` pairs at every
/// join, which is seconds — while the same width on a thirty-vertex ground set
/// is instantaneous. Gating on the width alone was measured as a loss: it let
/// the recombination spend 3.6 s inside a 5 s budget on PACE instance175, a
/// graph with 298 vertices, and cost three instances their proof.
///
/// So the gate is the work itself, computed from the decomposition that is
/// about to be run and in the same units as every other dispatch in this
/// solver. Tables are stored sparsely and are in practice far smaller than
/// `B(b+1)`, so this is conservative in the safe direction: it can refuse work
/// that would have been affordable, never accept work that is not.
///
/// `extra` is the number of vertices added to every bag before the run — one,
/// for the root terminal.
pub fn work_estimate(td: &TreeDecomposition, num_edges: usize, extra: usize) -> f64 {
    let mut work = 0.0;
    for (i, bag) in td.bags.iter().enumerate() {
        let b = (bag.len() + extra).min(MAX_BAG);
        // One introduce or forget node per bag vertex, plus the edges assigned
        // here; each sweeps the table once.
        work += (b as f64 + 1.0) * table_bound(b);
        // Every child past the first is a join, which pairs the two tables
        // class by class.
        let joins = td.children[i].len().saturating_sub(1) as f64;
        work += joins * join_bound(b);
    }
    // Edges are assigned one per bag on average; charge them at the widest bag
    // rather than tracking the assignment, which the caller has not made yet.
    let widest = (td.bags.iter().map(|b| b.len()).max().unwrap_or(0) + extra).min(MAX_BAG);
    work += num_edges as f64 * table_bound(widest);
    work
}

/// States a reduced table at a bag of `b` positions can hold.
///
/// The old estimate used `Bell(b+1)`, the number of signatures. That was right
/// before the rank-based reduction existed and is wrong by an exponential factor
/// now: a class whose used set has `s` elements is cut down to at most `2^{s-1}`
/// representatives, so the bound is
///
/// ```text
/// sum_{s=0}^{b} C(b,s) * min(Bell(s), 2^{max(s-1,0)}),
/// ```
///
/// which is `O(3^b)` rather than `O(Bell(b))`. At `b = 13` that is the
/// difference between `2.5e6` and `2.8e7`; at the widths the estimate is used to
/// *compare* decompositions the difference is nine orders of magnitude, because
/// the old form squared `Bell` at every join.
///
/// It is still an upper bound and still a loose one — the reachable signatures
/// at a bag are a small fraction of the representable ones — so it remains
/// unusable as an absolute admission test, which is why [`crate::solver`] bounds
/// the DP by the clock instead. What it *is* good for is ranking two
/// decompositions of the same graph against each other, where the looseness is a
/// common factor that cancels.
fn table_bound(b: usize) -> f64 {
    let mut total = 0.0;
    for s in 0..=b {
        total += binom(b, s) * class_bound(s);
    }
    total
}

/// Pairs a join forms, summed over the classes of one bag.
fn join_bound(b: usize) -> f64 {
    let mut total = 0.0;
    for s in 0..=b {
        let e = class_bound(s);
        total += binom(b, s) * e * e;
    }
    total
}

/// Representatives one `S`-class of size `s` can hold: the cut space has
/// dimension `2^{s-1}`, and there are only `Bell(s)` partitions to begin with.
fn class_bound(s: usize) -> f64 {
    if s == 0 {
        return 1.0;
    }
    BELL[s.min(BELL.len() - 1)].min((1u64 << (s - 1)) as f64)
}

fn binom(n: usize, k: usize) -> f64 {
    let mut r = 1.0;
    for i in 0..k {
        r = r * (n - i) as f64 / (i + 1) as f64;
    }
    r
}

/// Table entries this dynamic programme touches per second, measured.
///
/// The same shape as [`crate::model::HYP_UNITS_PER_SECOND`]: a machine constant
/// that turns the work estimate above into a predicted running time, so a
/// caller can decide *before starting* whether an attempt fits in the time it
/// has. That decision has to be made in advance — an attempt that runs out of
/// clock costs its whole budget and returns nothing.
///
/// # The measurement
///
/// The old value, `2.0e7`, was taken before [`table_bound`] was corrected for
/// the rank-based reduction, and it is wrong by an order of magnitude against
/// the programme it now describes. Fifteen completed runs — every PACE Track 2
/// instance the classical reduction leaves inside the width cap and the DP
/// carries to a value, `td_census` with a sixty-second cap:
///
/// | work | seconds | units/s |
/// |---|---|---|
/// | 2.83e8 | 2.36 | 1.20e8 |
/// | 2.94e8 | 1.81 | 1.62e8 |
/// | 5.76e8 | 3.01 | 1.91e8 |
/// | 6.41e8 | 3.68 | 1.74e8 |
/// | 6.61e8 | 4.10 | 1.61e8 |
/// | 1.16e9 | 8.98 | 1.29e8 |
/// | 1.28e9 | 5.17 | 2.48e8 |
/// | 1.39e9 | 7.37 | 1.89e8 |
/// | 1.80e9 | 6.80 | 2.65e8 |
/// | 2.01e9 | 10.42 | 1.93e8 |
/// | 2.17e9 | 10.05 | 2.16e8 |
/// | 3.16e9 | 15.78 | 2.00e8 |
/// | 4.56e9 | 23.58 | 1.93e8 |
/// | 6.15e9 | 44.67 | 1.38e8 |
/// | 6.52e9 | 22.57 | 2.89e8 |
///
/// The range is `1.2e8` to `2.9e8` over a work range of twenty-three, median
/// `1.9e8`. The value below is the **low end** of that range and not its median,
/// because the two errors are not symmetric: under-stating the throughput only
/// refuses an attempt that would have fitted, while over-stating it admits one
/// that consumes the window and returns nothing.
///
/// What the estimate is loose *about* is a separate matter and is why this
/// constant cannot be read as a prediction of any single run: [`table_bound`]
/// counts representable signatures, and on a graph whose reachable signatures
/// are a small fraction of those the ratio is not 1.5e8 but four orders of
/// magnitude more. So `work / TD_UNITS_PER_SECOND <= window` is a *sufficient*
/// condition for affordability and never a necessary one, and a caller may use
/// it to grant an attempt but never to withdraw one.
pub const TD_UNITS_PER_SECOND: f64 = 1.5e8;

/// Rank-based reduction of a table's partitions.
///
/// # The complexity improvement
///
/// The table at a bag of size `b` holds up to `Bell(b+1)` signatures and the
/// join step pairs two of them, so the DP is `Bell(b)^2` per join. That is what
/// makes width ten cost 38 seconds where width six costs 0.14. The **rank-based
/// approach** replaces `Bell` by `2^b`: at `b = 12` that is `4.2` million
/// against `2048`, and it is a change of exponential base, not a constant.
///
/// # The cut vector, and the identity everything rests on
///
/// For a partition `p` of a set `S`, let `cuts(p)` be the `GF(2)` vector indexed
/// by the bipartitions `(X, S - X)` of `S` — canonically, by the subsets `X`
/// containing the least element of `S`, so there are `2^{|S|-1}` of them — with
///
/// ```text
/// cuts(p)[X] = 1  iff  every block of p lies inside X or inside S - X.
/// ```
///
/// > **Identity.** For partitions `p, q` of `S`, the inner product
/// > `<cuts(p), cuts(q)>` over `GF(2)` is `1` exactly when `p ⊔ q = {S}`, i.e.
/// > exactly when `p` and `q` together connect `S`.
///
/// *Proof.* A bipartition refines both `p` and `q` exactly when it refines their
/// join `p ⊔ q`, since the blocks of the join are the connected components of
/// the union and a bipartition refines a partition iff no block crosses it. The
/// bipartitions refining a partition with `c` blocks are obtained by choosing,
/// for each block other than the one holding the least element, which side it
/// goes to — so there are `2^{c-1}` of them. Hence
/// `<cuts(p), cuts(q)> = 2^{c-1} mod 2`, which is `1` iff `c = 1`. QED
///
/// # The reduction, and why it loses nothing
///
/// > **Theorem (representation).** Process a weighted set `A` of partitions in
/// > nondecreasing weight, keeping `p` exactly when `cuts(p)` lies outside the
/// > span of the vectors already kept. For the resulting `A'` and **every**
/// > partition `q` of `S`,
/// > ```text
/// > min { w(p) : p in A,  p ⊔ q = {S} }  =  min { w(p) : p in A', p ⊔ q = {S} }.
/// > ```
///
/// *Proof.* `A'` is a subset of `A`, so `>=` is immediate. For `<=`, let `p in A`
/// attain the left-hand side. If `p in A'` there is nothing to prove. Otherwise
/// `cuts(p) = sum_{i in I} cuts(p_i)` for some kept `p_i`, each with
/// `w(p_i) <= w(p)` because `p` was processed after them. Then
/// `1 = <cuts(p), cuts(q)> = sum_{i in I} <cuts(p_i), cuts(q)>` over `GF(2)`, so
/// an odd number of the terms are `1` — in particular at least one — and that
/// `p_i` satisfies `p_i ⊔ q = {S}` with `w(p_i) <= w(p)`. QED
///
/// `|A'| <= rank <= 2^{|S|-1}`, which is the bound advertised.
///
/// # Why it is sound to apply after every node
///
/// The theorem above is a statement about one table and one query. The DP
/// applies the reduction at every node and then keeps computing, so what is
/// actually needed is that *representation is preserved by every operation the
/// DP performs*. Write `A ⊑ A'` for "`A'` is a subset of `A` and
/// `opt(A',q) = opt(A,q)` for every partition `q` of `S`", where
/// `opt(A,q) = min{ A(p) : p ⊔ q = {S} }`. Then:
///
/// > **Lemma J (join).** If `A ⊑ A'` then `join(A,B) ⊑ join(A',B)`, where
/// > `join(A,B)(r) = min{ A(p)+B(p') : p ⊔ p' = r }`.
///
/// *Proof.* Let `p, p'` attain `opt(join(A,B), q)`, so `p ⊔ (p' ⊔ q) = {S}`.
/// Apply `A ⊑ A'` with the query `p' ⊔ q`: some `p'' in A'` has
/// `A'(p'') <= A(p)` and `p'' ⊔ p' ⊔ q = {S}`. Then `p'' ⊔ p'` is a state of
/// `join(A',B)` of weight at most `A(p)+B(p')` completing `q`. QED
///
/// > **Lemma F (forget).** The projection `proj(A)(q) = min{ A(p) : p|_X = q,
/// > v is not a singleton block of p }` preserves representation.
///
/// *Proof.* This is the one filter in the DP that looks at an individual
/// partition, and it is exactly a connectivity query in disguise. In the union
/// graph of `p` and `q ∪ {{v}}`, the vertex `v` is adjacent only to its
/// `p`-blockmates, so `S ∪ {v}` is connected there iff `S` is connected in the
/// union of `p|_X` and `q` **and** `v` has a `p`-blockmate. Hence
/// `opt(proj(A), q) = opt(A, q ∪ {{v}})`, and the right-hand side is preserved
/// by hypothesis. QED
///
/// Introduce-vertex is the injection `p ↦ p ∪ {{v}}`, whose queries pull back
/// the same way; introduce-edge is `min(A, c + join(A, {uw}))`, covered by
/// Lemma J; the pointwise `min` of two represented tables represents their
/// `min`; and the terminal-coverage filter is a statement about `S` alone, so it
/// deletes whole classes and never splits one. The root query is a single
/// connectivity query. So the reduction is safe at every node.
///
/// # What it does *not* preserve: forest completions
///
/// The identity is about `p ⊔ q = {S}` and nothing else. If the DP instead asked
/// "which `p` complete `q` into a *forest*", the reduction would be wrong, and
/// the smallest witness is `S = {a,b,c}`. In cut space
///
/// ```text
/// cuts({ab|c}) + cuts({ac|b}) + cuts({bc|a}) = cuts({a|b|c}),
/// ```
///
/// so if the three two-block partitions are cheaper the discrete partition is
/// discarded as dependent. Query `q = {abc}`: every `p` connects, so no
/// connectivity answer changes — but the forest criterion
/// `|p| + |q| = |S| + |p ⊔ q|` reads `|p| + 1 = 3 + 1`, which only the discrete
/// partition satisfies. The reduced table has *no* forest completion of `q`
/// while the full table has one. This is why the join in this module accepts
/// cyclic unions; `forest_completions_are_not_preserved` keeps the witness
/// alive so the filter cannot be reintroduced by accident.
///
/// ## Why the filtered join nevertheless passed every test it was given
///
/// The witness needs the discrete partition to be *strictly dearer* than the
/// three two-block partitions, or to tie with them and lose the tie-break. It
/// can never be strictly dearer:
///
/// > **Lemma D (discrete dominance).** At any node `t` and used set `S`, the
/// > least cost of a partial solution with signature `(S,p)` is minimised over
/// > `p` by the discrete partition of `S`.
///
/// *Proof.* Let `F` realise `(S,p)` and let `C` be a component of `F` with trace
/// `B = C ∩ X_t`. Take a spanning tree of `C` and assign every vertex of `C` to
/// the nearest vertex of `B` in that tree, breaking ties by index. Each class is
/// a connected subtree — the whole path from a vertex to its representative is
/// assigned to that representative — and contains exactly one vertex of `B`, so
/// deleting the `|B| - 1` edges between classes splits `C` into `|B|` components
/// each meeting `X_t` in one vertex, with every forgotten terminal of `C` still
/// present in one of them. Doing this to every component yields a partial
/// solution with the discrete signature and, costs being nonnegative, no greater
/// cost. QED
///
/// So the discrete partition is processed first in the cost ordering, its cut
/// vector — the all-ones vector — is independent of the empty basis, and it
/// survives. The reduction can only discard it when several partitions tie at
/// the minimum and the tie-break puts the discrete one last, which is decided by
/// hash iteration order. That is why the filtered join answered every random
/// instance correctly, including unit-cost instances built to maximise ties: it
/// was correct by accident, on a hash order. Correctness that depends on hash
/// order is not correctness, which is the whole reason the filter is gone.
mod rankreduce {
    use super::{Cost, MAX_BAG, OUT};

    /// Words of `u64` a cut vector needs for a bag position count of `b`.
    /// Capped so that `MAX_BAG` positions stay addressable.
    const MAX_WORDS: usize = 1 << (MAX_BAG - 1 - 6);

    /// The cut vector of a decoded signature, over the positions it uses.
    ///
    /// `used` lists the bag positions in `S`, in increasing order; a bipartition
    /// is named by which of `used[1..]` join `used[0]`, so the vector has
    /// `2^{|S|-1}` entries.
    fn cut_vector(d: &[u8; MAX_BAG], used: &[usize], out: &mut [u64]) {
        out.iter_mut().for_each(|w| *w = 0);
        let s = used.len();
        if s == 0 {
            return;
        }
        // Block masks over the compressed index space `used[1..]`, and which
        // block holds `used[0]`.
        let mut block_mask = [0u32; MAX_BAG];
        let mut nblocks = 0usize;
        let mut label = [OUT; MAX_BAG];
        let mut home = usize::MAX;
        for (i, &pos) in used.iter().enumerate() {
            let raw = d[pos];
            let b = if label[raw as usize] == OUT {
                label[raw as usize] = nblocks as u8;
                nblocks += 1;
                nblocks - 1
            } else {
                label[raw as usize] as usize
            };
            if i == 0 {
                home = b;
            } else {
                block_mask[b] |= 1 << (i - 1);
            }
        }
        // Enumerate the subsets of the blocks other than `home`; each gives one
        // bipartition that refines the partition.
        let others: Vec<u32> =
            (0..nblocks).filter(|&b| b != home).map(|b| block_mask[b]).collect();
        let k = others.len();
        for t in 0..(1usize << k) {
            // `used[0]` is in `X` by convention, so the block holding it always
            // contributes; the other blocks are chosen by `t`.
            let mut x = block_mask[home];
            let mut tt = t;
            while tt != 0 {
                let i = tt.trailing_zeros() as usize;
                x |= others[i];
                tt &= tt - 1;
            }
            let col = x as usize;
            out[col >> 6] |= 1 << (col & 63);
        }
    }

    /// An incremental row-reduced basis of the cut space of an `s`-element
    /// ground set.
    ///
    /// The reduction is a matroid greedy: process candidates in nondecreasing
    /// weight and keep exactly those whose cut vector is independent of the ones
    /// already kept. Making the basis an object rather than a loop is what lets
    /// the join below run the greedy *while* it generates candidates, and stop
    /// the moment the basis is full.
    pub struct Basis {
        bits: usize,
        words: usize,
        rows: Vec<Vec<u64>>,
        pivots: Vec<usize>,
        scratch: Vec<u64>,
    }

    impl Basis {
        pub fn new(s: usize) -> Basis {
            // `s <= 1` admits exactly one partition, so the cut space is the
            // zero space and the first candidate is the only one.
            let bits = if s <= 1 { 1 } else { 1usize << (s - 1) };
            let words = bits.div_ceil(64).min(MAX_WORDS);
            Basis { bits, words, rows: Vec::new(), pivots: Vec::new(), scratch: vec![0u64; words] }
        }

        /// Whether the basis spans the whole cut space, so that every further
        /// candidate is dependent whatever it is.
        pub fn is_full(&self) -> bool {
            self.rows.len() >= self.bits
        }

        /// Offer a partition. Returns `true` — and keeps it — exactly when its
        /// cut vector is outside the current span.
        pub fn offer(&mut self, d: &[u8; MAX_BAG], used: &[usize]) -> bool {
            if used.len() <= 1 {
                // One partition exists; the first offer is it.
                if self.rows.is_empty() {
                    self.rows.push(vec![0u64; self.words]);
                    self.pivots.push(0);
                    return true;
                }
                return false;
            }
            cut_vector(d, used, &mut self.scratch);
            let mut v = std::mem::replace(&mut self.scratch, vec![0u64; self.words]);
            for (bi, &p) in self.pivots.iter().enumerate() {
                if v[p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..self.words {
                        v[w] ^= self.rows[bi][w];
                    }
                }
            }
            let Some(p) = (0..self.bits).find(|&c| v[c >> 6] >> (c & 63) & 1 == 1) else {
                self.scratch = v;
                return false;
            };
            // Normalise the kept rows so later reductions stay a single pass.
            for bi in 0..self.rows.len() {
                if self.rows[bi][p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..self.words {
                        self.rows[bi][w] ^= v[w];
                    }
                }
            }
            self.rows.push(v);
            self.pivots.push(p);
            true
        }
    }

    /// Keep a minimum-weight representative subset of `entries`.
    ///
    /// `order` must list the entries by nondecreasing cost; the returned indices
    /// are those to keep.
    pub fn reduce(decoded: &[[u8; MAX_BAG]], used: &[usize], order: &[usize]) -> Vec<usize> {
        if used.len() <= 1 {
            // A single element admits one partition, so nothing can be dropped
            // and no work is needed.
            return order.to_vec();
        }
        let mut basis = Basis::new(used.len());
        let mut keep = Vec::new();
        for &i in order {
            if basis.is_full() {
                break;
            }
            if basis.offer(&decoded[i], used) {
                keep.push(i);
            }
        }
        keep
    }

    /// Weight-ordered indices, cheapest first.
    pub fn by_cost(costs: &[Cost]) -> Vec<usize> {
        let mut order: Vec<usize> = (0..costs.len()).collect();
        order.sort_by(|&a, &b| costs[a].partial_cmp(&costs[b]).unwrap_or(std::cmp::Ordering::Equal));
        order
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// All partitions of `{0..s-1}`, as restricted growth strings padded
        /// into a signature over bag positions `0..s-1`.
        fn all_partitions(s: usize) -> Vec<[u8; MAX_BAG]> {
            let mut out = Vec::new();
            fn grow(i: usize, used: u8, a: &mut [u8; MAX_BAG], s: usize, out: &mut Vec<[u8; MAX_BAG]>) {
                if i == s {
                    out.push(*a);
                    return;
                }
                for v in 0..=used {
                    a[i] = v;
                    grow(i + 1, used.max(v + 1), a, s, out);
                }
            }
            let mut a = [OUT; MAX_BAG];
            a[0] = 0;
            grow(1, 1, &mut a, s, &mut out);
            out
        }

        /// Whether the join of two partitions of `{0..s-1}` is the single block.
        fn joins_connected(p: &[u8; MAX_BAG], q: &[u8; MAX_BAG], s: usize) -> bool {
            let mut uf: Vec<usize> = (0..s).collect();
            fn find(uf: &mut Vec<usize>, mut x: usize) -> usize {
                while uf[x] != x {
                    uf[x] = uf[uf[x]];
                    x = uf[x];
                }
                x
            }
            for side in [p, q] {
                for i in 0..s {
                    for j in i + 1..s {
                        if side[i] == side[j] {
                            let (a, b) = (find(&mut uf, i), find(&mut uf, j));
                            uf[a] = b;
                        }
                    }
                }
            }
            (0..s).map(|i| find(&mut uf, i)).collect::<std::collections::HashSet<_>>().len() == 1
        }

        /// Blocks of a partition of `{0..s-1}`, as a vector of masks.
        fn block_masks(p: &[u8; MAX_BAG], s: usize) -> Vec<u32> {
            let mut by: std::collections::HashMap<u8, u32> = std::collections::HashMap::new();
            for i in 0..s {
                *by.entry(p[i]).or_insert(0) |= 1 << i;
            }
            let mut v: Vec<u32> = by.into_values().collect();
            v.sort_unstable();
            v
        }

        /// The join of two partitions of `{0..s-1}`, as a canonical signature.
        fn join_of(p: &[u8; MAX_BAG], q: &[u8; MAX_BAG], s: usize) -> [u8; MAX_BAG] {
            let mut uf: Vec<usize> = (0..s).collect();
            fn find(uf: &mut Vec<usize>, mut x: usize) -> usize {
                while uf[x] != x {
                    uf[x] = uf[uf[x]];
                    x = uf[x];
                }
                x
            }
            for side in [p, q] {
                for i in 0..s {
                    for j in i + 1..s {
                        if side[i] == side[j] {
                            let (a, b) = (find(&mut uf, i), find(&mut uf, j));
                            uf[a] = b;
                        }
                    }
                }
            }
            let mut out = [OUT; MAX_BAG];
            let mut map = std::collections::HashMap::new();
            let mut next = 0u8;
            for i in 0..s {
                let r = find(&mut uf, i);
                let id = *map.entry(r).or_insert_with(|| {
                    next += 1;
                    next - 1
                });
                out[i] = id;
            }
            out
        }

        /// Whether `p ∪ q` is a forest: the rank criterion from the module
        /// comment, `|p| + |q| = |S| + |p ⊔ q|`.
        fn forest_compatible(p: &[u8; MAX_BAG], q: &[u8; MAX_BAG], s: usize) -> bool {
            let j = join_of(p, q, s);
            block_masks(p, s).len() + block_masks(q, s).len()
                == s + block_masks(&j, s).len()
        }

        /// **The reason the join in this module accepts cyclic unions.**
        ///
        /// The reduction preserves the least cost among *connected*
        /// completions. It does not preserve the least cost among
        /// *forest-compatible* completions, and this is the smallest witness:
        /// on `S = {a,b,c}` the three two-block partitions sum in cut space to
        /// the discrete partition, so making them cheaper discards it — and the
        /// discrete partition is the unique forest completion of the one-block
        /// query.
        ///
        /// If this test ever starts failing, the reduction has changed and the
        /// acyclicity filter might be safe again. Until then, reinstating that
        /// filter in the join makes the DP report values above the optimum.
        #[test]
        fn forest_completions_are_not_preserved() {
            let s = 3usize;
            let used = vec![0usize, 1, 2];
            let part = |a: u8, b: u8, c: u8| {
                let mut d = [OUT; MAX_BAG];
                d[0] = a;
                d[1] = b;
                d[2] = c;
                d
            };
            // {ab|c}, {ac|b}, {bc|a} at cost 1; the discrete partition at 2.
            let decoded = vec![part(0, 0, 1), part(0, 1, 0), part(0, 1, 1), part(0, 1, 2)];
            let costs: Vec<Cost> = vec![1.0, 1.0, 1.0, 2.0];
            let order = by_cost(&costs);
            assert_eq!(order.last(), Some(&3), "the discrete partition must sort last");
            let keep = reduce(&decoded, &used, &order);
            assert!(
                !keep.contains(&3),
                "the discrete partition was expected to be dependent on the three \
                 two-block partitions in cut space, but the reduction kept it"
            );

            // Connectivity is untouched: every one of the four connects with the
            // one-block query, and the cheapest survivor still costs 1.
            let q = part(0, 0, 0);
            for i in 0..4 {
                assert!(joins_connected(&decoded[i], &q, s));
            }

            // The forest question is answered differently by the two tables.
            let full_forest: Vec<usize> =
                (0..4).filter(|&i| forest_compatible(&decoded[i], &q, s)).collect();
            assert_eq!(full_forest, vec![3], "only the discrete partition is acyclic here");
            let kept_forest: Vec<usize> =
                keep.iter().copied().filter(|&i| forest_compatible(&decoded[i], &q, s)).collect();
            assert!(
                kept_forest.is_empty(),
                "the reduced table still had a forest completion; the witness has decayed"
            );
        }

        /// The rank-reduced join equals the naive join, as a *represented*
        /// table: for every ground set up to size six, every query partition,
        /// and randomly weighted tables including adversarial block-count
        /// distributions, joining the reduced tables answers every connectivity
        /// query at exactly the cost the full pairwise join does.
        ///
        /// This is Lemma J of the module comment, checked by brute force. It is
        /// the property the DP actually relies on — the single-table
        /// representation theorem is not enough on its own, because the DP joins
        /// tables that have already been reduced.
        #[test]
        fn reduced_join_matches_naive_join() {
            let mut seed = 0x1010_C0DE_7777_1111u64;
            let mut rng = move || {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                seed
            };
            for s in 2..=6usize {
                let used: Vec<usize> = (0..s).collect();
                let parts = all_partitions(s);
                for round in 0..40 {
                    // Round 0..9 keep everything; later rounds bias towards
                    // coarse or fine partitions, which is where the cut-space
                    // dependencies concentrate.
                    let bias = round % 4;
                    let pick = |p: &[u8; MAX_BAG], r: &mut dyn FnMut() -> u64| {
                        let blocks = block_masks(p, s).len();
                        let want = match bias {
                            0 => 70,
                            1 => 25 + 60 * (blocks == 1 || blocks == s) as u64,
                            2 => 90 - 12 * blocks as u64,
                            _ => 20 + 14 * blocks as u64,
                        };
                        r() % 100 < want
                    };
                    let build = |r: &mut dyn FnMut() -> u64| {
                        let chosen: Vec<[u8; MAX_BAG]> =
                            parts.iter().copied().filter(|p| pick(p, r)).collect();
                        let costs: Vec<Cost> =
                            (0..chosen.len()).map(|_| (r() % 40) as Cost).collect();
                        (chosen, costs)
                    };
                    let (pa, ca) = build(&mut rng);
                    let (pb, cb) = build(&mut rng);
                    if pa.is_empty() || pb.is_empty() {
                        continue;
                    }

                    // The naive join: every pair, minimum per result partition.
                    let mut naive: std::collections::HashMap<[u8; MAX_BAG], Cost> =
                        std::collections::HashMap::new();
                    for (i, p) in pa.iter().enumerate() {
                        for (j, q) in pb.iter().enumerate() {
                            let r = join_of(p, q, s);
                            let w = ca[i] + cb[j];
                            let e = naive.entry(r).or_insert(Cost::INFINITY);
                            if w < *e {
                                *e = w;
                            }
                        }
                    }

                    // The reduced join: reduce both sides, join, reduce again.
                    let ka = reduce(&pa, &used, &by_cost(&ca));
                    let kb = reduce(&pb, &used, &by_cost(&cb));
                    let mut fast: std::collections::HashMap<[u8; MAX_BAG], Cost> =
                        std::collections::HashMap::new();
                    for &i in &ka {
                        for &j in &kb {
                            let r = join_of(&pa[i], &pb[j], s);
                            let w = ca[i] + cb[j];
                            let e = fast.entry(r).or_insert(Cost::INFINITY);
                            if w < *e {
                                *e = w;
                            }
                        }
                    }
                    let fp: Vec<[u8; MAX_BAG]> = fast.keys().copied().collect();
                    let fc: Vec<Cost> = fp.iter().map(|k| fast[k]).collect();
                    let kf = reduce(&fp, &used, &by_cost(&fc));

                    for q in &parts {
                        let want = naive
                            .iter()
                            .filter(|(p, _)| joins_connected(p, q, s))
                            .map(|(_, &w)| w)
                            .fold(Cost::INFINITY, Cost::min);
                        let got = kf
                            .iter()
                            .filter(|&&i| joins_connected(&fp[i], q, s))
                            .map(|&i| fc[i])
                            .fold(Cost::INFINITY, Cost::min);
                        assert_eq!(
                            want.is_finite(),
                            got.is_finite(),
                            "reduced join changed feasibility at s={s}"
                        );
                        if want.is_finite() {
                            assert!(
                                (want - got).abs() < 1e-9,
                                "reduced join answered {got} where the naive join answers \
                                 {want} at s={s} query={:?}",
                                &q[..s]
                            );
                        }
                    }
                }
            }
        }

        /// The identity the whole reduction rests on, by brute force over every
        /// pair of partitions of every ground set up to size seven.
        #[test]
        fn inner_product_detects_connection() {
            for s in 1..=7usize {
                let used: Vec<usize> = (0..s).collect();
                let parts = all_partitions(s);
                let words = (1usize << (s - 1)).div_ceil(64);
                let vecs: Vec<Vec<u64>> = parts
                    .iter()
                    .map(|p| {
                        let mut v = vec![0u64; words];
                        cut_vector(p, &used, &mut v);
                        v
                    })
                    .collect();
                for (i, p) in parts.iter().enumerate() {
                    for (j, q) in parts.iter().enumerate() {
                        let dot = (0..words)
                            .map(|w| (vecs[i][w] & vecs[j][w]).count_ones())
                            .sum::<u32>()
                            % 2;
                        assert_eq!(
                            dot == 1,
                            joins_connected(p, q, s),
                            "s={s} p={:?} q={:?}",
                            &p[..s],
                            &q[..s]
                        );
                    }
                }
            }
        }

        /// The representation theorem, by brute force: after reduction, the
        /// least weight completing any query partition is unchanged.
        #[test]
        fn reduction_preserves_every_completion() {
            let mut seed = 0x5EED_1234_ABCD_9876u64;
            let mut rng = move || {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                seed
            };
            for s in 2..=6usize {
                let used: Vec<usize> = (0..s).collect();
                let parts = all_partitions(s);
                for _ in 0..60 {
                    // A random weighted subset of the partitions.
                    let chosen: Vec<usize> =
                        (0..parts.len()).filter(|_| rng() % 100 < 60).collect();
                    if chosen.is_empty() {
                        continue;
                    }
                    let decoded: Vec<[u8; MAX_BAG]> = chosen.iter().map(|&i| parts[i]).collect();
                    let costs: Vec<Cost> =
                        (0..decoded.len()).map(|_| (rng() % 50) as Cost).collect();
                    let order = by_cost(&costs);
                    let keep = reduce(&decoded, &used, &order);
                    assert!(
                        keep.len() <= 1usize << (s - 1),
                        "kept {} above the 2^(s-1) bound at s={s}",
                        keep.len()
                    );
                    for q in &parts {
                        let full = (0..decoded.len())
                            .filter(|&i| joins_connected(&decoded[i], q, s))
                            .map(|i| costs[i])
                            .fold(Cost::INFINITY, Cost::min);
                        let reduced = keep
                            .iter()
                            .copied()
                            .filter(|&i| joins_connected(&decoded[i], q, s))
                            .map(|i| costs[i])
                            .fold(Cost::INFINITY, Cost::min);
                        assert_eq!(
                            full.is_finite(),
                            reduced.is_finite(),
                            "reduction changed feasibility at s={s}"
                        );
                        if full.is_finite() {
                            assert!(
                                (full - reduced).abs() < 1e-9,
                                "reduction changed the minimum {full} -> {reduced} at s={s}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// What the join actually cost, measured rather than predicted.
///
/// The width DP's remaining ceiling is the join, so the first thing to know
/// about any replacement for it is what the old one was doing: how many classes
/// it paired, how large those classes were, how many of the pairs it formed
/// survived, and how much of the wall clock it owned. These counters are
/// accumulated in locals and flushed once per node, so reading them costs
/// nothing measurable.
#[derive(Debug, Default, Clone)]
pub struct JoinStats {
    /// Join nodes executed.
    pub joins: u64,
    /// `S`-classes paired.
    pub classes: u64,
    /// Sum over classes of `|A| * |B|` — the pairs the naive join would form.
    pub pairs_available: f64,
    /// Pairs the cost-ordered join actually popped.
    pub pairs_popped: u64,
    /// States the join emitted after reduction.
    pub emitted: u64,
    /// Classes that stopped early because the cut-space basis filled.
    pub saturated: u64,
    /// Widest bag any join ran on.
    pub max_bag: usize,
    /// Nanoseconds inside join nodes.
    pub nanos: u128,
    /// Non-join nodes executed, and the states they left after reduction.
    pub unary_nodes: u64,
    pub unary_states: u64,
}

thread_local! {
    static JOIN_STATS: std::cell::RefCell<JoinStats> =
        std::cell::RefCell::new(JoinStats::default());
}

/// Read and clear the join counters for this thread.
pub fn take_join_stats() -> JoinStats {
    JOIN_STATS.with(|s| std::mem::take(&mut *s.borrow_mut()))
}

fn record<F: FnOnce(&mut JoinStats)>(f: F) {
    JOIN_STATS.with(|s| f(&mut s.borrow_mut()));
}

/// `f64` under its total order, so costs can key a binary heap.
#[derive(PartialEq, PartialOrd)]
struct ByCost(Cost);
impl Eq for ByCost {}
impl Ord for ByCost {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

/// The rank-reduced join of two tables, computed without forming their product.
///
/// # The cost the naive join pays, and why it is avoidable
///
/// After the rank-based reduction a class of used-set size `s` holds at most
/// `2^{s-1}` states, so pairing two of them is `4^{s-1}` and the whole join is
/// `sum_s C(b,s) 4^{s-1} = 5^b / 4`. But the *result* is then reduced back to at
/// most `2^{s-1}` states. Almost every pair the naive join forms is discarded a
/// moment later, and the discarding rule is a matroid greedy: process candidates
/// in nondecreasing cost, keep the ones independent of what is kept.
///
/// A matroid greedy does not need its candidates in advance. It needs them *in
/// order*, one at a time, and it may stop as soon as the basis is full.
///
/// > **Theorem (lazy join).** Let `A` and `B` be tables over `Pi(S)` sorted by
/// > cost. Enumerate the pairs `(p_i, q_j)` in nondecreasing order of
/// > `A(p_i) + B(q_j)`, and for each pair whose join partition has not been seen
/// > before, offer that partition to a cut-space basis at that cost; stop when
/// > the basis has rank `2^{s-1}` or the pairs run out. The kept set is a
/// > representative set of `join(A,B)` — that is, it answers every connectivity
/// > query at exactly the cost `join(A,B)` answers it at.
///
/// *Proof.* Write `c(r) = min{A(p)+B(q) : p ⊔ q = r}` for the naive join. Since
/// the pairs are enumerated in nondecreasing cost, the *first* pair whose join
/// is `r` has cost exactly `c(r)`; so the sequence of first appearances lists
/// the partitions of `join(A,B)` in nondecreasing `c`, which is precisely the
/// input the representation theorem asks for, and the greedy run on it keeps a
/// set satisfying that theorem's conclusion. Stopping at full rank changes
/// nothing: every candidate offered afterwards is a linear combination of kept
/// vectors of no greater cost, which is exactly the case the theorem's proof
/// already covers. QED
///
/// The tie-break among partitions of equal cost may differ from the order a hash
/// table would have produced. That is immaterial — the theorem's hypothesis is
/// *nondecreasing* cost, not a particular order — and it is what the
/// differential test `lazy_join_represents_the_naive_join` checks.
///
/// # What this buys
///
/// The pop count is bounded by the number of pairs, so nothing is worse than
/// before; and it is bounded below the moment the basis fills, which is after at
/// most `2^{s-1}` *successful* offers. On the tables the DP actually produces the
/// basis fills early, and the measured pop counts are in [`JoinStats`]. This is
/// not the `2^w poly(w)` join the research programme asks for — see the module
/// notes for why the min-plus analogue of the Cut&Count linearisation collapses —
/// but it is exact, it is proved, and it is bounded by the old cost.
fn join_tables(
    left: &HashMap<u64, (Cost, Back)>,
    right: &HashMap<u64, (Cost, Back)>,
    b: usize,
) -> HashMap<u64, (Cost, Back)> {
    use std::collections::BinaryHeap;
    use std::cmp::Reverse;

    let mut by_class: HashMap<u32, (Vec<(u64, Cost)>, Vec<(u64, Cost)>)> = HashMap::new();
    for (&code, &(cost, _)) in left {
        by_class.entry(used_mask(code, b)).or_default().0.push((code, cost));
    }
    for (&code, &(cost, _)) in right {
        by_class.entry(used_mask(code, b)).or_default().1.push((code, cost));
    }

    let mut out: HashMap<u64, (Cost, Back)> = HashMap::new();
    let mut st = JoinStats { joins: 1, max_bag: b, ..Default::default() };
    for (mask, (mut l, mut r)) in by_class {
        if l.is_empty() || r.is_empty() {
            continue;
        }
        st.classes += 1;
        st.pairs_available += l.len() as f64 * r.len() as f64;
        l.sort_by(|a, c| a.1.total_cmp(&c.1));
        r.sort_by(|a, c| a.1.total_cmp(&c.1));
        let used: Vec<usize> = (0..b).filter(|&j| mask & (1 << j) != 0).collect();
        let dl: Vec<[u8; MAX_BAG]> = l.iter().map(|&(c, _)| decode(c, b)).collect();
        let dr: Vec<[u8; MAX_BAG]> = r.iter().map(|&(c, _)| decode(c, b)).collect();

        let mut basis = rankreduce::Basis::new(used.len());
        let mut seen: std::collections::HashSet<u64> = std::collections::HashSet::new();
        let mut heap: BinaryHeap<Reverse<(ByCost, u32, u32)>> = BinaryHeap::with_capacity(l.len());
        for i in 0..l.len() {
            heap.push(Reverse((ByCost(l[i].1 + r[0].1), i as u32, 0)));
        }
        while let Some(Reverse((ByCost(cost), i, j))) = heap.pop() {
            if basis.is_full() {
                st.saturated += 1;
                break;
            }
            st.pairs_popped += 1;
            let (li, rj) = (i as usize, j as usize);
            if rj + 1 < r.len() {
                heap.push(Reverse((ByCost(l[li].1 + r[rj + 1].1), i, j + 1)));
            }
            // Same class, so the used sets agree and the union always exists.
            let Some(mut d) = union_partitions(&dl[li], &dr[rj], b) else { continue };
            let code = encode_canonical(&mut d, b);
            if !seen.insert(code) {
                continue;
            }
            if basis.offer(&d, &used) {
                out.insert(code, (cost, Back::Join(l[li].0, r[rj].0)));
            }
        }
    }
    st.emitted = out.len() as u64;
    record(|g| {
        g.joins += st.joins;
        g.classes += st.classes;
        g.pairs_available += st.pairs_available;
        g.pairs_popped += st.pairs_popped;
        g.emitted += st.emitted;
        g.saturated += st.saturated;
        g.max_bag = g.max_bag.max(st.max_bag);
    });
    out
}

/// How a state was reached, so the tree can be read back out.
#[derive(Debug, Clone, Copy)]
enum Back {
    Leaf,
    /// Introduce-vertex or forget-vertex: one child state, no edge.
    Unary(u64),
    /// Introduce-edge, with the edge taken.
    Edge(u64, EdgeId),
    Join(u64, u64),
}

/// One node of the nice decomposition.
#[derive(Debug, Clone)]
enum Nice {
    Leaf,
    Introduce { child: usize, v: u32 },
    Forget { child: usize, v: u32 },
    Edge { child: usize, u: u32, w: u32, cost: Cost, id: EdgeId },
    Join { left: usize, right: usize },
}

/// A least-cost tree spanning `terminals`, or `None` if the decomposition is
/// too wide, the caps are hit, or the instance is infeasible.
///
/// `graph` must be connected on the terminals and its costs nonnegative; both
/// are checked rather than assumed.
/// Everything the transition loop needs, derived once from the decomposition.
///
/// Factored out so the packed dynamic programme below and the unpacked
/// [`reference`] one run over *the same* nice decomposition, the same edge
/// assignment and the same root terminal. A differential test between two DPs
/// that built their own scaffolding would be testing the scaffolding.
struct Prepared {
    nodes: Vec<Nice>,
    node_bags: Vec<Vec<u32>>,
    final_node: usize,
    is_terminal: Vec<bool>,
}

/// `max_bag` is the largest bag the caller's signature encoding can address;
/// pass `usize::MAX` for an encoding that has no such limit.
fn prepare(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    td: &TreeDecomposition,
    max_bag: usize,
) -> Option<Prepared> {
    if graph.edges.iter().any(|e| e.cost < 0.0) {
        // Both the cycle exclusions above use nonnegativity.
        return None;
    }
    // A single component is required: the root bag is unique only then, and
    // Lemma 1's separator argument is stated for a tree containing `r`.
    if td.roots.len() != 1 {
        return None;
    }

    let n = td.index_to_node.len();
    let root_terminal = *td.node_to_index.get(&terminals[0])?;
    let mut is_terminal = vec![false; n];
    for &t in terminals {
        is_terminal[*td.node_to_index.get(&t)? as usize] = true;
    }

    // The root terminal joins every bag. That is what makes "a component that
    // meets no bag vertex is orphaned" true without an exception for the
    // component holding the answer, and it costs one unit of width.
    let mut bags: Vec<Vec<u32>> = td.bags.clone();
    for bag in &mut bags {
        if bag.binary_search(&root_terminal).is_err() {
            bag.push(root_terminal);
            bag.sort_unstable();
        }
        if bag.len() > max_bag {
            return None;
        }
    }

    // Each edge is introduced at the bag of its earliest-eliminated endpoint,
    // which axiom 2's proof shows contains both.
    let mut pos = vec![0usize; n];
    for (i, &v) in td.own.iter().enumerate() {
        pos[v as usize] = i;
    }
    let mut edges_at: Vec<Vec<(u32, u32, Cost, EdgeId)>> = vec![Vec::new(); bags.len()];
    for e in &graph.edges {
        if e.src == e.dst {
            continue;
        }
        let (Some(&u), Some(&w)) = (td.node_to_index.get(&e.src), td.node_to_index.get(&e.dst))
        else {
            return None;
        };
        let at = pos[u as usize].min(pos[w as usize]);
        debug_assert!(bags[at].binary_search(&u).is_ok() && bags[at].binary_search(&w).is_ok());
        edges_at[at].push((u, w, e.cost, e.id));
    }

    let (nodes, node_bags, final_node) = build_nice(td, &bags, &edges_at)?;
    Some(Prepared { nodes, node_bags, final_node, is_terminal })
}

pub fn steiner_tree_over_decomposition(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    td: &TreeDecomposition,
    state_cap: usize,
    want_tree: bool,
    deadline: Option<std::time::Instant>,
) -> Option<(Cost, Vec<EdgeId>)> {
    if terminals.is_empty() {
        return Some((0.0, Vec::new()));
    }
    let Prepared { nodes, node_bags, final_node, is_terminal } =
        prepare(graph, terminals, td, MAX_BAG)?;

    // The tables, one per nice node, sparse.
    //
    // A node's table is dead the moment its parent has been built, because the
    // nice decomposition is a tree and every node has exactly one parent. When
    // the caller does not want the tree read back — the exact finish reports a
    // value, not an edge set — the dead tables are dropped, and `state_cap`
    // becomes a bound on what is *live* rather than on the cumulative count. On
    // a graph with four thousand bags that is the difference between a bound on
    // memory and a bound on the size of the instance.
    let mut tables: Vec<HashMap<u64, (Cost, Back)>> = vec![HashMap::new(); nodes.len()];
    let mut live_states = 0usize;

    for i in 0..nodes.len() {
        let bag = &node_bags[i];
        let b = bag.len();
        let mut table: HashMap<u64, (Cost, Back)> = HashMap::new();
        let mut already_reduced = false;
        match nodes[i].clone() {
            Nice::Leaf => {
                table.insert(0, (0.0, Back::Leaf));
            }
            Nice::Introduce { child, v } => {
                let cb = &node_bags[child];
                let vp = bag.binary_search(&v).ok()?;
                for (&code, &(cost, _)) in &tables[child] {
                    // `v` absent: the same forest, re-based onto the wider bag.
                    let base = rebase(code, cb, bag, b);
                    relax(&mut table, base, cost, Back::Unary(code));
                    // `v` present and isolated: a new singleton block.
                    let mut d = decode(base, b);
                    d[vp] = free_block(&d, b);
                    let with = encode_canonical(&mut d, b);
                    relax(&mut table, with, cost, Back::Unary(code));
                }
            }
            Nice::Forget { child, v } => {
                let cb = &node_bags[child];
                let vp = cb.binary_search(&v).ok()?;
                let terminal = is_terminal[v as usize];
                for (&code, &(cost, _)) in &tables[child] {
                    let d = decode(code, cb.len());
                    if d[vp] == OUT {
                        // A terminal must appear in the forest.
                        if terminal {
                            continue;
                        }
                    } else {
                        // Forgetting a vertex alone in its block orphans its
                        // component; see the module comment.
                        let alone = (0..cb.len()).all(|j| j == vp || d[j] != d[vp]);
                        if alone {
                            continue;
                        }
                    }
                    let out = rebase(code, cb, bag, b);
                    relax(&mut table, out, cost, Back::Unary(code));
                }
            }
            Nice::Edge { child, u, w, cost: ec, id } => {
                let up = bag.binary_search(&u).ok()?;
                let wp = bag.binary_search(&w).ok()?;
                for (&code, &(cost, _)) in &tables[child] {
                    // Not taken.
                    relax(&mut table, code, cost, Back::Unary(code));
                    let mut d = decode(code, b);
                    if d[up] == OUT || d[wp] == OUT || d[up] == d[wp] {
                        continue;
                    }
                    let (keep, drop) = (d[up], d[wp]);
                    for j in 0..b {
                        if d[j] == drop {
                            d[j] = keep;
                        }
                    }
                    let merged = encode_canonical(&mut d, b);
                    relax(&mut table, merged, cost + ec, Back::Edge(code, id));
                }
            }
            Nice::Join { left, right } => {
                // The join is where the DP's remaining cost lives, so it is the
                // one node type that reduces as it generates rather than
                // afterwards. Unconditional in the acyclicity sense: the union
                // of the two sides is an edge set, not necessarily a forest, and
                // Lemma 2 says that is the right semantics.
                let t0 = std::time::Instant::now();
                table = join_tables(&tables[left], &tables[right], b);
                let ns = t0.elapsed().as_nanos();
                record(|g| g.nanos += ns);
                already_reduced = true;
            }
        }
        if table.is_empty() {
            return None;
        }
        // Rank-based reduction, applied per `S`-class: within a class the
        // partitions are comparable and the theorem in `rankreduce` says a
        // spanning subset of their cut vectors preserves the least completion
        // cost for every way the rest of the tree might close. The join has
        // already done this inline.
        let table = if already_reduced {
            table
        } else {
            let t = reduce_table(table, b);
            let states = t.len() as u64;
            record(|g| {
                g.unary_nodes += 1;
                g.unary_states += states;
            });
            t
        };
        live_states += table.len();
        if live_states > state_cap {
            return None;
        }
        // Checked every node rather than every sixty-fourth: a single join at a
        // wide bag can take longer than the whole rest of the run.
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            return None;
        }
        tables[i] = table;
        if !want_tree {
            for child in match &nodes[i] {
                Nice::Leaf => Vec::new(),
                Nice::Introduce { child, .. }
                | Nice::Forget { child, .. }
                | Nice::Edge { child, .. } => vec![*child],
                Nice::Join { left, right } => vec![*left, *right],
            } {
                live_states -= tables[child].len();
                tables[child] = HashMap::new();
            }
        }
    }

    // The final bag is `{r}` and the answer is the state in which `r` is used.
    debug_assert_eq!(node_bags[final_node].len(), 1);
    let mut d = [OUT; MAX_BAG];
    d[0] = 0;
    let goal = encode_canonical(&mut d, 1);
    let &(cost, _) = tables[final_node].get(&goal)?;

    if !want_tree {
        return Some((cost, Vec::new()));
    }
    // Read the tree back by walking the backpointers.
    let mut used: Vec<EdgeId> = Vec::new();
    let mut stack = vec![(final_node, goal)];
    while let Some((node, code)) = stack.pop() {
        let (_, back) = *tables[node].get(&code)?;
        match (back, &nodes[node]) {
            (Back::Leaf, _) => {}
            (Back::Unary(c), Nice::Introduce { child, .. })
            | (Back::Unary(c), Nice::Forget { child, .. })
            | (Back::Unary(c), Nice::Edge { child, .. }) => stack.push((*child, c)),
            (Back::Edge(c, id), Nice::Edge { child, .. }) => {
                used.push(id);
                stack.push((*child, c));
            }
            (Back::Join(a, c), Nice::Join { left, right }) => {
                stack.push((*left, a));
                stack.push((*right, c));
            }
            _ => return None,
        }
    }
    // The edge set is connected and spans every terminal, but it may carry
    // zero-cost cycles now that the join no longer rejects them. Take a
    // spanning tree; the module comment proves every edge this drops has cost
    // zero, and the assertion below is that proof made executable.
    let tree = spanning_tree(graph, &used);
    let dropped: Cost = used.iter().map(|&e| graph.edges[e as usize].cost).sum::<Cost>()
        - tree.iter().map(|&e| graph.edges[e as usize].cost).sum::<Cost>();
    debug_assert!(dropped < 1e-9, "spanning tree discarded {dropped} of cost");
    Some((cost - dropped, tree))
}

/// The dynamic programme with nothing packed and nothing reduced.
///
/// # Why this exists twice
///
/// The fast path above is two optimisations stacked on one recurrence: a
/// signature packed into a machine word, and the rank-based reduction of §43. It
/// is exact, but *both* optimisations are where an error would hide — §32's
/// unsoundness was one of them — and neither can be checked against the other,
/// because the reduced table is not the naive table and is not meant to be.
///
/// This module is the recurrence with neither. Signatures are `Vec<u8>` over bag
/// positions, so there is no width ceiling and no reserved sentinel value; every
/// reachable state is kept, so the table at a node is the *definition* the
/// reduction is a representative subset of. It is deliberately slow.
///
/// It serves two purposes:
///
/// 1. **The differential oracle.** The packed DP must agree with it on the final
///    value for every instance both can address, and at partition level the
///    reduced table must answer every connectivity query at the raw table's cost.
/// 2. **The instrument.** [`RawCensus`] records the raw reachable table size per
///    `S`-class as a function of bag size — the measurement that decides whether
///    the rank reduction is needed at a given width at all, since its cost is
///    `2^{|S|-1}` bits per state whatever the table actually holds.
pub mod reference {
    use std::collections::HashMap;
    use std::time::Instant;

    use super::{Cost, Nice, TreeDecomposition};
    use crate::graph::{NodeId, UndirectedGraph};

    /// Block index meaning "this bag position is not in `S`".
    const NONE: u8 = u8::MAX;

    /// A signature: one block index per bag position, [`NONE`] where unused.
    type Sig = Vec<u8>;

    /// The raw reachable table sizes, aggregated by `(bag positions, |S|)`.
    ///
    /// The values are `(classes seen, total states, largest class)`. The largest
    /// column is the one that matters: the rank reduction can only pay when a
    /// class is larger than the `2^{|S|-1}` bound it reduces to, and it costs
    /// `2^{|S|-1}` bits per state offered whether it pays or not.
    #[derive(Debug, Clone, Default)]
    pub struct RawCensus {
        pub by_class: std::collections::BTreeMap<(u32, u32), (u64, u64, u32)>,
        /// The same, after the rank reduction, when it was run and affordable.
        pub reduced_by_class: std::collections::BTreeMap<(u32, u32), (u64, u64, u32)>,
        pub nodes: u64,
        pub peak_live: usize,
        pub joins: u64,
        pub join_pairs: f64,
        /// Bytes the widest basis held, and the `|S|` it held them at. The
        /// reduction's footprint at a class is `rank * 2^{|S|-1}` bits, which is
        /// the quantity that decides whether a width is reachable at all.
        pub basis_bytes: u64,
        pub basis_at_s: u32,
        /// Classes the reduction was not run on because its basis would not fit.
        pub reduction_refused: u64,
        /// Set when the run stopped on the state cap or the deadline; the
        /// aggregates are then a lower bound on what a full run would have seen.
        pub aborted: bool,
    }

    impl RawCensus {
        fn record(&mut self, b: usize, s: usize, size: usize) {
            let e = self.by_class.entry((b as u32, s as u32)).or_insert((0, 0, 0));
            e.0 += 1;
            e.1 += size as u64;
            e.2 = e.2.max(size as u32);
        }

        fn record_reduced(&mut self, b: usize, s: usize, size: usize) {
            let e = self.reduced_by_class.entry((b as u32, s as u32)).or_insert((0, 0, 0));
            e.0 += 1;
            e.1 += size as u64;
            e.2 = e.2.max(size as u32);
        }

        /// The largest raw class observed at any bag size, and the `2^{s-1}`
        /// bound the rank reduction would replace it by.
        pub fn worst(&self) -> Option<(u32, u32, u32, f64)> {
            self.by_class
                .iter()
                .map(|(&(b, s), &(_, _, mx))| {
                    (b, s, mx, if s == 0 { 1.0 } else { (1u64 << (s - 1).min(62)) as f64 })
                })
                .max_by_key(|t| t.2)
        }
    }

    /// The rank-based reduction of §43, restated over dynamically sized ground
    /// sets so it can be *measured* at bag sizes the packed encoding cannot
    /// address.
    ///
    /// The algorithm is exactly [`super::rankreduce::Basis`]'s and rests on the
    /// same two statements — the inner-product identity and the representation
    /// theorem — so nothing new is being claimed; what is new is that the cut
    /// vector is `2^{|S|-1}` bits of *heap*, so the footprint the reduction pays
    /// is observable rather than bounded by a compile-time constant.
    ///
    /// `budget_bytes` bounds the rows the basis will hold. Exhausting it is not
    /// an error and does not cost exactness: [`DynBasis::offer`] then returns
    /// `None`, and a caller that keeps every remaining candidate holds a
    /// *superset* of a representative set, which answers every connectivity
    /// query at the same cost the full table does.
    pub struct DynBasis {
        bits: usize,
        words: usize,
        rows: Vec<Vec<u64>>,
        pivots: Vec<usize>,
        budget_bytes: u64,
    }

    impl DynBasis {
        pub fn new(s: usize, budget_bytes: u64) -> DynBasis {
            let bits = if s <= 1 { 1 } else { 1usize << (s - 1) };
            let words = bits.div_ceil(64);
            DynBasis { bits, words, rows: Vec::new(), pivots: Vec::new(), budget_bytes }
        }

        pub fn is_full(&self) -> bool {
            self.rows.len() >= self.bits
        }

        pub fn bytes(&self) -> u64 {
            self.rows.len() as u64 * self.words as u64 * 8
        }

        fn would_exceed(&self) -> bool {
            (self.rows.len() as u64 + 1) * self.words as u64 * 8 > self.budget_bytes
        }

        /// `Some(true)` to keep, `Some(false)` to drop, `None` when the basis
        /// has run out of budget and the caller must keep everything after.
        pub fn offer(&mut self, d: &[u8], used: &[usize]) -> Option<bool> {
            if used.len() <= 1 {
                // One partition exists; the first offer is it.
                if self.rows.is_empty() {
                    self.rows.push(vec![0u64; self.words]);
                    self.pivots.push(0);
                    return Some(true);
                }
                return Some(false);
            }
            let mut v = vec![0u64; self.words];
            cut_vector(d, used, &mut v);
            for (bi, &p) in self.pivots.iter().enumerate() {
                if v[p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..self.words {
                        v[w] ^= self.rows[bi][w];
                    }
                }
            }
            let Some(p) = (0..self.bits).find(|&c| v[c >> 6] >> (c & 63) & 1 == 1) else {
                return Some(false);
            };
            if self.would_exceed() {
                return None;
            }
            for bi in 0..self.rows.len() {
                if self.rows[bi][p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..self.words {
                        self.rows[bi][w] ^= v[w];
                    }
                }
            }
            self.rows.push(v);
            self.pivots.push(p);
            Some(true)
        }
    }

    /// The cut vector of a signature over the positions it uses. Identical to
    /// [`super::rankreduce`]'s, over a slice rather than a fixed array.
    fn cut_vector(d: &[u8], used: &[usize], out: &mut [u64]) {
        out.iter_mut().for_each(|w| *w = 0);
        let s = used.len();
        if s == 0 {
            return;
        }
        let mut block_mask = vec![0u64; s];
        let mut label = vec![usize::MAX; d.len() + 1];
        let mut nblocks = 0usize;
        let mut home = usize::MAX;
        for (i, &pos) in used.iter().enumerate() {
            let raw = d[pos] as usize;
            let b = if label[raw] == usize::MAX {
                label[raw] = nblocks;
                nblocks += 1;
                nblocks - 1
            } else {
                label[raw]
            };
            if i == 0 {
                home = b;
            } else {
                block_mask[b] |= 1 << (i - 1);
            }
        }
        let others: Vec<u64> =
            (0..nblocks).filter(|&b| b != home).map(|b| block_mask[b]).collect();
        let k = others.len();
        for t in 0..(1usize << k) {
            let mut x = block_mask[home];
            let mut tt = t;
            while tt != 0 {
                let i = tt.trailing_zeros() as usize;
                x |= others[i];
                tt &= tt - 1;
            }
            let col = x as usize;
            out[col >> 6] |= 1 << (col & 63);
        }
    }

    /// Reduce one `S`-class, cheapest first. Returns the kept entries.
    ///
    /// Once the basis refuses, every remaining candidate is kept — a superset of
    /// a representative set is still a representative set.
    fn reduce_class(mut entries: Vec<(Sig, Cost)>, used: &[usize], budget: u64) -> (Vec<(Sig, Cost)>, u64, bool) {
        entries.sort_by(|a, b| a.1.total_cmp(&b.1));
        let mut basis = DynBasis::new(used.len(), budget);
        let mut out = Vec::new();
        let mut refused = false;
        for (sig, cost) in entries {
            // A full basis spans the cut space, so every later candidate is a
            // combination of kept ones of no greater cost: the theorem's own
            // hypothesis, and the rest may be dropped. A *refused* basis proves
            // nothing about what follows, so everything after it is kept.
            if !refused && basis.is_full() {
                break;
            }
            if refused {
                out.push((sig, cost));
                continue;
            }
            match basis.offer(&sig, used) {
                Some(true) => out.push((sig, cost)),
                Some(false) => {}
                None => {
                    refused = true;
                    out.push((sig, cost));
                }
            }
        }
        let bytes = basis.bytes();
        (out, bytes, refused)
    }

    fn canon(d: &mut [u8]) {
        let n = d.len();
        let mut map = vec![NONE; n + 1];
        let mut next = 0u8;
        for j in 0..n {
            let x = d[j];
            if x == NONE {
                continue;
            }
            if map[x as usize] == NONE {
                map[x as usize] = next;
                next += 1;
            }
            d[j] = map[x as usize];
        }
    }

    fn used_mask(d: &[u8]) -> u64 {
        let mut m = 0u64;
        for (j, &x) in d.iter().enumerate() {
            if x != NONE {
                m |= 1 << j;
            }
        }
        m
    }

    fn free_block(d: &[u8]) -> u8 {
        let mut used = vec![false; d.len() + 1];
        for &x in d {
            if x != NONE {
                used[x as usize] = true;
            }
        }
        (0..d.len()).find(|&k| !used[k]).unwrap_or(0) as u8
    }

    /// Re-express a signature over `from` as one over `to`, keeping each
    /// vertex's block; positions of `to` absent from `from` become unused.
    fn rebase(d: &[u8], from: &[u32], to: &[u32]) -> Sig {
        let mut out = vec![NONE; to.len()];
        let mut i = 0usize;
        for (j, &v) in to.iter().enumerate() {
            while i < from.len() && from[i] < v {
                i += 1;
            }
            if i < from.len() && from[i] == v {
                out[j] = d[i];
            }
        }
        canon(&mut out);
        out
    }

    fn relax(t: &mut HashMap<Sig, Cost>, k: Sig, c: Cost) {
        match t.get_mut(&k) {
            Some(slot) if *slot <= c + 1e-12 => {}
            Some(slot) => *slot = c,
            None => {
                t.insert(k, c);
            }
        }
    }

    /// The join of two signatures over the same used set, by union-find.
    fn union_partitions(l: &[u8], r: &[u8]) -> Option<Sig> {
        let b = l.len();
        let mut uf: Vec<u8> = (0..b as u8).collect();
        fn find(uf: &mut [u8], mut x: u8) -> u8 {
            while uf[x as usize] != x {
                uf[x as usize] = uf[uf[x as usize] as usize];
                x = uf[x as usize];
            }
            x
        }
        for j in 0..b {
            if (l[j] == NONE) != (r[j] == NONE) {
                return None;
            }
        }
        for side in [l, r] {
            for j in 0..b {
                if side[j] == NONE {
                    continue;
                }
                for k in j + 1..b {
                    if side[k] == side[j] {
                        let (a, c) = (find(&mut uf, j as u8), find(&mut uf, k as u8));
                        uf[a as usize] = c;
                    }
                }
            }
        }
        let mut out = vec![NONE; b];
        for j in 0..b {
            if l[j] != NONE {
                out[j] = find(&mut uf, j as u8);
            }
        }
        canon(&mut out);
        Some(out)
    }

    /// Least cost of a tree spanning `terminals`, by the unreduced recurrence.
    ///
    /// Returns `None` exactly when the packed path would: an infeasible or
    /// disconnected instance, a decomposition without a single root, negative
    /// costs, or a cap hit. `census` is appended to whether or not the run
    /// completes, with [`RawCensus::aborted`] recording which.
    pub fn raw_dp(
        graph: &UndirectedGraph,
        terminals: &[NodeId],
        td: &TreeDecomposition,
        state_cap: usize,
        deadline: Option<Instant>,
        census: &mut RawCensus,
    ) -> Option<Cost> {
        dp(graph, terminals, td, state_cap, deadline, None, census)
    }

    /// The same recurrence with the rank reduction applied per `S`-class.
    ///
    /// `basis_budget` is the bytes one class's basis may hold; `None` runs the
    /// recurrence raw. The reduction is exact either way — see [`DynBasis`] for
    /// why exhausting the budget costs nothing but size — so this function and
    /// [`raw_dp`] must return the same value, which is what
    /// `the_reduction_does_not_change_the_reference_value` checks.
    pub fn dp(
        graph: &UndirectedGraph,
        terminals: &[NodeId],
        td: &TreeDecomposition,
        state_cap: usize,
        deadline: Option<Instant>,
        basis_budget: Option<u64>,
        census: &mut RawCensus,
    ) -> Option<Cost> {
        if terminals.is_empty() {
            return Some(0.0);
        }
        let super::Prepared { nodes, node_bags, final_node, is_terminal } =
            super::prepare(graph, terminals, td, 64)?;

        let mut tables: Vec<HashMap<Sig, Cost>> = vec![HashMap::new(); nodes.len()];
        let mut live = 0usize;

        for i in 0..nodes.len() {
            let bag = &node_bags[i];
            let b = bag.len();
            let mut table: HashMap<Sig, Cost> = HashMap::new();
            match nodes[i].clone() {
                Nice::Leaf => {
                    table.insert(Vec::new(), 0.0);
                }
                Nice::Introduce { child, v } => {
                    let cb = &node_bags[child];
                    let vp = bag.binary_search(&v).ok()?;
                    for (code, &cost) in &tables[child] {
                        let base = rebase(code, cb, bag);
                        let mut with = base.clone();
                        with[vp] = free_block(&with);
                        canon(&mut with);
                        relax(&mut table, base, cost);
                        relax(&mut table, with, cost);
                    }
                }
                Nice::Forget { child, v } => {
                    let cb = &node_bags[child];
                    let vp = cb.binary_search(&v).ok()?;
                    let terminal = is_terminal[v as usize];
                    for (code, &cost) in &tables[child] {
                        if code[vp] == NONE {
                            if terminal {
                                continue;
                            }
                        } else if (0..cb.len()).all(|j| j == vp || code[j] != code[vp]) {
                            // Alone in its block: forgetting it orphans the
                            // component it is the whole of.
                            continue;
                        }
                        let out = rebase(code, cb, bag);
                        relax(&mut table, out, cost);
                    }
                }
                Nice::Edge { child, u, w, cost: ec, id: _ } => {
                    let up = bag.binary_search(&u).ok()?;
                    let wp = bag.binary_search(&w).ok()?;
                    for (code, &cost) in &tables[child] {
                        relax(&mut table, code.clone(), cost);
                        if code[up] == NONE || code[wp] == NONE || code[up] == code[wp] {
                            continue;
                        }
                        let mut d = code.clone();
                        let (keep, drop) = (d[up], d[wp]);
                        for x in d.iter_mut() {
                            if *x == drop {
                                *x = keep;
                            }
                        }
                        canon(&mut d);
                        relax(&mut table, d, cost + ec);
                    }
                }
                Nice::Join { left, right } => {
                    let mut by_class: HashMap<u64, (Vec<(&Sig, Cost)>, Vec<(&Sig, Cost)>)> =
                        HashMap::new();
                    for (code, &cost) in &tables[left] {
                        by_class.entry(used_mask(code)).or_default().0.push((code, cost));
                    }
                    for (code, &cost) in &tables[right] {
                        by_class.entry(used_mask(code)).or_default().1.push((code, cost));
                    }
                    census.joins += 1;
                    for (_, (l, r)) in &by_class {
                        census.join_pairs += l.len() as f64 * r.len() as f64;
                        for (lp, lc) in l {
                            for (rp, rc) in r {
                                if let Some(j) = union_partitions(lp, rp) {
                                    relax(&mut table, j, lc + rc);
                                }
                            }
                        }
                    }
                }
            }
            if table.is_empty() {
                return None;
            }
            census.nodes += 1;
            // The raw class sizes, which is the whole point of the instrument.
            let mut sizes: HashMap<u64, usize> = HashMap::new();
            for code in table.keys() {
                *sizes.entry(used_mask(code)).or_insert(0) += 1;
            }
            for (&m, &sz) in &sizes {
                census.record(b, m.count_ones() as usize, sz);
            }
            if let Some(budget) = basis_budget {
                let mut by_class: HashMap<u64, Vec<(Sig, Cost)>> = HashMap::new();
                for (sig, cost) in table.drain() {
                    by_class.entry(used_mask(&sig)).or_default().push((sig, cost));
                }
                for (m, entries) in by_class {
                    let used: Vec<usize> = (0..b).filter(|&j| m >> j & 1 == 1).collect();
                    let (kept, bytes, refused) = reduce_class(entries, &used, budget);
                    if bytes > census.basis_bytes {
                        census.basis_bytes = bytes;
                        census.basis_at_s = used.len() as u32;
                    }
                    census.reduction_refused += u64::from(refused);
                    census.record_reduced(b, used.len(), kept.len());
                    for (sig, cost) in kept {
                        table.insert(sig, cost);
                    }
                }
            }
            live += table.len();
            census.peak_live = census.peak_live.max(live);
            if live > state_cap || deadline.is_some_and(|d| Instant::now() >= d) {
                census.aborted = true;
                return None;
            }
            tables[i] = table;
            for child in match &nodes[i] {
                Nice::Leaf => Vec::new(),
                Nice::Introduce { child, .. }
                | Nice::Forget { child, .. }
                | Nice::Edge { child, .. } => vec![*child],
                Nice::Join { left, right } => vec![*left, *right],
            } {
                live -= tables[child].len();
                tables[child] = HashMap::new();
            }
        }

        debug_assert_eq!(node_bags[final_node].len(), 1);
        tables[final_node].get(&vec![0u8]).copied()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn all_partitions(s: usize) -> Vec<Sig> {
            let mut out = Vec::new();
            fn grow(i: usize, used: u8, a: &mut Vec<u8>, s: usize, out: &mut Vec<Sig>) {
                if i == s {
                    out.push(a.clone());
                    return;
                }
                for v in 0..=used {
                    a[i] = v;
                    grow(i + 1, used.max(v + 1), a, s, out);
                }
            }
            let mut a = vec![0u8; s];
            grow(0, 0, &mut a, s, &mut out);
            out
        }

        /// Whether `p join q` is the one-block partition.
        fn joins_connected(p: &[u8], q: &[u8]) -> bool {
            let s = p.len();
            let mut uf: Vec<usize> = (0..s).collect();
            fn find(uf: &mut Vec<usize>, mut x: usize) -> usize {
                while uf[x] != x {
                    uf[x] = uf[uf[x]];
                    x = uf[x];
                }
                x
            }
            for side in [p, q] {
                for j in 0..s {
                    for k in j + 1..s {
                        if side[j] == side[k] {
                            let (a, b) = (find(&mut uf, j), find(&mut uf, k));
                            uf[a] = b;
                        }
                    }
                }
            }
            (0..s).all(|j| find(&mut uf, j) == find(&mut uf, 0))
        }

        /// The representation theorem, over every partition of every ground set
        /// up to size seven.
        ///
        /// This is the same gate `rankreduce::reduction_preserves_every_completion`
        /// applies to the packed basis, restated for the dynamically sized one:
        /// for **every** query `q`, the least weight among kept partitions that
        /// join `q` to a single block equals the least weight among all of them.
        /// It is a connectivity query and not an identity — the kept set is not
        /// the input set and is not meant to be.
        #[test]
        fn the_dynamic_reduction_preserves_every_completion() {
            let mut st = 0x1357_9BDF_2468_ACE0u64;
            let mut rng = move || {
                st ^= st << 13;
                st ^= st >> 7;
                st ^= st << 17;
                st
            };
            for s in 1..=7usize {
                let parts = all_partitions(s);
                let used: Vec<usize> = (0..s).collect();
                for _ in 0..60 {
                    let mut entries: Vec<(Sig, Cost)> = Vec::new();
                    for p in &parts {
                        if rng() % 3 != 0 {
                            entries.push((p.clone(), (rng() % 50) as Cost));
                        }
                    }
                    if entries.is_empty() {
                        continue;
                    }
                    let (kept, _, refused) = reduce_class(entries.clone(), &used, 1 << 20);
                    assert!(!refused);
                    assert!(
                        kept.len() <= if s <= 1 { 1 } else { 1usize << (s - 1) },
                        "kept {} at s={s}",
                        kept.len()
                    );
                    for q in &parts {
                        let full = entries
                            .iter()
                            .filter(|(p, _)| joins_connected(p, q))
                            .map(|(_, c)| *c)
                            .fold(Cost::INFINITY, Cost::min);
                        let red = kept
                            .iter()
                            .filter(|(p, _)| joins_connected(p, q))
                            .map(|(_, c)| *c)
                            .fold(Cost::INFINITY, Cost::min);
                        assert!(
                            (full - red).abs() < 1e-9 || (full.is_infinite() && red.is_infinite()),
                            "s={s} query {q:?}: full {full} reduced {red}"
                        );
                    }
                }
            }
        }

        /// A basis that runs out of budget keeps everything it has not decided,
        /// which is a superset of a representative set — so the preserved
        /// minimum is preserved a fortiori, and the value cannot move.
        #[test]
        fn an_exhausted_basis_keeps_the_answer() {
            let s = 6usize;
            let parts = all_partitions(s);
            let used: Vec<usize> = (0..s).collect();
            let entries: Vec<(Sig, Cost)> =
                parts.iter().enumerate().map(|(i, p)| (p.clone(), i as Cost)).collect();
            // One row of eight bytes: the basis refuses after the first keep.
            let (kept, _, refused) = reduce_class(entries.clone(), &used, 8);
            assert!(refused);
            for q in &parts {
                let full = entries
                    .iter()
                    .filter(|(p, _)| joins_connected(p, q))
                    .map(|(_, c)| *c)
                    .fold(Cost::INFINITY, Cost::min);
                let red = kept
                    .iter()
                    .filter(|(p, _)| joins_connected(p, q))
                    .map(|(_, c)| *c)
                    .fold(Cost::INFINITY, Cost::min);
                assert!((full - red).abs() < 1e-9 || (full.is_infinite() && red.is_infinite()));
            }
        }
    }
}

/// A spanning forest of `used`, by union-find over the endpoints.
fn spanning_tree(graph: &UndirectedGraph, used: &[EdgeId]) -> Vec<EdgeId> {
    let mut uf: HashMap<NodeId, NodeId> = HashMap::new();
    fn find(uf: &mut HashMap<NodeId, NodeId>, x: NodeId) -> NodeId {
        let mut r = x;
        while let Some(&p) = uf.get(&r) {
            if p == r {
                break;
            }
            r = p;
        }
        uf.insert(x, r);
        r
    }
    let mut out = Vec::with_capacity(used.len());
    for &id in used {
        let e = &graph.edges[id as usize];
        uf.entry(e.src).or_insert(e.src);
        uf.entry(e.dst).or_insert(e.dst);
        let (a, c) = (find(&mut uf, e.src), find(&mut uf, e.dst));
        if a != c {
            uf.insert(a, c);
            out.push(id);
        }
    }
    out
}

/// Nice-ify: expand each decomposition node into introduce/forget chains, join
/// its children pairwise, and introduce the edges assigned to it.
///
/// Returns the node list, each node's bag, and the index of the final node,
/// whose bag is `{r}`.
fn build_nice(
    td: &TreeDecomposition,
    bags: &[Vec<u32>],
    edges_at: &[Vec<(u32, u32, Cost, EdgeId)>],
) -> Option<(Vec<Nice>, Vec<Vec<u32>>, usize)> {
    let mut nodes: Vec<Nice> = Vec::new();
    let mut node_bags: Vec<Vec<u32>> = Vec::new();
    let push = |n: Nice, bag: Vec<u32>, nodes: &mut Vec<Nice>, nb: &mut Vec<Vec<u32>>| {
        nodes.push(n);
        nb.push(bag);
        nodes.len() - 1
    };

    // `parent[i] > i` makes the identity order a post-order, so a bag's
    // children are already built when it is reached.
    let mut top: Vec<usize> = vec![usize::MAX; bags.len()];
    for i in 0..bags.len() {
        let target = &bags[i];
        let mut merged: Option<usize> = None;
        for &c in &td.children[i] {
            let mut cur = top[c];
            let mut cur_bag = node_bags[cur].clone();
            // Forget first, then introduce: the bag never exceeds the larger of
            // the two it interpolates between.
            for &v in &node_bags[top[c]].clone() {
                if target.binary_search(&v).is_err() {
                    let mut nb = cur_bag.clone();
                    nb.retain(|&x| x != v);
                    cur = push(Nice::Forget { child: cur, v }, nb.clone(), &mut nodes, &mut node_bags);
                    cur_bag = nb;
                }
            }
            for &v in target {
                if cur_bag.binary_search(&v).is_err() {
                    let mut nb = cur_bag.clone();
                    nb.push(v);
                    nb.sort_unstable();
                    cur = push(Nice::Introduce { child: cur, v }, nb.clone(), &mut nodes, &mut node_bags);
                    cur_bag = nb;
                }
            }
            merged = Some(match merged {
                None => cur,
                Some(prev) => push(
                    Nice::Join { left: prev, right: cur },
                    target.clone(),
                    &mut nodes,
                    &mut node_bags,
                ),
            });
        }
        let mut cur = match merged {
            Some(m) => m,
            None => {
                // A leaf of the decomposition: introduce the bag from nothing.
                let mut cur = push(Nice::Leaf, Vec::new(), &mut nodes, &mut node_bags);
                let mut cur_bag: Vec<u32> = Vec::new();
                for &v in target {
                    cur_bag.push(v);
                    cur_bag.sort_unstable();
                    cur = push(
                        Nice::Introduce { child: cur, v },
                        cur_bag.clone(),
                        &mut nodes,
                        &mut node_bags,
                    );
                }
                cur
            }
        };
        for &(u, w, cost, id) in &edges_at[i] {
            cur = push(
                Nice::Edge { child: cur, u, w, cost, id },
                target.clone(),
                &mut nodes,
                &mut node_bags,
            );
        }
        top[i] = cur;
    }

    // Forget down from the single root to `{r}`. `r` is in every bag, so it is
    // the one vertex that must survive.
    let root = *td.roots.first()?;
    let mut cur = top[root];
    let mut cur_bag = node_bags[cur].clone();
    let keep = *bags[root].first().filter(|_| bags[root].len() == 1).unwrap_or(&u32::MAX);
    // `r` is whichever vertex all bags share; recover it as the one in every bag.
    let r = if keep != u32::MAX {
        keep
    } else {
        *bags
            .iter()
            .fold(bags[0].clone(), |acc, b| {
                acc.into_iter().filter(|v| b.binary_search(v).is_ok()).collect()
            })
            .first()?
    };
    for &v in &cur_bag.clone() {
        if v != r {
            let mut nb = cur_bag.clone();
            nb.retain(|&x| x != v);
            cur = push(Nice::Forget { child: cur, v }, nb.clone(), &mut nodes, &mut node_bags);
            cur_bag = nb;
        }
    }
    Some((nodes, node_bags, cur))
}

/// Apply the rank-based reduction to every `S`-class of one node's table.
///
/// Signatures with different `S` never interact — every transition preserves or
/// changes `S` uniformly — so each class is reduced on its own.
fn reduce_table(
    table: HashMap<u64, (Cost, Back)>,
    b: usize,
) -> HashMap<u64, (Cost, Back)> {
    let mut classes: HashMap<u32, Vec<(u64, Cost, Back)>> = HashMap::new();
    for (code, (cost, back)) in table {
        classes.entry(used_mask(code, b)).or_default().push((code, cost, back));
    }
    let mut out = HashMap::new();
    for (mask, entries) in classes {
        let used: Vec<usize> = (0..b).filter(|&j| mask & (1 << j) != 0).collect();
        // A class of one, or a ground set of one, has nothing to span.
        if entries.len() <= 1 || used.len() <= 1 {
            for (code, cost, back) in entries {
                out.insert(code, (cost, back));
            }
            continue;
        }
        let decoded: Vec<[u8; MAX_BAG]> = entries.iter().map(|&(c, _, _)| decode(c, b)).collect();
        let costs: Vec<Cost> = entries.iter().map(|&(_, c, _)| c).collect();
        let order = rankreduce::by_cost(&costs);
        for i in rankreduce::reduce(&decoded, &used, &order) {
            let (code, cost, back) = entries[i];
            out.insert(code, (cost, back));
        }
    }
    out
}

/// Keep the cheaper of an existing entry and a new one.
#[inline]
fn relax(table: &mut HashMap<u64, (Cost, Back)>, code: u64, cost: Cost, back: Back) {
    match table.get_mut(&code) {
        Some(slot) if slot.0 <= cost + 1e-12 => {}
        Some(slot) => *slot = (cost, back),
        None => {
            table.insert(code, (cost, back));
        }
    }
}

#[inline]
fn decode(code: u64, b: usize) -> [u8; MAX_BAG] {
    let mut d = [OUT; MAX_BAG];
    for (j, slot) in d.iter_mut().enumerate().take(b) {
        *slot = ((code >> (4 * j)) & 0xF) as u8;
    }
    d
}

/// Renumber blocks by first appearance and pack. Canonical form is what makes
/// two states equal exactly when they describe the same partition.
#[inline]
fn encode_canonical(d: &mut [u8; MAX_BAG], b: usize) -> u64 {
    let mut map = [OUT; MAX_BAG + 1];
    let mut next = 0u8;
    let mut code = 0u64;
    for j in 0..b {
        let x = d[j];
        let id = if x == OUT {
            OUT
        } else {
            if map[x as usize] == OUT {
                map[x as usize] = next;
                next += 1;
            }
            map[x as usize]
        };
        d[j] = id;
        code |= (id as u64) << (4 * j);
    }
    for j in b..MAX_BAG {
        code |= (OUT as u64) << (4 * j);
    }
    code
}

/// The lowest block index not in use, for a newly introduced isolated vertex.
#[inline]
fn free_block(d: &[u8; MAX_BAG], b: usize) -> u8 {
    let mut used = 0u16;
    for j in 0..b {
        if d[j] != OUT {
            used |= 1 << d[j];
        }
    }
    (0..OUT).find(|&k| used & (1 << k) == 0).unwrap_or(0)
}

/// Which bag positions the state uses, as a bitmask.
#[inline]
fn used_mask(code: u64, b: usize) -> u32 {
    let mut m = 0u32;
    for j in 0..b {
        if ((code >> (4 * j)) & 0xF) as u8 != OUT {
            m |= 1 << j;
        }
    }
    m
}

/// The join of two partitions of the same set, by union-find over bag positions.
/// `None` when the two disagree on which positions are used.
fn union_partitions(l: &[u8; MAX_BAG], r: &[u8; MAX_BAG], b: usize) -> Option<[u8; MAX_BAG]> {
    let mut uf: [u8; MAX_BAG] = [0; MAX_BAG];
    for (j, slot) in uf.iter_mut().enumerate() {
        *slot = j as u8;
    }
    fn find(uf: &mut [u8; MAX_BAG], mut x: u8) -> u8 {
        while uf[x as usize] != x {
            uf[x as usize] = uf[uf[x as usize] as usize];
            x = uf[x as usize];
        }
        x
    }
    for j in 0..b {
        if (l[j] == OUT) != (r[j] == OUT) {
            return None;
        }
    }
    for side in [l, r] {
        for j in 0..b {
            if side[j] == OUT {
                continue;
            }
            for k in j + 1..b {
                if side[k] == side[j] {
                    let (a, c) = (find(&mut uf, j as u8), find(&mut uf, k as u8));
                    uf[a as usize] = c;
                }
            }
        }
    }
    let mut out = [OUT; MAX_BAG];
    for j in 0..b {
        if l[j] != OUT {
            out[j] = find(&mut uf, j as u8);
        }
    }
    Some(out)
}

/// Re-express a signature over `from` as one over `to`, keeping each vertex's
/// block. Positions of `to` absent from `from` become unused.
fn rebase(code: u64, from: &[u32], to: &[u32], b: usize) -> u64 {
    let d = decode(code, from.len());
    let mut out = [OUT; MAX_BAG];
    let mut i = 0usize;
    for (j, &v) in to.iter().enumerate().take(b) {
        while i < from.len() && from[i] < v {
            i += 1;
        }
        if i < from.len() && from[i] == v {
            out[j] = d[i];
        }
    }
    encode_canonical(&mut out, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::{decompose, dreyfus_wagner};
    use crate::graph::NodeType;

    /// Build an undirected graph from an edge list, with `terminals` marked.
    fn make(n: u32, edges: &[(u32, u32, f64)], terminals: &[u32]) -> UndirectedGraph {
        let mut g = UndirectedGraph::new(n);
        for v in 1..=n {
            let t = terminals.contains(&v);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        for &(u, w, c) in edges {
            g.add_edge(u, w, c);
        }
        g
    }

    fn solve(g: &UndirectedGraph, terminals: &[NodeId]) -> Option<(Cost, Vec<EdgeId>)> {
        let td = decompose(g, MAX_BAG - 1, None)?;
        assert!(td.verify(g), "decomposition failed its axioms");
        let with = steiner_tree_over_decomposition(g, terminals, &td, 4_000_000, true, None);
        // The cost-only mode frees each table once its parent is built, which
        // must not change the value it reports -- only whether the tree can be
        // read back.
        let without = steiner_tree_over_decomposition(g, terminals, &td, 4_000_000, false, None);
        match (&with, &without) {
            (Some((a, _)), Some((b, edges))) => {
                assert!((a - b).abs() < 1e-9, "cost-only mode reported {b} against {a}");
                assert!(edges.is_empty(), "cost-only mode returned edges");
            }
            (None, None) => {}
            _ => panic!("the two modes disagree on feasibility"),
        }
        with
    }

    /// The returned edge set really is a tree spanning the terminals, and its
    /// cost really is the reported one.
    fn check_tree(g: &UndirectedGraph, terminals: &[NodeId], cost: Cost, used: &[EdgeId]) {
        let mut sum = 0.0;
        let mut adj: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        let mut seen = std::collections::HashSet::new();
        for &id in used {
            assert!(seen.insert(id), "edge {id} used twice");
            let e = &g.edges[id as usize];
            sum += e.cost;
            adj.entry(e.src).or_default().push(e.dst);
            adj.entry(e.dst).or_default().push(e.src);
        }
        assert!((sum - cost).abs() < 1e-9, "cost {cost} but edges sum to {sum}");
        // Connected and acyclic on its vertex set.
        let verts: Vec<NodeId> = adj.keys().copied().collect();
        if verts.is_empty() {
            assert!(terminals.len() <= 1);
            return;
        }
        let mut stack = vec![verts[0]];
        let mut vis = std::collections::HashSet::new();
        vis.insert(verts[0]);
        while let Some(x) = stack.pop() {
            for &y in adj.get(&x).map_or(&[][..], |v| v.as_slice()) {
                if vis.insert(y) {
                    stack.push(y);
                }
            }
        }
        assert_eq!(vis.len(), verts.len(), "solution is disconnected");
        assert_eq!(used.len(), verts.len() - 1, "solution has a cycle");
        for &t in terminals {
            assert!(vis.contains(&t), "terminal {t} missing");
        }
    }

    /// Every partition of the positions in `mask`, as canonical signatures.
    fn partitions_of(mask: u32, b: usize) -> Vec<u64> {
        let used: Vec<usize> = (0..b).filter(|&j| mask & (1 << j) != 0).collect();
        let mut out = Vec::new();
        fn grow(k: usize, next: u8, cur: &mut Vec<u8>, used: &[usize], b: usize, out: &mut Vec<u64>) {
            if k == used.len() {
                let mut d = [OUT; MAX_BAG];
                for (i, &p) in used.iter().enumerate() {
                    d[p] = cur[i];
                }
                out.push(encode_canonical(&mut d, b));
                return;
            }
            for v in 0..=next {
                cur.push(v);
                grow(k + 1, next.max(v + 1), cur, used, b, out);
                cur.pop();
            }
        }
        grow(0, 0, &mut Vec::new(), &used, b, &mut out);
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Whether two signatures over the same used set join to one block.
    fn connects(a: u64, c: u64, b: usize) -> bool {
        let (da, dc) = (decode(a, b), decode(c, b));
        let Some(mut u) = union_partitions(&da, &dc, b) else { return false };
        let code = encode_canonical(&mut u, b);
        let d = decode(code, b);
        (0..b).filter(|&j| d[j] != OUT).all(|j| d[j] == 0)
            && (0..b).any(|j| d[j] != OUT)
    }

    /// The lazy cost-ordered join answers every connectivity query at exactly
    /// the cost the full pairwise join answers it at, on random tables over
    /// random used-set classes.
    ///
    /// This is the theorem on [`join_tables`] checked against the algorithm it
    /// replaces, at the level of the tables the DP actually manipulates rather
    /// than at the level of abstract partitions. It also checks the two
    /// invariants that make the replacement safe to dispatch on: the lazy join
    /// never pops more pairs than the naive join would form, and it never emits
    /// more states than the cut-space dimension allows.
    #[test]
    fn lazy_join_represents_the_naive_join() {
        let mut s = 0x_ABBA_1234_5678_9ABCu64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for b in 2..=5usize {
            for _ in 0..300 {
                // Two random tables. Costs are small integers so that ties are
                // frequent, which is where the two orders can disagree.
                let mut build = || {
                    let mut t: HashMap<u64, (Cost, Back)> = HashMap::new();
                    let draws = 1 + rng() % 24;
                    for _ in 0..draws {
                        let mask = (rng() as u32) & ((1u32 << b) - 1);
                        let all = partitions_of(mask, b);
                        let code = all[(rng() as usize) % all.len()];
                        let cost = (rng() % 12) as Cost;
                        relax(&mut t, code, cost, Back::Leaf);
                    }
                    t
                };
                let l = build();
                let r = build();
                if l.is_empty() || r.is_empty() {
                    continue;
                }

                // The naive join: every same-class pair.
                let mut naive: HashMap<u64, Cost> = HashMap::new();
                for (&lc, &(lw, _)) in &l {
                    for (&rc, &(rw, _)) in &r {
                        if used_mask(lc, b) != used_mask(rc, b) {
                            continue;
                        }
                        let (dl, dr) = (decode(lc, b), decode(rc, b));
                        let Some(mut d) = union_partitions(&dl, &dr, b) else { continue };
                        let code = encode_canonical(&mut d, b);
                        let e = naive.entry(code).or_insert(Cost::INFINITY);
                        if lw + rw < *e {
                            *e = lw + rw;
                        }
                    }
                }

                let before = take_join_stats();
                drop(before);
                let fast = join_tables(&l, &r, b);
                let stats = take_join_stats();
                assert!(
                    stats.pairs_popped as f64 <= stats.pairs_available,
                    "popped {} of {} available pairs",
                    stats.pairs_popped,
                    stats.pairs_available
                );

                // Every state the lazy join emits is one the naive join has, at
                // the same cost: it is a subset, not an approximation.
                for (&code, &(cost, _)) in &fast {
                    let want = naive.get(&code).copied().unwrap_or(Cost::INFINITY);
                    assert!(
                        (cost - want).abs() < 1e-9,
                        "lazy join priced {code:x} at {cost}, naive join at {want}"
                    );
                }

                // And it answers every connectivity query identically.
                let masks: std::collections::HashSet<u32> =
                    naive.keys().map(|&c| used_mask(c, b)).collect();
                for mask in masks {
                    let used_count = (mask.count_ones()) as usize;
                    assert!(
                        fast.keys().filter(|&&c| used_mask(c, b) == mask).count()
                            <= if used_count <= 1 { 1 } else { 1 << (used_count - 1) },
                        "class of {used_count} elements kept more than its cut-space dimension"
                    );
                    for q in partitions_of(mask, b) {
                        let want = naive
                            .iter()
                            .filter(|&(&c, _)| used_mask(c, b) == mask && connects(c, q, b))
                            .map(|(_, &w)| w)
                            .fold(Cost::INFINITY, Cost::min);
                        let got = fast
                            .iter()
                            .filter(|&(&c, _)| used_mask(c, b) == mask && connects(c, q, b))
                            .map(|(_, &(w, _))| w)
                            .fold(Cost::INFINITY, Cost::min);
                        assert_eq!(
                            want.is_finite(),
                            got.is_finite(),
                            "lazy join changed feasibility at b={b} mask={mask:b}"
                        );
                        if want.is_finite() {
                            assert!(
                                (want - got).abs() < 1e-9,
                                "lazy join answered {got} where the naive join answers {want}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn matches_dreyfus_wagner_on_small_graphs() {
        // Exhaustive-in-spirit enumeration: every graph the generator can make
        // in this size range, checked against an independent exact algorithm.
        // Anything the DP's recurrences get wrong — an orphan rule, the
        // acyclicity criterion, the edge-to-bag assignment — shows up as a
        // value that differs from Dreyfus-Wagner's.
        let mut s = 0x51ED_2701_ABCD_1234u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut ran = 0;
        for n in 3..=9u32 {
            for _ in 0..120 {
                let k = 2 + (rng() % (n as u64 - 1).min(4)) as u32;
                let terminals: Vec<u32> = (1..=k).collect();
                let mut edges = Vec::new();
                // A random spanning path guarantees connectivity, then random
                // chords give the graph its cycle space.
                let mut perm: Vec<u32> = (1..=n).collect();
                for i in (1..perm.len()).rev() {
                    perm.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                for w in perm.windows(2) {
                    edges.push((w[0], w[1], 1.0 + (rng() % 9) as f64));
                }
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 25 {
                            edges.push((u, v, 1.0 + (rng() % 9) as f64));
                        }
                    }
                }
                let g = make(n, &edges, &terminals);
                let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
                let Some((cost, used)) = solve(&g, &terminals) else { continue };
                assert!(
                    (cost - dw.optimal_cost).abs() < 1e-6,
                    "DP {cost} vs Dreyfus-Wagner {} on n={n} edges={edges:?}",
                    dw.optimal_cost
                );
                check_tree(&g, &terminals, cost, &used);
                ran += 1;
            }
        }
        assert!(ran > 500, "only {ran} cases ran");
    }

    /// Unit costs, so every tie the reduction can face actually happens.
    ///
    /// The rank-based reduction breaks ties by whatever order equal costs come
    /// out in, and a partition discarded on a tie is exactly the situation the
    /// forest-versus-connectivity witness describes. Weighted random graphs
    /// almost never produce those ties; a graph whose edges all cost one
    /// produces almost nothing else. This test failed on the acyclicity-filtered
    /// join that this module used to run — that is what established the bug was
    /// reachable and not only a statement about partitions.
    #[test]
    fn matches_dreyfus_wagner_with_heavy_ties() {
        let mut s = 0x7EED_0F00_D1CE_2468u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut ran = 0;
        for n in 6..=12u32 {
            for _ in 0..120 {
                let mut edges = Vec::new();
                let mut perm: Vec<u32> = (1..=n).collect();
                for i in (1..perm.len()).rev() {
                    perm.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                for w in perm.windows(2) {
                    edges.push((w[0], w[1], 1.0));
                }
                // Dense enough that bags carry three or more exposed vertices,
                // which is the smallest ground set on which the discrete
                // partition is cut-space dependent.
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            edges.push((u, v, 1.0));
                        }
                    }
                }
                let k = 3 + (rng() % 4) as u32;
                let mut terminals: Vec<u32> = Vec::new();
                while (terminals.len() as u32) < k.min(n) {
                    let t = 1 + (rng() % n as u64) as u32;
                    if !terminals.contains(&t) {
                        terminals.push(t);
                    }
                }
                terminals.sort();
                let g = make(n, &edges, &terminals);
                let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
                let Some((cost, used)) = solve(&g, &terminals) else { continue };
                assert!(
                    (cost - dw.optimal_cost).abs() < 1e-6,
                    "DP {cost} vs Dreyfus-Wagner {} on n={n} terminals={terminals:?} \
                     edges={edges:?}",
                    dw.optimal_cost
                );
                check_tree(&g, &terminals, cost, &used);
                ran += 1;
            }
        }
        assert!(ran > 500, "only {ran} cases ran");
    }

    #[test]
    fn matches_dreyfus_wagner_on_near_trees() {
        // The regime the DP is actually dispatched into: many vertices, few
        // independent cycles, and more terminals than a subset table could
        // hold in the wild — here kept small enough that Dreyfus-Wagner can
        // still adjudicate.
        let mut s = 0x0BAD_C0DE_1111_2222u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for n in 10..=22u32 {
            for _ in 0..40 {
                let mut edges = Vec::new();
                for v in 2..=n {
                    let p = 1 + (rng() % (v as u64 - 1)) as u32;
                    edges.push((p, v, 1.0 + (rng() % 20) as f64));
                }
                // A handful of chords, which is what makes it a near-tree
                // rather than a tree.
                for _ in 0..(rng() % 5) + 1 {
                    let u = 1 + (rng() % n as u64) as u32;
                    let v = 1 + (rng() % n as u64) as u32;
                    if u != v {
                        edges.push((u, v, 1.0 + (rng() % 20) as f64));
                    }
                }
                let k = 3 + (rng() % 4) as u32;
                let mut terminals: Vec<u32> = Vec::new();
                while (terminals.len() as u32) < k {
                    let t = 1 + (rng() % n as u64) as u32;
                    if !terminals.contains(&t) {
                        terminals.push(t);
                    }
                }
                terminals.sort();
                let g = make(n, &edges, &terminals);
                let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
                let Some((cost, used)) = solve(&g, &terminals) else { continue };
                assert!(
                    (cost - dw.optimal_cost).abs() < 1e-6,
                    "DP {cost} vs DW {} on n={n}",
                    dw.optimal_cost
                );
                check_tree(&g, &terminals, cost, &used);
            }
        }
    }

    #[test]
    fn handles_many_terminals_at_small_width() {
        // The property the DP exists for: indifference to the terminal count.
        // A long cycle with every second vertex a terminal has width 2 and 25
        // terminals, which no subset table could address.
        let n = 50u32;
        let mut edges = Vec::new();
        for v in 1..n {
            edges.push((v, v + 1, 1.0));
        }
        edges.push((n, 1, 1.0));
        let terminals: Vec<u32> = (1..=n).step_by(2).collect();
        let g = make(n, &edges, &terminals);
        let (cost, used) = solve(&g, &terminals).expect("solved");
        // The terminals are 1, 3, ..., 49, so the path 1-2-...-49 contains all
        // of them and costs 48. Nothing cheaper exists: a tree containing 1 and
        // 49 inside a 50-cycle must contain one of the two arcs joining them
        // whole, and the shorter arc has 48 edges.
        assert!((cost - 48.0).abs() < 1e-9, "expected 48, got {cost}");
        check_tree(&g, &terminals, cost, &used);
    }

    #[test]
    fn a_tree_input_returns_itself() {
        // On a tree the answer is the union of the terminal-to-terminal paths,
        // and the DP must find exactly that.
        let g = make(
            7,
            &[(1, 2, 3.0), (2, 3, 4.0), (2, 4, 5.0), (4, 5, 6.0), (5, 6, 7.0), (5, 7, 8.0)],
            &[1, 3, 6],
        );
        let (cost, used) = solve(&g, &[1, 3, 6]).expect("solved");
        assert!((cost - 25.0).abs() < 1e-9, "got {cost}");
        check_tree(&g, &[1, 3, 6], cost, &used);
    }

    /// The unreduced recurrence is the definition; the packed one must equal it.
    ///
    /// Dreyfus-Wagner checks the *answer*. This checks the two dynamic
    /// programmes against each other over the same nice decomposition, so a
    /// disagreement localises to the packing or the reduction rather than to the
    /// recurrence — and it is the oracle the wide encoding is gated against,
    /// since Dreyfus-Wagner cannot reach the terminal counts the wide path is
    /// for.
    #[test]
    fn reference_dp_agrees_with_the_packed_dp_and_with_dreyfus_wagner() {
        use super::reference::{raw_dp, RawCensus};
        let mut s = 0x0BAD_C0DE_1234_9999u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut ran = 0;
        for n in 3..=10u32 {
            for round in 0..90 {
                let k = 2 + (rng() % (n as u64 - 1).min(5)) as u32;
                let terminals: Vec<u32> = (1..=k).collect();
                let mut edges = Vec::new();
                let mut perm: Vec<u32> = (1..=n).collect();
                for i in (1..perm.len()).rev() {
                    perm.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                // Half the rounds are unit-cost, so the tie regime the reduction
                // is most exposed to is covered rather than sampled.
                let unit = round % 2 == 0;
                let w = |r: &mut dyn FnMut() -> u64| {
                    if unit {
                        1.0
                    } else {
                        1.0 + (r() % 9) as f64
                    }
                };
                for i in 0..perm.len() - 1 {
                    let c = w(&mut rng);
                    edges.push((perm[i], perm[i + 1], c));
                }
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            let c = w(&mut rng);
                            edges.push((u, v, c));
                        }
                    }
                }
                let g = make(n, &edges, &terminals);
                let td = match decompose(&g, MAX_BAG - 1, None) {
                    Some(t) => t,
                    None => continue,
                };
                let mut census = RawCensus::default();
                let Some(raw) = raw_dp(&g, &terminals, &td, 5_000_000, None, &mut census) else {
                    continue;
                };
                let packed =
                    steiner_tree_over_decomposition(&g, &terminals, &td, 5_000_000, false, None)
                        .expect("packed DP over a decomposition the raw one completed");
                assert!(
                    (raw - packed.0).abs() < 1e-6,
                    "raw {raw} vs packed {} on n={n} edges={edges:?}",
                    packed.0
                );
                if let Some(dw) = dreyfus_wagner(&g, &terminals) {
                    assert!(
                        (raw - dw.optimal_cost).abs() < 1e-6,
                        "raw {raw} vs Dreyfus-Wagner {} on n={n} edges={edges:?}",
                        dw.optimal_cost
                    );
                }
                assert!(census.nodes > 0 && !census.aborted);
                ran += 1;
            }
        }
        assert!(ran > 400, "only {ran} cases ran");
    }

    /// The census records a class size for every `(bag, |S|)` it builds, and the
    /// recorded maximum is a real table size rather than a bound.
    #[test]
    fn the_raw_census_counts_states_that_exist() {
        use super::reference::{raw_dp, RawCensus};
        let g = make(
            8,
            &[
                (1, 2, 1.0),
                (2, 3, 1.0),
                (3, 4, 1.0),
                (4, 5, 1.0),
                (5, 6, 1.0),
                (6, 7, 1.0),
                (7, 8, 1.0),
                (8, 1, 1.0),
                (1, 5, 3.0),
                (2, 6, 3.0),
            ],
            &[1, 3, 5, 7],
        );
        let td = decompose(&g, MAX_BAG - 1, None).expect("decomposition");
        let mut census = RawCensus::default();
        let raw = raw_dp(&g, &[1, 3, 5, 7], &td, 5_000_000, None, &mut census).expect("solved");
        let packed = steiner_tree_over_decomposition(&g, &[1, 3, 5, 7], &td, 5_000_000, false, None)
            .expect("solved")
            .0;
        assert!((raw - packed).abs() < 1e-9);
        assert!(!census.by_class.is_empty());
        let (_, _, mx, _) = census.worst().expect("a widest class");
        assert!(mx >= 1);
        // The dynamically sized reduction must not move the value.
        let mut rc = super::reference::RawCensus::default();
        let red = super::reference::dp(
            &g,
            &[1, 3, 5, 7],
            &td,
            5_000_000,
            None,
            Some(1 << 20),
            &mut rc,
        )
        .expect("solved");
        assert!((red - raw).abs() < 1e-9);
        assert!(!rc.reduced_by_class.is_empty());
        // Every recorded total is at least the recorded maximum, and at least
        // one state per class exists.
        for (_, &(classes, total, mx)) in &census.by_class {
            assert!(total >= mx as u64 && total >= classes);
        }
    }
}
