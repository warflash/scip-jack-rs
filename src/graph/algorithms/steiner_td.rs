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
//!   requires `u,w in S` and merges their blocks. Using it when `u` and `w`
//!   already share a block would close a cycle; that is excluded because costs
//!   are nonnegative, so some spanning forest of any such `F` is a partial
//!   solution with the same signature and no greater cost. Nonnegativity is
//!   checked, not assumed.
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
//!   and `P` is the join `P_1 ⊔ P_2` in the partition lattice of `S`. The union
//!   is a forest exactly when
//!
//!   ```text
//!   |P_1| + |P_2| = |S| + |P_1 ⊔ P_2|.
//!   ```
//!
//!   *Proof of the criterion.* Contract each component of `F_i` to a spanning
//!   tree of its trace on `S`: side `i` contributes `|S| - |P_i|` connections
//!   between elements of `S`. Their union is a graph on `S` with
//!   `(|S|-|P_1|) + (|S|-|P_2|)` edges and `|P_1 ⊔ P_2|` components, and a graph
//!   with `n` vertices and `k` components is a forest iff it has exactly `n - k`
//!   edges and never fewer. Rearranging gives the display, and `<=` always
//!   holds. Cycles in the union are excluded for the same nonnegativity reason
//!   as above. QED
//!
//! # The answer
//!
//! The decomposition of a connected graph produced by the elimination game has
//! a single root bag; forgetting down from it leaves the bag `{r}`, and the
//! entry `c(S={r}, P={{r}})` is the cost of a least-cost forest in `G` in which
//! every terminal appears and every component meets `{r}` — that is, a
//! least-cost tree containing every terminal. That is the Steiner minimum tree.
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
        let b = (bag.len() + extra).min(BELL.len() - 2);
        let states = BELL[b + 1];
        // One introduce or forget node per bag vertex, plus the edges assigned
        // here; each sweeps the table once.
        work += (b as f64 + 1.0) * states;
        // Every child past the first is a join, which pairs the two tables.
        let joins = td.children[i].len().saturating_sub(1) as f64;
        work += joins * states * states;
    }
    // Edges are assigned one per bag on average; charge them at the widest bag
    // rather than tracking the assignment, which the caller has not made yet.
    let widest = td.bags.iter().map(|b| b.len()).max().unwrap_or(0) + extra;
    work += num_edges as f64 * BELL[(widest + 1).min(BELL.len() - 1)];
    work
}

/// Table entries this dynamic programme touches per second, measured.
///
/// The same shape as [`crate::model::HYP_UNITS_PER_SECOND`]: a machine constant
/// that turns the work estimate above into a predicted running time, so a
/// caller can decide *before starting* whether an attempt fits in the time it
/// has. That decision has to be made in advance — an attempt that runs out of
/// clock costs its whole budget and returns nothing.
pub const TD_UNITS_PER_SECOND: f64 = 2.0e7;

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
/// The quantity the whole DP eventually reports is
/// `min { w(p) : p ⊔ q = {S} }` for the single query `q` that closes the tree at
/// the root bag. Every operation between here and there — introducing a vertex,
/// forgetting one, taking an edge, joining two children — extends a partial
/// solution, and *some* extension of a partial solution completes it into a tree
/// exactly when the partition it carries joins with the partition of that
/// extension to the single block. So the theorem's guarantee is precisely the
/// invariant the DP needs: replacing a table by a representative set cannot
/// change, for any way the rest of the tree might complete, the least cost at
/// which it can be completed. Costs are only ever added on the way up, so the
/// minimum is preserved with its weight.
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

    /// Keep a minimum-weight representative subset of `entries`.
    ///
    /// `entries` is `(code, cost, payload)` and must be sorted by cost
    /// ascending; the returned indices are those to keep.
    pub fn reduce(
        decoded: &[[u8; MAX_BAG]],
        used: &[usize],
        order: &[usize],
    ) -> Vec<usize> {
        let s = used.len();
        if s <= 1 {
            // A single element admits one partition, so nothing can be dropped
            // and no work is needed.
            return order.to_vec();
        }
        let bits = 1usize << (s - 1);
        let words = bits.div_ceil(64).min(MAX_WORDS);
        let mut basis: Vec<Vec<u64>> = Vec::new();
        let mut pivots: Vec<usize> = Vec::new();
        let mut keep = Vec::new();
        let mut row = vec![0u64; words];
        for &i in order {
            cut_vector(&decoded[i], used, &mut row);
            let mut v = row.clone();
            for (bi, &p) in pivots.iter().enumerate() {
                if v[p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..words {
                        v[w] ^= basis[bi][w];
                    }
                }
            }
            // The leading set bit, if the vector survived reduction.
            let Some(p) = (0..bits).find(|&c| v[c >> 6] >> (c & 63) & 1 == 1) else {
                continue;
            };
            // Normalise the basis so later reductions stay a single pass.
            for (bi, &q) in pivots.iter().enumerate() {
                let _ = q;
                if basis[bi][p >> 6] >> (p & 63) & 1 == 1 {
                    for w in 0..words {
                        basis[bi][w] ^= v[w];
                    }
                }
            }
            basis.push(v);
            pivots.push(p);
            keep.push(i);
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
pub fn steiner_tree_over_decomposition(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    td: &TreeDecomposition,
    state_cap: usize,
    deadline: Option<std::time::Instant>,
) -> Option<(Cost, Vec<EdgeId>)> {
    if terminals.is_empty() {
        return Some((0.0, Vec::new()));
    }
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
        if bag.len() > MAX_BAG {
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

    // The tables, one per nice node, sparse.
    let mut tables: Vec<HashMap<u64, (Cost, Back)>> = vec![HashMap::new(); nodes.len()];
    let mut total_states = 0usize;

    for i in 0..nodes.len() {
        let bag = &node_bags[i];
        let b = bag.len();
        let mut table: HashMap<u64, (Cost, Back)> = HashMap::new();
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
                // Group the right table by which vertices it uses, so only
                // states with a matching `S` are paired.
                let mut by_used: HashMap<u32, Vec<(u64, Cost)>> = HashMap::new();
                for (&code, &(cost, _)) in &tables[right] {
                    by_used.entry(used_mask(code, b)).or_default().push((code, cost));
                }
                for (&lc, &(lcost, _)) in &tables[left] {
                    let Some(bucket) = by_used.get(&used_mask(lc, b)) else { continue };
                    let dl = decode(lc, b);
                    let pl = blocks(&dl, b);
                    let size = (0..b).filter(|&j| dl[j] != OUT).count();
                    for &(rc, rcost) in bucket {
                        let dr = decode(rc, b);
                        let pr = blocks(&dr, b);
                        let Some(mut d) = union_partitions(&dl, &dr, b) else { continue };
                        let pj = blocks(&d, b);
                        // Acyclicity, exactly as derived in the module comment.
                        if pl + pr != size + pj {
                            continue;
                        }
                        let code = encode_canonical(&mut d, b);
                        relax(&mut table, code, lcost + rcost, Back::Join(lc, rc));
                    }
                }
            }
        }
        if table.is_empty() {
            return None;
        }
        // Rank-based reduction, applied per `S`-class: within a class the
        // partitions are comparable and the theorem in `rankreduce` says a
        // spanning subset of their cut vectors preserves the least completion
        // cost for every way the rest of the tree might close.
        let table = reduce_table(table, b);
        total_states += table.len();
        if total_states > state_cap {
            return None;
        }
        // Checked every node rather than every sixty-fourth: a single join at a
        // wide bag can take longer than the whole rest of the run.
        if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            return None;
        }
        tables[i] = table;
    }

    // The final bag is `{r}` and the answer is the state in which `r` is used.
    debug_assert_eq!(node_bags[final_node].as_slice(), &[root_terminal]);
    let mut d = [OUT; MAX_BAG];
    d[0] = 0;
    let goal = encode_canonical(&mut d, 1);
    let &(cost, _) = tables[final_node].get(&goal)?;

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
    Some((cost, used))
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

/// Number of blocks in a decoded signature.
#[inline]
fn blocks(d: &[u8; MAX_BAG], b: usize) -> usize {
    let mut seen = 0u16;
    for j in 0..b {
        if d[j] != OUT {
            seen |= 1 << d[j];
        }
    }
    seen.count_ones() as usize
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
        steiner_tree_over_decomposition(g, terminals, &td, 4_000_000, None)
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
}
