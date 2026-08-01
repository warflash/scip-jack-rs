//! A certified lower bound from the hypergraphic (full-component) relaxation.
//!
//! # The relaxation
//!
//! A Steiner tree decomposes uniquely into **full components**: the maximal
//! subtrees whose terminals are all leaves. Write `R_K` for the terminal set of a
//! full component `K` and `c_K` for its cost. For a partition `P` of the terminal
//! set `R` put
//!
//! ```text
//! r(P)   = |P| - 1,
//! r_K(P) = (number of parts of P that R_K meets) - 1.
//! ```
//!
//! The hypergraphic relaxation and its dual are
//!
//! ```text
//! min  sum_K c_K x_K                    max  sum_P r(P) lambda_P
//! s.t. sum_K r_K(P) x_K >= r(P)  for P   s.t. sum_P r_K(P) lambda_P <= c_K  for K
//!      x >= 0                                lambda >= 0.
//! ```
//!
//! > **Every feasible dual is a lower bound on the Steiner optimum.**
//!
//! *Proof.* Let `T` be an optimal Steiner tree and `K_1, ..., K_m` its full
//! components. Fix a partition `P` with `p` parts and expose the components in an
//! order that keeps the exposed part-groups connected. A component meeting `q_i`
//! parts merges at most `q_i` groups into one, so it lowers the number of groups
//! by at most `q_i - 1 = r_{K_i}(P)`. `T` connects every terminal, so the `p`
//! groups end as one and `sum_i r_{K_i}(P) >= p - 1 = r(P)`. Hence `x = 1` on
//! `T`'s components is primal feasible, so the primal optimum is at most `c(T)`;
//! weak duality gives `sum_P r(P) lambda_P <= c(T)` for every feasible `lambda`. ∎
//!
//! # Where a certificate can go wrong, and where it cannot
//!
//! Restricting the **dual variables** to a chosen family of partitions is always
//! safe: setting `lambda_P = 0` on the omitted partitions leaves a feasible point
//! of the full dual, so the value is still a lower bound. Restricting the
//! **constraints** — pricing only some full components — is not, and that is the
//! standing failure mode of restricted hypergraphic masters: the resulting
//! `lambda` can violate an omitted component and its objective can exceed the
//! optimum outright.
//!
//! This module therefore never omits a constraint. It enumerates **every**
//! terminal subset `S` with `|S| >= 2` and charges it with `smt(S)`, the cost of a
//! Steiner minimum tree on `S`, which is a *lower* bound on the cost of any full
//! component whose terminal set is `S` — a full component on `S` is in particular
//! a tree containing `S`. Using the smaller value makes the constraint harder, so
//! the feasible region shrinks and the certificate stays valid. There is no
//! pricing step because there is nothing left to price.
//!
//! Every `smt(S)` comes out of a single Dreyfus-Wagner table, which is exactly
//! what makes the enumeration affordable at all: the `l(v, S)` recursion computes
//! all `2^{|R|}` of them at once. That is also what bounds this module's reach,
//! and the bound is a computed work estimate rather than a terminal count — see
//! [`hyp_is_affordable`].
//!
//! # The partition family
//!
//! The dual has one variable per partition of `R`, and there are `Bell(|R|)` of
//! those: 4,140 at eight terminals, 21,147 at nine, 27 million at thirteen.
//! Two families are used, and both are subsets of the full one, so both are safe:
//!
//! - **every partition**, when `Bell(|R|)` fits;
//! - otherwise the **bipartitions** `{A, R \ A}` together with the all-singletons
//!   partition. A bipartition has `r(P) = 1` and `r_S(P) = 1` exactly when `S`
//!   meets both sides, so its dual variable prices a terminal cut; the singleton
//!   partition has `r(P) = |R| - 1` and `r_S(P) = |S| - 1`, and it is the one
//!   partition whose rank grows with the component.
//!
//! # Why the value is recomputed rather than read off the solver
//!
//! The LP is solved in floating point, and a dual that is feasible to within the
//! solver's tolerance is not feasible. [`HypCertificate`] therefore re-checks
//! every constraint against the returned `lambda` and, if any is violated, scales
//! the whole vector by the worst ratio before reporting anything. Scaling is
//! sound because the constraint system is homogeneous on the left and the
//! right-hand sides are nonnegative: for `0 <= theta <= 1`,
//! `sum_P r_S(P) (theta lambda_P) = theta sum_P r_S(P) lambda_P <= theta smt(S)
//! <= smt(S)`. The reported bound is then computed from the scaled vector, not
//! from the solver's objective.
//!
//! # What this is not
//!
//! It is not a state potential. The natural candidate
//! `H_lambda(S) = sum_P lambda_P r_S(P)` does bound the cost of every tree
//! spanning `S` — the proof above applies verbatim to the minimal subtree of `S` —
//! and it is subadditive under the merge step. It is **not** a valid lower bound
//! in the Dijkstra-Steiner sense, and the witness is small: three terminals
//! `{r, a, b}` on a unit triangle, the all-singletons partition priced at one.
//! Then `H(R) = 2` and `H({r,a}) = 1`, while the validity condition with
//! `I = R`, `I' = {r,a}` and `v = w = b` demands `2 <= 1 + smt({b}) = 1`. So
//! [`crate::graph::algorithms::SteinerSearch`] is not offered this potential, and
//! the pointwise maximum with the cut packing is not taken: a bound that fails
//! consistency corrupts the settling order rather than merely being weak.

use std::time::Instant;

use highs::{HighsModelStatus, RowProblem, Sense};

use crate::graph::{Cost, NodeId, UndirectedGraph};

/// Terminals this module will address. `2^k` constraints and one Dreyfus-Wagner
/// table are both indexed by it.
pub const HYP_MAX_TERMINALS: usize = 20;

/// Work the subset table may cost, in the same units as the solver's
/// Dreyfus-Wagner budget: `3^k n` for the merge step plus `2^k m` for the scans.
const HYP_WORK_BUDGET: f64 = 2e8;

/// Work the subset table may cost before the module declines outright, in the
/// units of [`hyp_work`]. The caller's clock decides the rest.
pub const HYP_WORK_CEILING: f64 = HYP_WORK_BUDGET;

/// Partitions the dual may carry. Beyond this the bipartition family is used
/// instead of the full one.
const HYP_MAX_PARTITIONS: usize = 8192;

/// Work units the subset table will cost: `3^k n` for the subset merges plus
/// `2^k (m + n log n)` for the Dijkstra layer. Infinite when out of range.
///
/// This is a computed estimate, not a terminal count: thirteen terminals on two
/// hundred vertices is 320 million operations and thirteen on twenty thousand is
/// fifty times that.
pub fn hyp_work(num_terminals: usize, num_nodes: u32, num_edges: usize) -> f64 {
    if !(2..=HYP_MAX_TERMINALS).contains(&num_terminals) {
        return f64::INFINITY;
    }
    let k = num_terminals as i32;
    let n = num_nodes as f64;
    3f64.powi(k) * n + 2f64.powi(k) * (num_edges as f64 + n * n.max(2.0).log2())
}

/// Work units this machine gets through in a second, measured rather than
/// guessed: the table for PACE instance024 — nine terminals, 640 vertices,
/// 204,454 edges, so 120 million units — builds and its LP solves in 0.17 s,
/// which is seven hundred million a second. Half of that is used here, so the
/// estimate a caller compares against its clock has a factor of two in hand.
///
/// The point of having it at all is that an *attempt* that runs out of clock
/// costs the budget it consumed and returns nothing. On instance025 at a
/// three-second limit that was the difference between proving the instance and
/// not, so the decision has to be made before the work starts.
pub const HYP_UNITS_PER_SECOND: f64 = 3.5e8;

/// Whether the subset table is affordable for this instance.
pub fn hyp_is_affordable(num_terminals: usize, num_nodes: u32, num_edges: usize) -> bool {
    hyp_work(num_terminals, num_nodes, num_edges) <= HYP_WORK_BUDGET
}

pub struct HypCertificate {
    /// `sum_P r(P) lambda_P`, computed from the verified multipliers.
    pub lower_bound: Cost,
    /// The dual multipliers, one per partition of `partitions`, after any
    /// feasibility rescaling.
    pub lambda: Vec<Cost>,
    /// Each partition as a part index per terminal, in `terminals` order.
    pub partitions: Vec<Vec<u32>>,
    /// Worst constraint violation before rescaling, as a ratio.
    pub repair_ratio: f64,
    /// `smt(S)` for every terminal subset, indexed by bitmask over `terminals`.
    pub subset_cost: Vec<Cost>,
}

impl HypCertificate {
    /// Re-derive dual feasibility from scratch. The certificate is worthless
    /// unless this holds, and it is checked before the bound is reported.
    pub fn verify(&self, tolerance: Cost) -> bool {
        let k = self.partitions.first().map_or(0, |p| p.len());
        if k == 0 {
            return self.lower_bound <= tolerance;
        }
        for mask in 1u32..(1u32 << k) {
            if mask.count_ones() < 2 {
                continue;
            }
            let mut charge = 0.0;
            for (p, part) in self.partitions.iter().enumerate() {
                if self.lambda[p] <= 0.0 {
                    continue;
                }
                charge += self.lambda[p] * rank(part, mask) as Cost;
            }
            if charge > self.subset_cost[mask as usize] + tolerance {
                return false;
            }
        }
        true
    }
}

/// `r_S(P)`: parts of `P` that `S` meets, minus one. Zero for `|S| <= 1`.
fn rank(part: &[u32], mask: u32) -> u32 {
    let mut seen: u64 = 0;
    let mut count = 0u32;
    for (i, &p) in part.iter().enumerate() {
        if mask >> i & 1 == 1 && seen >> p & 1 == 0 {
            seen |= 1u64 << p;
            count += 1;
        }
    }
    count.saturating_sub(1)
}

/// Certify a hypergraphic lower bound at the root.
///
/// Returns `None` when the instance is out of the addressable range, when the
/// terminals are not all in one component, or when the LP does not reach
/// optimality — in each case there is nothing to certify.
pub fn hyp_certificate(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    deadline: Option<Instant>,
) -> Option<HypCertificate> {
    let k = terminals.len();
    if !hyp_is_affordable(k, graph.num_nodes, graph.edges.len()) {
        return None;
    }
    let subset_cost = subset_steiner_costs(graph, terminals)?;
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return None;
    }
    let partitions = partition_family(k);

    // The dual, as a row problem: one column per partition, one row per terminal
    // subset of size at least two.
    let mut problem = RowProblem::default();
    let cols: Vec<_> = partitions
        .iter()
        .map(|part| {
            let parts = part.iter().copied().max().map_or(0, |m| m + 1);
            problem.add_column(parts.saturating_sub(1) as f64, 0.0..f64::INFINITY)
        })
        .collect();
    for mask in 1u32..(1u32 << k) {
        if mask.count_ones() < 2 {
            continue;
        }
        let mut row: Vec<(_, f64)> = Vec::new();
        for (p, part) in partitions.iter().enumerate() {
            let r = rank(part, mask);
            if r > 0 {
                row.push((cols[p], r as f64));
            }
        }
        if row.is_empty() {
            continue;
        }
        problem.add_row(f64::NEG_INFINITY..subset_cost[mask as usize], &row);
    }

    let mut model = problem.optimise(Sense::Maximise);
    model.set_option("output_flag", false);
    if let Some(d) = deadline {
        let budget = d.saturating_duration_since(Instant::now()).as_secs_f64();
        if budget <= 0.0 {
            return None;
        }
        model.set_option("time_limit", budget);
    }
    let solved = model.solve();
    if solved.status() != HighsModelStatus::Optimal {
        return None;
    }
    let mut lambda: Vec<Cost> = solved.get_solution().columns().to_vec();
    lambda.truncate(partitions.len());
    lambda.resize(partitions.len(), 0.0);
    for l in lambda.iter_mut() {
        if *l < 0.0 {
            *l = 0.0;
        }
    }

    // Feasibility repair. See the module comment for why scaling is sound.
    let mut worst = 1.0f64;
    for mask in 1u32..(1u32 << k) {
        if mask.count_ones() < 2 {
            continue;
        }
        let cap = subset_cost[mask as usize];
        let mut charge = 0.0;
        for (p, part) in partitions.iter().enumerate() {
            if lambda[p] > 0.0 {
                charge += lambda[p] * rank(part, mask) as Cost;
            }
        }
        if charge > cap {
            if cap <= 0.0 {
                worst = f64::INFINITY;
            } else {
                worst = worst.max(charge / cap);
            }
        }
    }
    let repair_ratio = worst;
    if worst.is_finite() && worst > 1.0 {
        let theta = 1.0 / worst;
        for l in lambda.iter_mut() {
            *l *= theta;
        }
    } else if !worst.is_finite() {
        lambda.iter_mut().for_each(|l| *l = 0.0);
    }

    let lower_bound: Cost = partitions
        .iter()
        .zip(lambda.iter())
        .map(|(part, &l)| {
            let parts = part.iter().copied().max().map_or(0, |m| m + 1);
            l * parts.saturating_sub(1) as Cost
        })
        .sum();

    let cert = HypCertificate { lower_bound, lambda, partitions, repair_ratio, subset_cost };
    cert.verify(1e-6).then_some(cert)
}

/// The partition family, as a part index per terminal.
///
/// Every family here is a subset of the set of all partitions, which is what
/// makes the restriction safe; see the module comment.
fn partition_family(k: usize) -> Vec<Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    if bell(k) <= HYP_MAX_PARTITIONS {
        // Restricted growth strings: `a[0] = 0` and `a[i] <= 1 + max(a[0..i])`.
        // Each one names a partition, and each partition has exactly one, so this
        // enumerates the family without duplicates.
        fn grow(i: usize, used: u32, a: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
            if i == a.len() {
                out.push(a.clone());
                return;
            }
            for p in 0..=used {
                a[i] = p;
                grow(i + 1, used.max(p + 1), a, out);
            }
        }
        let mut a = vec![0u32; k];
        grow(1, 1, &mut a, &mut out);
        return out;
    }
    // Bipartitions `{A, R \ A}` with terminal 0 in `A`, so each is generated once,
    // plus the all-singletons partition.
    for a in 1u32..(1u32 << (k - 1)) {
        let mut part = vec![0u32; k];
        for (i, p) in part.iter_mut().enumerate().skip(1) {
            if a >> (i - 1) & 1 == 1 {
                *p = 1;
            }
        }
        out.push(part);
        if out.len() >= HYP_MAX_PARTITIONS {
            break;
        }
    }
    out.push((0..k as u32).collect());
    out
}

fn bell(k: usize) -> usize {
    // Bell numbers by the triangle, saturating so the caller's comparison is
    // still meaningful for large `k`.
    let mut row = vec![1usize];
    for _ in 1..k.max(1) {
        let mut next = vec![*row.last().unwrap()];
        for &x in &row {
            let last = *next.last().unwrap();
            next.push(last.saturating_add(x));
        }
        row = next;
    }
    *row.last().unwrap_or(&1)
}

/// `smt(S)` for every subset `S` of the terminals, by the Dreyfus-Wagner
/// recursion.
///
/// `l[S][v]` is the cheapest tree containing `S` and `v`; the recursion is the
/// standard one, and `smt(S) = min over v in S of l[S \ {v}][v]`. Returning the
/// whole table is the point: the hypergraphic dual needs a charge for every
/// terminal subset, and one run supplies all of them.
fn subset_steiner_costs(graph: &UndirectedGraph, terminals: &[NodeId]) -> Option<Vec<Cost>> {
    let k = terminals.len();
    let n = graph.num_nodes as usize + 1;
    let num_masks = 1usize << k;

    // Adjacency, once.
    let mut start = vec![0u32; n + 1];
    for e in &graph.edges {
        start[e.src as usize + 1] += 1;
        start[e.dst as usize + 1] += 1;
    }
    for i in 0..n {
        start[i + 1] += start[i];
    }
    let mut fill = start.clone();
    let mut head = vec![0u32; graph.edges.len() * 2];
    let mut cost = vec![0.0 as Cost; graph.edges.len() * 2];
    for e in &graph.edges {
        let i = fill[e.src as usize] as usize;
        head[i] = e.dst;
        cost[i] = e.cost;
        fill[e.src as usize] += 1;
        let j = fill[e.dst as usize] as usize;
        head[j] = e.src;
        cost[j] = e.cost;
        fill[e.dst as usize] += 1;
    }

    let mut l = vec![Cost::INFINITY; num_masks * n];
    for (i, &t) in terminals.iter().enumerate() {
        l[(1usize << i) * n + t as usize] = 0.0;
    }

    let mut heap: std::collections::BinaryHeap<(std::cmp::Reverse<Ordered>, u32)> =
        std::collections::BinaryHeap::new();
    for mask in 1..num_masks {
        // Merge two disjoint proper submasks.
        let base = mask * n;
        let mut sub = (mask - 1) & mask;
        while sub > 0 {
            let other = mask ^ sub;
            if sub < other {
                let (a, b) = (sub * n, other * n);
                for v in 0..n {
                    let s = l[a + v] + l[b + v];
                    if s < l[base + v] {
                        l[base + v] = s;
                    }
                }
            }
            sub = (sub - 1) & mask;
        }
        // Grow along edges: a Dijkstra over the vertex layer.
        heap.clear();
        for v in 0..n {
            if l[base + v].is_finite() {
                heap.push((std::cmp::Reverse(Ordered(l[base + v])), v as u32));
            }
        }
        while let Some((std::cmp::Reverse(Ordered(d)), v)) = heap.pop() {
            if d > l[base + v as usize] + 1e-12 {
                continue;
            }
            let (s, e) = (start[v as usize] as usize, start[v as usize + 1] as usize);
            for i in s..e {
                let u = head[i] as usize;
                let nd = d + cost[i];
                if nd < l[base + u] - 1e-12 {
                    l[base + u] = nd;
                    heap.push((std::cmp::Reverse(Ordered(nd)), u as u32));
                }
            }
        }
    }

    let mut smt = vec![0.0 as Cost; num_masks];
    for mask in 1..num_masks {
        if mask.count_ones() < 2 {
            continue;
        }
        let mut best = Cost::INFINITY;
        for i in 0..k {
            if mask >> i & 1 == 1 {
                let rest = mask ^ (1 << i);
                best = best.min(l[rest * n + terminals[i] as usize]);
            }
        }
        if !best.is_finite() {
            return None; // terminals split across components
        }
        smt[mask] = best;
    }
    Some(smt)
}

#[derive(PartialEq, PartialOrd)]
struct Ordered(Cost);
impl Eq for Ordered {}
#[allow(clippy::derive_ord_xor_partial_ord)]
impl Ord for Ordered {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::dreyfus_wagner;
    use crate::graph::NodeType;

    fn random_graph(seed: &mut u64) -> Option<(UndirectedGraph, Vec<NodeId>)> {
        let mut rng = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        let n = 5 + (rng() % 5) as u32;
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
        for u in 1..=n {
            for v in (u + 1)..=n {
                if rng() % 3 != 0 {
                    g.add_edge(u, v, 1.0 + (rng() % 9) as Cost);
                }
            }
        }
        Some((g, terminals))
    }

    /// The subset table must agree with the reference Dreyfus-Wagner on every
    /// subset, not only on the full terminal set.
    #[test]
    fn the_subset_table_is_the_steiner_optimum_of_every_subset() {
        let mut seed = 0x4A17_0F5E_2026_0801u64;
        let mut ran = 0;
        for _ in 0..200 {
            let Some((g, terminals)) = random_graph(&mut seed) else { continue };
            let Some(table) = subset_steiner_costs(&g, &terminals) else { continue };
            ran += 1;
            let k = terminals.len();
            for mask in 1u32..(1u32 << k) {
                if mask.count_ones() < 2 {
                    continue;
                }
                let sub: Vec<NodeId> =
                    (0..k).filter(|&i| mask >> i & 1 == 1).map(|i| terminals[i]).collect();
                let want = dreyfus_wagner(&g, &sub).expect("connected").optimal_cost;
                assert!(
                    (table[mask as usize] - want).abs() < 1e-9,
                    "subset {mask:b}: table {} against {want}",
                    table[mask as usize]
                );
            }
        }
        assert!(ran > 100, "only {ran} graphs were checked");
    }

    /// The certificate must never exceed the optimum, and its dual must survive
    /// an independent feasibility check.
    #[test]
    fn the_bound_never_exceeds_the_optimum() {
        let mut seed = 0x9C3E_1B7D_2026_0801u64;
        let mut ran = 0;
        let mut nontrivial = 0;
        for _ in 0..300 {
            let Some((g, terminals)) = random_graph(&mut seed) else { continue };
            let Some(opt) = dreyfus_wagner(&g, &terminals) else { continue };
            let Some(cert) = hyp_certificate(&g, &terminals, None) else { continue };
            ran += 1;
            assert!(cert.verify(1e-6), "the reported dual is infeasible");
            assert!(
                cert.lower_bound <= opt.optimal_cost + 1e-6,
                "bound {} exceeds the optimum {}",
                cert.lower_bound,
                opt.optimal_cost
            );
            if cert.lower_bound > 1e-9 {
                nontrivial += 1;
            }
        }
        assert!(ran > 100, "only {ran} certificates were produced");
        assert!(nontrivial > 50, "only {nontrivial} of them were nonzero");
    }

    /// Enumerating restricted growth strings must produce every partition of the
    /// terminal set exactly once.
    #[test]
    fn the_partition_family_is_complete_when_it_claims_to_be() {
        for k in 2..=7usize {
            let fam = partition_family(k);
            assert_eq!(fam.len(), bell(k), "k = {k}");
            // Canonical form: the parts as a sorted set of sorted member lists.
            let mut seen: std::collections::HashSet<Vec<Vec<usize>>> = Default::default();
            for part in &fam {
                let mut groups: std::collections::BTreeMap<u32, Vec<usize>> = Default::default();
                for (i, &p) in part.iter().enumerate() {
                    groups.entry(p).or_default().push(i);
                }
                let canon: Vec<Vec<usize>> = groups.into_values().collect();
                assert!(seen.insert(canon), "duplicate partition at k = {k}");
            }
        }
    }

    /// On a star of unit edges the relaxation is exact, which is the smallest
    /// case where the singleton partition earns its keep: `r(P) = k - 1` and the
    /// only binding constraint is the full set.
    #[test]
    fn a_unit_star_is_certified_exactly() {
        let mut g = UndirectedGraph::new(4);
        for v in 1..=3u32 {
            g.add_node(v, NodeType::Terminal, 0.0);
        }
        g.add_node(4, NodeType::Steiner, 0.0);
        for v in 1..=3u32 {
            g.add_edge(v, 4, 1.0);
        }
        let cert = hyp_certificate(&g, &[1, 2, 3], None).expect("certificate");
        assert!(cert.verify(1e-9));
        assert!(
            (cert.lower_bound - 3.0).abs() < 1e-6,
            "bound {} against an optimum of 3",
            cert.lower_bound
        );
    }
}
