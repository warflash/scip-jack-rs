//! Certified pricing for the hypergraphic dual, past the `2^{|R|}` ceiling.
//!
//! # The obligation this discharges
//!
//! [`crate::model::hypergraphic`] is valid because it omits *no* constraint: it
//! enumerates every terminal subset `S` and charges it with `smt(S)` out of one
//! Dreyfus-Wagner table. That is what caps its reach near a dozen terminals.
//! Going past that means solving a **restricted master** — a dual over a chosen
//! subset of the constraints — and a restricted dual can violate an omitted
//! constraint, so its objective is not a bound on anything until something
//! proves otherwise. A restricted master is a discovery tool. This module is the
//! proof.
//!
//! The dual is
//!
//! ```text
//! max sum_P r(P) lambda_P   s.t.  sum_P r_S(P) lambda_P <= smt(S)   for all S,
//! ```
//!
//! so pricing means minimising the reduced cost
//!
//! ```text
//! f(S) = smt(S) - sum_P r_S(P) lambda_P
//! ```
//!
//! over all `S subset R` with `|S| >= 2`, and certifying `min f >= 0`.
//!
//! # Signatures collapse the search
//!
//! Let the **active** partitions be those with `lambda_P > 0`, say
//! `P^(1), ..., P^(t)`. Give each terminal `u` the tuple
//!
//! ```text
//! sig(u) = ( part of u in P^(1), ..., part of u in P^(t) ),
//! ```
//!
//! and let `h` be the number of distinct tuples. Terminals sharing a signature
//! are interchangeable as far as the reward is concerned:
//!
//! > **Lemma 1 (the reward sees only signatures).** `sum_P r_S(P) lambda_P`
//! > depends on `S` only through `sig(S) = { sig(u) : u in S }`.
//!
//! *Proof.* `r_S(P) = |{parts of P meeting S}| - 1`, and which part of `P^(i)`
//! a terminal lies in is by definition the `i`-th coordinate of its signature.
//! So the set of parts of `P^(i)` met by `S` is determined by `sig(S)`. Inactive
//! partitions carry `lambda_P = 0` and contribute nothing. QED
//!
//! Write `G(Q)` for that common value when `sig(S) = Q`.
//!
//! > **Lemma 2 (one representative per class suffices).** For a nonempty
//! > `Q subset [h]`,
//! > ```text
//! > min { smt(S) : sig(S) = Q } = min { smt(S) : |S| = |Q|, one terminal per class of Q },
//! > ```
//! > and the right-hand side is the **group Steiner tree** value: choose one
//! > terminal from each signature class in `Q` and connect them as cheaply as
//! > possible.
//!
//! *Proof.* Take `S` attaining the left-hand side. If two of its terminals
//! `u != u'` share a class, drop `u'`: the signature set is unchanged, because
//! `u` still contributes that class, and `smt` is monotone under removing a
//! terminal, so the value does not increase. Repeating leaves exactly one
//! terminal per class of `Q`, and no class outside `Q` is represented. QED
//!
//! > **Theorem (exact pricing in `3^h`).** With `m(Q)` the group Steiner value
//! > of Lemma 2,
//! > ```text
//! > min { f(S) : |S| >= 2 } = min { m(Q) - G(Q) : Q subset [h], |Q| >= 2 },
//! > ```
//! > and the right-hand side is computed by one Dreyfus-Wagner recursion over
//! > the `h` groups, in `O(3^h n + 2^h (m + n log n))`.
//!
//! *Proof.* Partition the `S` by `Q = sig(S)`. For `|Q| = 1` every terminal of
//! `S` lies in one part of every active partition, so `r_S(P) = 0` for all of
//! them, `G(Q) = 0`, and `f(S) = smt(S) >= 0`: those `S` can never violate.
//! For `|Q| >= 2`, every `S` with `sig(S) = Q` has `|S| >= 2` automatically, and
//! Lemma 1 makes the reward constant on the class while Lemma 2 identifies the
//! cheapest member. The group Steiner value is what
//! [`group_steiner_costs`] computes: it is the ordinary Dreyfus-Wagner
//! recursion with each singleton base case replaced by a multi-source distance
//! from a whole group. QED
//!
//! The exponent is `h`, not `|R|`. That was the hope — an active dual supported
//! on a few coarse partitions has few signatures however many terminals there
//! are — and it does not survive contact with the relaxation. **A one-line
//! proposition kills it**, and it is stated and gated on
//! [`GroupedHypDual`]: any dual with `h < |R|` is capped at the cost of
//! connecting `h` representatives, which for `h = 10` and `|R| = 134` is a
//! twelfth of the optimum. Read that before building anything on this file.
//!
//! What is here regardless is the machinery, which is correct and reusable:
//! [`group_steiner_costs`] is an exact group Steiner oracle, and
//! [`price_and_repair`] discharges — against *every* terminal subset, in `3^h`
//! — the proof obligation that a restricted master cannot discharge for itself.
//!
//! # What is reported
//!
//! Never the solver's objective. The pricing minimum is computed from the
//! returned multipliers, and if it is negative the whole vector is scaled by
//!
//! ```text
//! theta = min over Q with G(Q) > 0 of m(Q) / G(Q),   capped at 1,
//! ```
//!
//! which is feasible for the same homogeneity reason the enumerating module
//! uses: the constraint system is homogeneous on the left with nonnegative
//! right-hand sides, so `theta lambda` satisfies
//! `sum_P r_S(P) theta lambda_P = theta G(sig(S)) <= m(sig(S)) <= smt(S)` for
//! every `S`. The reported bound is `sum_P r(P) theta lambda_P`.
//!
//! Because the repair is applied against the *exact* pricing minimum over all
//! `S`, the reported value is a valid lower bound on the Steiner optimum
//! whatever the restricted master did — which is precisely the certificate a
//! restricted master cannot supply on its own.

use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;
use std::time::Instant;

use highs::{HighsModelStatus, RowProblem, Sense};

use crate::graph::{cmp_cost, Cost, NodeId, UndirectedGraph};

/// Signature classes the pricing oracle will address. The table is `2^h n`
/// wide and the merge step `3^h n`.
pub const MAX_SIGNATURES: usize = 18;

/// A hypergraphic dual whose global feasibility has been priced, not assumed.
#[derive(Debug, Clone)]
pub struct PricedDual {
    /// `sum_P r(P) lambda_P` after repair. A valid lower bound on the optimum.
    pub lower_bound: Cost,
    /// The multipliers actually certified, in the caller's partition order.
    pub lambda: Vec<Cost>,
    /// Distinct terminal signatures the active partitions induced.
    pub signatures: usize,
    /// `min_Q (m(Q) - G(Q))` before repair; negative means the master's dual was
    /// infeasible for an omitted constraint, which is the expected case.
    pub min_reduced_cost: Cost,
    /// The scaling applied. `1.0` means the master's dual was already globally
    /// feasible.
    pub theta: Cost,
}

/// Price a hypergraphic dual exactly and repair it into a valid bound.
///
/// `partitions[p][i]` is the part index of `terminals[i]` under partition `p`,
/// and `lambda[p]` its multiplier. Returns `None` when the signature count is
/// out of range, the graph does not connect the terminals, or the deadline
/// passes — in every case leaving the caller with nothing rather than with an
/// unproved number.
pub fn price_and_repair(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    partitions: &[Vec<u32>],
    lambda: &[Cost],
    deadline: Option<Instant>,
) -> Option<PricedDual> {
    if terminals.len() < 2 || partitions.len() != lambda.len() {
        return None;
    }
    // Only the active partitions define signatures; the rest contribute nothing
    // to any reward and are held at zero.
    let active: Vec<usize> = (0..partitions.len()).filter(|&p| lambda[p] > 1e-12).collect();
    let mut lambda = lambda.to_vec();
    for (p, l) in lambda.iter_mut().enumerate() {
        if !active.contains(&p) {
            *l = 0.0;
        }
    }
    if active.is_empty() {
        return Some(PricedDual {
            lower_bound: 0.0,
            lambda,
            signatures: 0,
            min_reduced_cost: 0.0,
            theta: 1.0,
        });
    }

    // Signatures, and the classes they induce.
    let mut class_of: Vec<usize> = Vec::with_capacity(terminals.len());
    let mut index: HashMap<Vec<u32>, usize> = HashMap::new();
    for i in 0..terminals.len() {
        let sig: Vec<u32> = active.iter().map(|&p| partitions[p][i]).collect();
        let next = index.len();
        let c = *index.entry(sig).or_insert(next);
        class_of.push(c);
    }
    let h = index.len();
    if h < 2 || h > MAX_SIGNATURES {
        return None;
    }
    let mut groups: Vec<Vec<NodeId>> = vec![Vec::new(); h];
    for (i, &t) in terminals.iter().enumerate() {
        groups[class_of[i]].push(t);
    }

    // `m(Q)`, from the group Steiner recursion.
    let m = group_steiner_costs(graph, &groups, deadline)?;

    // `G(Q)`, accumulated one active partition at a time. For a fixed partition
    // the parts met by `Q` are the union of the parts met by its classes, so a
    // single subset sweep computes them all: strip the lowest class, take the
    // union with that class's part, count the bits.
    let full = 1usize << h;
    let mut reward = vec![0.0 as Cost; full];
    let mut met = vec![0u64; full];
    for &p in &active {
        // Part of each class under this partition. Classes are well defined
        // here: every terminal of a class shares its part in every active
        // partition, by construction of the signature.
        let mut part_of_class = vec![u32::MAX; h];
        for i in 0..terminals.len() {
            part_of_class[class_of[i]] = partitions[p][i];
        }
        if part_of_class.iter().any(|&x| x >= 64) {
            // More than 64 parts: the bitmask cannot represent it, so this
            // partition is not priced and the certificate is abandoned rather
            // than approximated.
            return None;
        }
        met[0] = 0;
        for q in 1..full {
            let low = q.trailing_zeros() as usize;
            met[q] = met[q & (q - 1)] | (1u64 << part_of_class[low]);
        }
        for q in 1..full {
            reward[q] += lambda[p] * (met[q].count_ones() as Cost - 1.0);
        }
    }

    // The pricing minimum, over every signature set of size at least two.
    let mut min_reduced = Cost::INFINITY;
    let mut theta = 1.0 as Cost;
    for q in 1..full {
        if (q as u32).count_ones() < 2 {
            continue;
        }
        let cap = m[q];
        if !cap.is_finite() {
            // No tree connects one terminal from each of these classes, so no
            // full component has this signature and the constraint is vacuous.
            continue;
        }
        let g = reward[q];
        min_reduced = min_reduced.min(cap - g);
        if g > 0.0 && cap < g {
            theta = theta.min(cap / g);
        }
    }
    if !min_reduced.is_finite() {
        min_reduced = 0.0;
    }
    if theta < 1.0 {
        for l in lambda.iter_mut() {
            *l *= theta;
        }
    }

    // `r(P) = |P| - 1` counts the parts that are actually *occupied*. Taking
    // one more than the largest index instead assumes the labels are
    // contiguous, and a partition whose labels skip a value is then charged a
    // rank it does not have — which inflates the objective directly and is a
    // way to report a "bound" above the optimum.
    let lower_bound: Cost = partitions
        .iter()
        .zip(lambda.iter())
        .map(|(part, &l)| {
            let mut seen: Vec<u32> = part.clone();
            seen.sort_unstable();
            seen.dedup();
            l * seen.len().saturating_sub(1) as Cost
        })
        .sum();

    Some(PricedDual { lower_bound, lambda, signatures: h, min_reduced_cost: min_reduced, theta })
}

/// A hypergraphic dual over a *clustering* of the terminals.
///
/// # Why this needs no pricing loop
///
/// The theorem above says the reward `sum_P r_S(P) lambda_P` sees a terminal
/// set only through its signature, and that the cheapest set with a given
/// signature is the group Steiner value. Turn that around: **fix** the classes
/// first, insist that every partition be a union of classes, and the two facts
/// become a construction rather than a certificate.
///
/// > **Theorem (complete by construction).** Let `R = C_1 + ... + C_h` be any
/// > partition of the terminals into classes, let the dual range over
/// > partitions of `{C_1, ..., C_h}`, and charge each nonempty
/// > `Q subset [h]` with `m(Q)`, the group Steiner value. Then every feasible
/// > `lambda` for those `2^h` constraints is feasible for the *full*
/// > hypergraphic dual, and its objective is a lower bound on the Steiner
/// > optimum.
///
/// *Proof.* Take any `S subset R` with `|S| >= 2` and let `Q = sig(S)` be the
/// classes it meets. Every partition in the family is a union of classes, so
/// each terminal's part is determined by its class and `r_S(P) = r_Q(P)` for
/// every `P` — this is Lemma 1 with the classes fixed in advance rather than
/// read off an active set. Lemma 2 gives `m(Q) <= smt(S)`, since `S` meets
/// every class of `Q` and `m(Q)` minimises over exactly such sets. Hence
/// `sum_P r_S(P) lambda_P = sum_P r_Q(P) lambda_P <= m(Q) <= smt(S)`, which is
/// the omitted constraint. Restricting the dual *variables* to partitions of
/// the classes is safe for the usual reason — the omitted ones are zero — and
/// [`crate::model::hypergraphic`]'s weak-duality argument finishes it. QED
///
/// So no constraint is omitted and there is nothing left to price: the table is
/// `2^h` rather than `2^{|R|}`, and `h` is chosen by what is affordable rather
/// than dictated by the instance. Singleton classes recover the enumerating
/// module exactly.
///
/// The clustering is free to be anything — every clustering gives a valid
/// bound, only the strength changes — so it is chosen by farthest-first
/// traversal in the terminal metric, which spreads the centres and keeps
/// terminals that behave alike together.
///
/// # Why this cannot work, and it is a theorem rather than a measurement
///
/// > **Proposition (the coarsening ceiling).** The grouped dual's objective is
/// > at most `m([h])`, the cost of connecting one representative from each of
/// > the `h` classes.
///
/// *Proof.* Among the constraints is the one at `Q = [h]`. Take the
/// all-singletons partition of the classes, for which `r_{[h]}(P) = |P| - 1`;
/// in fact for **every** partition `P` of the classes, `Q = [h]` meets every
/// part, so `r_{[h]}(P) = |P| - 1` identically. The constraint at `Q = [h]` is
/// therefore `sum_P (|P| - 1) lambda_P <= m([h])`, and its left-hand side *is*
/// the objective. QED
///
/// With singleton classes `h = |R|` and the ceiling is `m([|R|]) = smt(R)`, the
/// optimum itself — which is why the enumerating module is not handicapped. But
/// coarsening moves the ceiling down to the cost of a tree on `h` terminals,
/// and a tree spanning ten representatives costs a small fraction of one
/// spanning a hundred terminals. **Measured on the reduced instances**, against
/// a dual ascent that is free:
///
/// | instance | \|R\| | ascent | grouped `h=8` | `h=10` | optimum |
/// |---|---|---|---|---|---|
/// | 197 | 101 | 4,219 | 1,190 | 1,219 | 4,292 |
/// | 200 | 134 | 6,249 | 456 | 512 | 6,393 |
/// | 161 | 25 | 5,123 | 1,570 | 2,046 | 5,199 |
/// | 172 | 27 | 6,602 | 2,147 | 3,305 | 7,299 |
///
/// which is exactly the ratio the proposition predicts. And the obstruction is
/// not specific to *this* clustering: `h < |R|` forces two terminals to share
/// every part of every priced partition, which is a clustering by definition,
/// so the ceiling applies to any way of making the exponent smaller than the
/// terminal count. The direction is closed, not merely unpromising.
///
/// What survives is the machinery: [`group_steiner_costs`] is an exact oracle
/// in its own right, and [`price_and_repair`] certifies an arbitrary set of
/// multipliers against **every** terminal subset in `3^h` — which is the proof
/// obligation a restricted master cannot discharge for itself, and is what any
/// future column generation on this relaxation would have to call.
#[derive(Debug, Clone)]
pub struct GroupedHypDual {
    pub lower_bound: Cost,
    /// Terminals per class, in class order.
    pub groups: Vec<Vec<NodeId>>,
    pub partitions: Vec<Vec<u32>>,
    pub lambda: Vec<Cost>,
    /// Worst constraint violation before rescaling, as a ratio.
    pub repair_ratio: Cost,
}

/// Cluster the terminals into at most `max_groups` classes by farthest-first
/// traversal in the terminal metric.
///
/// The first centre is `terminals[0]`; each next is the terminal furthest from
/// the centres chosen so far; every terminal then joins its nearest centre.
/// Deterministic, and it costs one Dijkstra per centre.
pub fn farthest_first_groups(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    max_groups: usize,
) -> Vec<Vec<NodeId>> {
    if terminals.len() <= max_groups || max_groups == 0 {
        return terminals.iter().map(|&t| vec![t]).collect();
    }
    let n = graph.num_nodes as usize + 1;
    let mut nearest = vec![Cost::INFINITY; terminals.len()];
    let mut owner = vec![0usize; terminals.len()];
    let mut centres: Vec<NodeId> = vec![terminals[0]];

    for c in 0..max_groups {
        let src = centres[c];
        let mut row = vec![Cost::INFINITY; n];
        let mut heap: BinaryHeap<Entry> = BinaryHeap::new();
        if (src as usize) < n {
            row[src as usize] = 0.0;
            heap.push(Entry { cost: 0.0, node: src });
        }
        relax(graph, &mut row, &mut heap);
        for (i, &t) in terminals.iter().enumerate() {
            let d = row.get(t as usize).copied().unwrap_or(Cost::INFINITY);
            if d < nearest[i] {
                nearest[i] = d;
                owner[i] = c;
            }
        }
        if centres.len() >= max_groups {
            break;
        }
        // The terminal furthest from every centre so far becomes the next one.
        let mut best = 0usize;
        let mut best_d = -1.0 as Cost;
        for (i, &d) in nearest.iter().enumerate() {
            let d = if d.is_finite() { d } else { Cost::MAX };
            if d > best_d && !centres.contains(&terminals[i]) {
                best_d = d;
                best = i;
            }
        }
        if best_d < 0.0 {
            break;
        }
        centres.push(terminals[best]);
    }

    let mut groups: Vec<Vec<NodeId>> = vec![Vec::new(); centres.len()];
    for (i, &t) in terminals.iter().enumerate() {
        groups[owner[i].min(centres.len() - 1)].push(t);
    }
    groups.retain(|g| !g.is_empty());
    groups
}

/// Build and certify the grouped hypergraphic dual.
///
/// `max_groups` bounds the exponent, and the caller is expected to pick it from
/// [`group_steiner_work`] against the time it has. Returns `None` when the
/// oracle is out of range, the LP does not solve, or the deadline passes.
pub fn grouped_hyp_dual(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    max_groups: usize,
    deadline: Option<Instant>,
) -> Option<GroupedHypDual> {
    if terminals.len() < 2 || max_groups < 2 {
        return None;
    }
    let groups = farthest_first_groups(graph, terminals, max_groups.min(MAX_SIGNATURES));
    let h = groups.len();
    if h < 2 || h > MAX_SIGNATURES {
        return None;
    }
    let m = group_steiner_costs(graph, &groups, deadline)?;
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return None;
    }

    // Partitions of the classes. Same family logic as the enumerating module:
    // all of them when the Bell number fits, otherwise the bipartitions plus
    // the all-singletons partition. Both are subsets of the full family, which
    // is what makes the restriction safe.
    let partitions = class_partitions(h);

    let mut problem = RowProblem::default();
    let cols: Vec<_> = partitions
        .iter()
        .map(|part| {
            let mut seen: Vec<u32> = part.clone();
            seen.sort_unstable();
            seen.dedup();
            problem.add_column(seen.len().saturating_sub(1) as f64, 0.0..f64::INFINITY)
        })
        .collect();
    for q in 1usize..(1usize << h) {
        if (q as u32).count_ones() < 2 || !m[q].is_finite() {
            continue;
        }
        let mut row: Vec<(_, f64)> = Vec::new();
        for (p, part) in partitions.iter().enumerate() {
            let r = class_rank(part, q);
            if r > 0 {
                row.push((cols[p], r as f64));
            }
        }
        if !row.is_empty() {
            problem.add_row(f64::NEG_INFINITY..m[q], &row);
        }
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

    // Feasibility repair against the *same* constraints, recomputed. A dual
    // feasible to within the solver's tolerance is not feasible.
    let mut worst = 1.0 as Cost;
    for q in 1usize..(1usize << h) {
        if (q as u32).count_ones() < 2 || !m[q].is_finite() {
            continue;
        }
        let charge: Cost = partitions
            .iter()
            .zip(lambda.iter())
            .map(|(part, &l)| l * class_rank(part, q) as Cost)
            .sum();
        if charge > m[q] {
            if m[q] <= 0.0 {
                worst = Cost::INFINITY;
            } else {
                worst = worst.max(charge / m[q]);
            }
        }
    }
    if !worst.is_finite() {
        lambda.iter_mut().for_each(|l| *l = 0.0);
    } else if worst > 1.0 {
        let theta = 1.0 / worst;
        lambda.iter_mut().for_each(|l| *l *= theta);
    }

    let lower_bound: Cost = partitions
        .iter()
        .zip(lambda.iter())
        .map(|(part, &l)| {
            let mut seen: Vec<u32> = part.clone();
            seen.sort_unstable();
            seen.dedup();
            l * seen.len().saturating_sub(1) as Cost
        })
        .sum();

    Some(GroupedHypDual { lower_bound, groups, partitions, lambda, repair_ratio: worst })
}

/// `r_Q(P)`: parts of `P` met by the classes of `Q`, minus one.
fn class_rank(part: &[u32], q: usize) -> usize {
    let mut seen = 0u64;
    for (c, &p) in part.iter().enumerate() {
        if q & (1 << c) != 0 && p < 64 {
            seen |= 1 << p;
        }
    }
    (seen.count_ones() as usize).saturating_sub(1)
}

/// Partitions of `h` classes, as a part index per class.
fn class_partitions(h: usize) -> Vec<Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    // Bell(h) grows fast; enumerate it whole only while it is small.
    if h <= 8 {
        fn grow(i: usize, used: u32, a: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
            if i == a.len() {
                out.push(a.clone());
                return;
            }
            for v in 0..=used {
                a[i] = v;
                grow(i + 1, used.max(v + 1), a, out);
            }
        }
        let mut a = vec![0u32; h];
        grow(1, 1, &mut a, &mut out);
        return out;
    }
    // Otherwise the bipartitions, plus the all-singletons partition.
    for mask in 1u32..(1u32 << (h - 1)) {
        out.push((0..h).map(|c| u32::from(mask & (1 << c) != 0)).collect());
    }
    out.push((0..h as u32).collect());
    out
}

/// Work the group Steiner oracle will cost, in the same units the solver's
/// other exact dispatches use: `3^h n` for the subset merges plus
/// `2^h (m + n log n)` for the shortest-path layer.
pub fn group_steiner_work(h: usize, num_nodes: u32, num_edges: usize) -> f64 {
    if h > MAX_SIGNATURES {
        return f64::INFINITY;
    }
    let n = num_nodes.max(1) as f64;
    3f64.powi(h as i32) * n + 2f64.powi(h as i32) * (num_edges as f64 + n * n.max(2.0).log2())
}

/// `m(Q)` for every `Q subset [h]`: the least cost of a tree containing at
/// least one vertex from each group in `Q`.
///
/// This is the Dreyfus-Wagner recursion with the singleton base case replaced
/// by a multi-source distance from a whole group. Its correctness is the same
/// induction: a minimal tree meeting the groups of `Q` either branches at some
/// vertex `v`, splitting `Q`, or is a path from `v` to a vertex of a single
/// group, and both cases are enumerated.
pub fn group_steiner_costs(
    graph: &UndirectedGraph,
    groups: &[Vec<NodeId>],
    deadline: Option<Instant>,
) -> Option<Vec<Cost>> {
    let h = groups.len();
    if h == 0 || h > MAX_SIGNATURES {
        return None;
    }
    let n = graph.num_nodes as usize + 1;
    let full = 1usize << h;
    let mut dp = vec![vec![Cost::INFINITY; n]; full];

    // Base: one multi-source Dijkstra per group.
    for (i, group) in groups.iter().enumerate() {
        let mask = 1usize << i;
        let row = &mut dp[mask];
        let mut heap: BinaryHeap<Entry> = BinaryHeap::new();
        for &t in group {
            if (t as usize) < n && row[t as usize] > 0.0 {
                row[t as usize] = 0.0;
                heap.push(Entry { cost: 0.0, node: t });
            }
        }
        relax(graph, row, &mut heap);
    }

    // Subsets in increasing order of value, which is increasing in size.
    for q in 1..full {
        if (q as u32).count_ones() < 2 {
            continue;
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        // Merge: split `Q` into two nonempty halves meeting at `v`.
        let mut sub = (q - 1) & q;
        while sub > 0 {
            let comp = q ^ sub;
            if sub < comp {
                for v in 1..n {
                    let c = dp[sub][v] + dp[comp][v];
                    if c < dp[q][v] {
                        dp[q][v] = c;
                    }
                }
            }
            sub = (sub - 1) & q;
        }
        // Extend along shortest paths.
        let mut heap: BinaryHeap<Entry> = BinaryHeap::new();
        for v in 1..n {
            if dp[q][v].is_finite() {
                heap.push(Entry { cost: dp[q][v], node: v as NodeId });
            }
        }
        let row = &mut dp[q];
        relax(graph, row, &mut heap);
    }

    let mut out = vec![Cost::INFINITY; full];
    for (q, row) in dp.iter().enumerate().skip(1) {
        out[q] = row[1..].iter().copied().fold(Cost::INFINITY, Cost::min);
    }
    Some(out)
}

/// Dijkstra relaxation of an already-seeded distance row.
fn relax(graph: &UndirectedGraph, row: &mut [Cost], heap: &mut BinaryHeap<Entry>) {
    while let Some(Entry { cost, node }) = heap.pop() {
        let v = node as usize;
        if v >= row.len() || cost > row[v] + 1e-10 {
            continue;
        }
        for (u, edge_cost) in graph.neighbors_with_cost(node) {
            let next = cost + edge_cost;
            if (u as usize) < row.len() && next < row[u as usize] - 1e-10 {
                row[u as usize] = next;
                heap.push(Entry { cost: next, node: u });
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
struct Entry {
    cost: Cost,
    node: NodeId,
}
impl Eq for Entry {}
impl Ord for Entry {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_cost(other.cost, self.cost)
    }
}
impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::dreyfus_wagner;
    use crate::graph::NodeType;

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

    /// Singleton groups make the group Steiner oracle the ordinary Steiner
    /// problem, so it must agree with Dreyfus-Wagner on every subset.
    #[test]
    fn singleton_groups_reproduce_dreyfus_wagner() {
        let mut s = 0xFEED_FACE_1234_5678u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for n in 4..=11u32 {
            for _ in 0..40 {
                let k = 2 + (rng() % (n as u64 - 1).min(4)) as u32;
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
                    for v in u + 1..=n {
                        if rng() % 100 < 25 {
                            edges.push((u, v, 1.0 + (rng() % 9) as f64));
                        }
                    }
                }
                let g = make(n, &edges, &terminals);
                let groups: Vec<Vec<NodeId>> = terminals.iter().map(|&t| vec![t]).collect();
                let m = group_steiner_costs(&g, &groups, None).expect("oracle");
                for q in 1..(1usize << k) {
                    if (q as u32).count_ones() < 2 {
                        continue;
                    }
                    let sub: Vec<NodeId> = (0..k as usize)
                        .filter(|&i| q & (1 << i) != 0)
                        .map(|i| terminals[i])
                        .collect();
                    let dw = dreyfus_wagner(&g, &sub).expect("dw").optimal_cost;
                    assert!(
                        (m[q] - dw).abs() < 1e-6,
                        "group {} vs Dreyfus-Wagner {dw} on Q={q:b}",
                        m[q]
                    );
                }
            }
        }
    }

    /// A group's value is the minimum over choices of one member per group,
    /// checked against brute force.
    #[test]
    fn groups_take_the_best_representative() {
        let mut s = 0x0FF1_CE00_ABCD_4321u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for n in 5..=10u32 {
            for _ in 0..40 {
                let mut edges = Vec::new();
                for v in 2..=n {
                    edges.push((1 + (rng() % (v as u64 - 1)) as u32, v, 1.0 + (rng() % 9) as f64));
                }
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            edges.push((u, v, 1.0 + (rng() % 9) as f64));
                        }
                    }
                }
                // Two groups of two, drawn from distinct vertices.
                let mut pick: Vec<u32> = (1..=n).collect();
                for i in (1..pick.len()).rev() {
                    pick.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                if pick.len() < 4 {
                    continue;
                }
                let groups = vec![vec![pick[0], pick[1]], vec![pick[2], pick[3]]];
                let all: Vec<u32> = pick[..4].to_vec();
                let g = make(n, &edges, &all);
                let m = group_steiner_costs(&g, &groups, None).expect("oracle");
                let mut brute = f64::INFINITY;
                for &a in &groups[0] {
                    for &b in &groups[1] {
                        if let Some(r) = dreyfus_wagner(&g, &[a, b]) {
                            brute = brute.min(r.optimal_cost);
                        }
                    }
                }
                assert!((m[0b11] - brute).abs() < 1e-6, "{} vs {brute}", m[0b11]);
            }
        }
    }

    /// The coarsening ceiling, checked rather than only argued: the grouped
    /// dual never exceeds the group Steiner value of all its classes.
    #[test]
    fn the_coarsening_ceiling_binds() {
        let g = make(
            9,
            &[
                (1, 5, 3.0), (2, 5, 3.0), (3, 6, 3.0), (4, 6, 3.0), (5, 7, 1.0), (6, 7, 1.0),
                (7, 8, 2.0), (8, 9, 2.0), (1, 2, 9.0), (3, 4, 9.0),
            ],
            &[1, 2, 3, 4],
        );
        let terminals = vec![1, 2, 3, 4];
        for h in 2..=4usize {
            let Some(d) = grouped_hyp_dual(&g, &terminals, h, None) else { continue };
            let m = group_steiner_costs(&g, &d.groups, None).expect("oracle");
            let all = (1usize << d.groups.len()) - 1;
            assert!(
                d.lower_bound <= m[all] + 1e-6,
                "bound {} above the ceiling {} at h={h}",
                d.lower_bound,
                m[all]
            );
        }
    }

    /// The grouped dual is a bound however the terminals are clustered, and at
    /// singleton classes it recovers the enumerating module's value.
    #[test]
    fn the_grouped_dual_never_exceeds_the_optimum() {
        let mut s = 0xC0FF_EE12_3456_789Au64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut exercised = 0;
        for n in 6..=13u32 {
            for _ in 0..60 {
                let k = 3 + (rng() % (n as u64 - 2).min(6)) as u32;
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
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            edges.push((u, v, 1.0 + (rng() % 9) as f64));
                        }
                    }
                }
                let g = make(n, &edges, &terminals);
                let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
                // Every clustering size, including coarser than the terminal
                // set: the theorem claims validity for all of them.
                for max_groups in 2..=(k as usize) {
                    let Some(d) = grouped_hyp_dual(&g, &terminals, max_groups, None) else {
                        continue;
                    };
                    exercised += 1;
                    assert!(
                        d.lower_bound <= dw.optimal_cost + 1e-6,
                        "grouped bound {} exceeds the optimum {} at h<={max_groups}",
                        d.lower_bound,
                        dw.optimal_cost
                    );
                    // Independently: the multipliers are feasible for *every*
                    // terminal subset, not only for the grouped constraints
                    // they were solved against.
                    for q in 1u32..(1 << k) {
                        if q.count_ones() < 2 {
                            continue;
                        }
                        let sub: Vec<NodeId> = (0..k as usize)
                            .filter(|&i| q & (1 << i) != 0)
                            .map(|i| terminals[i])
                            .collect();
                        let smt = dreyfus_wagner(&g, &sub).expect("dw").optimal_cost;
                        // The class of each terminal, then the parts each
                        // partition's classes occupy.
                        let mut class_of = vec![usize::MAX; k as usize];
                        for (c, group) in d.groups.iter().enumerate() {
                            for &t in group {
                                class_of[(t - 1) as usize] = c;
                            }
                        }
                        let charge: Cost = d
                            .partitions
                            .iter()
                            .zip(d.lambda.iter())
                            .map(|(part, &l)| {
                                let mut seen = 0u64;
                                for i in 0..k as usize {
                                    if q & (1 << i) != 0 {
                                        seen |= 1 << part[class_of[i]];
                                    }
                                }
                                l * (seen.count_ones() as Cost - 1.0)
                            })
                            .sum();
                        assert!(
                            charge <= smt + 1e-6,
                            "grouped dual charges {charge} against smt {smt} on subset {q:b}"
                        );
                    }
                }
            }
        }
        assert!(exercised > 300, "only {exercised} clusterings ran");
    }

    /// The certificate the module exists for: whatever multipliers it is
    /// handed, the repaired dual is feasible for **every** terminal subset and
    /// its value never exceeds the optimum.
    #[test]
    fn a_priced_dual_never_exceeds_the_optimum() {
        let mut s = 0xB16B_00B5_DEAD_C0DEu64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut exercised = 0;
        for n in 5..=11u32 {
            for _ in 0..60 {
                let k = 3 + (rng() % (n as u64 - 2).min(4)) as u32;
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
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            edges.push((u, v, 1.0 + (rng() % 9) as f64));
                        }
                    }
                }
                let g = make(n, &edges, &terminals);
                let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };

                // Deliberately arbitrary multipliers, including wildly
                // infeasible ones: the repair, not the input, is what makes the
                // reported value a bound.
                let mut partitions: Vec<Vec<u32>> = Vec::new();
                for _ in 0..3 {
                    partitions.push((0..k).map(|_| (rng() % 3) as u32).collect());
                }
                partitions.push((0..k).collect());
                let lambda: Vec<Cost> =
                    (0..partitions.len()).map(|_| (rng() % 40) as Cost / 4.0).collect();

                let Some(priced) = price_and_repair(&g, &terminals, &partitions, &lambda, None)
                else {
                    continue;
                };
                exercised += 1;
                assert!(
                    priced.lower_bound <= dw.optimal_cost + 1e-6,
                    "priced bound {} exceeds the optimum {}",
                    priced.lower_bound,
                    dw.optimal_cost
                );

                // And the repaired multipliers really are feasible for every
                // subset, checked independently against Dreyfus-Wagner rather
                // than against the oracle that produced them.
                for q in 1u32..(1 << k) {
                    if q.count_ones() < 2 {
                        continue;
                    }
                    let sub: Vec<NodeId> = (0..k as usize)
                        .filter(|&i| q & (1 << i) != 0)
                        .map(|i| terminals[i])
                        .collect();
                    let smt = dreyfus_wagner(&g, &sub).expect("dw").optimal_cost;
                    let charge: Cost = partitions
                        .iter()
                        .zip(priced.lambda.iter())
                        .map(|(part, &l)| {
                            let mut seen = 0u64;
                            for (i, &p) in part.iter().enumerate() {
                                if q & (1 << i) != 0 {
                                    seen |= 1 << p;
                                }
                            }
                            l * (seen.count_ones() as Cost - 1.0)
                        })
                        .sum();
                    assert!(
                        charge <= smt + 1e-6,
                        "repaired dual charges {charge} against smt {smt} on subset {q:b}"
                    );
                }
            }
        }
        assert!(exercised > 150, "only {exercised} cases ran");
    }
}
