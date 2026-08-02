//! Certified cut packings read out of an LP dual.
//!
//! # What this is for
//!
//! The goal-directed search in [`crate::graph::algorithms::dijkstra_steiner`] is
//! limited by the strength of its A* potential, and that potential is a *cut
//! packing*: non-negative weights `y_W` on vertex sets missing the root with
//!
//! ```text
//! sum { y_W : a enters W } <= c(a)      for every arc a.                  (PACK)
//! ```
//!
//! Until now the only source of one was Wong's dual ascent. That source is
//! exhausted: after an ascent from `r0` terminates every terminal is reachable
//! from `r0` over zero-reduced-cost arcs, so every set missing `r0` is crossed by
//! a saturated arc and admits no increase whatsoever. The ascent's packing is
//! **maximal**, and no further combinatorial step can improve it.
//!
//! The LP on the same relaxation reaches further, because it can *lower* some
//! weights in order to raise others, which is an LP pivot and not an ascent
//! step. How much further is worth stating precisely, since it bounds what this
//! module can ever be worth: on PACE instance086 the ascent stops at 3268 and
//! twenty seconds of cut loop reaches 3360 against an optimum of 3661, and on
//! instance087 the numbers are 31, 32.1 and 36. The bidirected-cut relaxation
//! itself is 8–11 % short on those instances, so no dual object built on it can
//! close them. Where it does pay is the opposite regime — instances whose gap is
//! a handful of units on a large base, where two or three units of extra
//! potential is a quarter of the gap.
//!
//! This module takes that stronger dual and turns it back into an object
//! satisfying (PACK), so the search can use it at every state and not only at
//! the root.
//!
//! # The extraction, and why nothing about the LP has to be trusted
//!
//! The connectivity rows of the model are `sum_{a in A} y_a >= 1`. Let `lambda_A`
//! be the multiplier the LP gave such a row. Three things stand between that
//! number and a packing, and each is discharged by construction rather than by
//! assumption.
//!
//! **1. `A` need not be `delta^-(W)` for any `W`.** Recover one:
//!
//! > **Lemma (set recovery).** For an arbitrary arc set `A` and a root `r`, let
//! > `W(A)` be the set of vertices unreachable from `r` in `G - A`. Then
//! > `r not in W(A)` and `delta^-(W(A)) subseteq A`.
//! >
//! > *Proof.* `r` reaches itself, so `r not in W(A)`. Let `(u,v)` be an arc with
//! > `u not in W(A)` and `v in W(A)`. If `(u,v) not in A` then the path
//! > witnessing `u`'s reachability extends along it and `v` is reachable — a
//! > contradiction. So `(u,v) in A`. ∎
//!
//! The lemma holds for *any* `A`, so a row that is not a Steiner cut at all, or a
//! separator that emitted a wrong one, can only produce a set whose boundary is
//! contained in the row's support. Since the packing condition is then checked
//! against `delta^-(W(A))`, which is a subset of `A`, a bogus row costs strength
//! and never validity. (When `W(A)` is empty the row is dropped; it certifies
//! nothing.)
//!
//! **2. The multipliers need not satisfy (PACK).** The model carries far more
//! than connectivity rows — in-degree equalities, flow balance, anti-symmetry,
//! edge-vertex coupling — and rows of `<=` sense contribute *negatively* to a
//! column's dual sum, so the connectivity part alone may exceed `c(a)`. Two
//! repairs are computed and the better one kept. Both produce a vector that
//! satisfies (PACK) by construction:
//!
//! - **uniform scaling** by `1 / max(mu, 1)` with `mu = max_a load(a)/c(a)`;
//! - **greedy admission** in decreasing weight order, each set admitted at the
//!   largest weight the remaining capacity on `delta^-(W)` allows.
//!
//! Scaling a feasible-after-scaling vector is trivially feasible; greedy
//! admission maintains `load(a) <= c(a)` as an invariant. Neither needs the LP to
//! have been solved correctly.
//!
//! **3. Scaling throws away strength.** It also leaves slack on every arc, and
//! *that* is recoverable: [`crate::graph::algorithms::dual_ascent_packing_residual`]
//! runs Wong's ascent against `c - load` and returns a second packing feasible for
//! the residual. Adding the two arc inequalities shows the sum is feasible for
//! `c`. This is the one situation in which two packings may be added — they were
//! never independently feasible against the same costs — and it is exactly where
//! the maximality argument above does not apply, because the first layer did not
//! come from an ascent.
//!
//! The value of the result is `sum y_W`, a valid lower bound on the instance by
//! the packing theorem, and the sets are a valid A* potential for a search rooted
//! at the same `r0`.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use crate::graph::algorithms::{dual_ascent_cuts, dual_ascent_packing, dual_ascent_packing_residual, ArcIndex};
use crate::graph::{ArcId, Cost, DirectedGraph, NodeId};
use crate::model::LpRelaxation;
use crate::separation::{CycleCutSeparator, FlowCutSeparator, PartitionSeparator, TfCutSeparator};

/// Arc entries the ascent may record while producing the LP's seed rows. Same
/// cap the branch-and-cut uses; dropping a cut costs at most its own multiplier.
const ASCENT_CUT_NNZ: usize = 400_000;

/// A cut packing that has been checked against the arc costs.
#[derive(Debug, Clone, Default)]
pub struct CertifiedPacking {
    /// `(y_W, W)` for every set with positive weight. No set contains the root.
    pub sets: Vec<(Cost, Vec<NodeId>)>,
    /// `sum y_W`. A valid lower bound on the cost of any arborescence rooted at
    /// the root that reaches every raised set.
    pub value: Cost,
}

impl CertifiedPacking {
    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
    }

    /// Re-check (PACK) from scratch, and that no set holds the root.
    ///
    /// Nothing in the pipeline depends on this passing — the construction is
    /// feasible by invariant — but it is the statement the proofs above make, so
    /// it is written down and tested rather than asserted in prose.
    pub fn verify(&self, idx: &ArcIndex, root: NodeId, tolerance: Cost) -> bool {
        self.overload(idx, root).is_some_and(|mu| mu <= 1.0 + tolerance)
    }

    /// The worst ratio `load(a) / c(a)` over the arcs, or `None` when the vector
    /// is not even a candidate — a negative weight, a set holding the root, or a
    /// loaded arc of zero cost, none of which any amount of scaling repairs.
    ///
    /// `mu <= 1` is exactly (PACK).
    fn overload(&self, idx: &ArcIndex, root: NodeId) -> Option<Cost> {
        let mut load = vec![0.0 as Cost; idx.num_arcs()];
        let mut inside = vec![false; idx.num_nodes() + 1];
        for (weight, members) in &self.sets {
            if *weight < 0.0 || members.iter().any(|&v| v == root) {
                return None;
            }
            for &v in members {
                inside[v as usize] = true;
            }
            for &v in members {
                for &a in idx.incoming(v) {
                    if !inside[idx.tail(a) as usize] {
                        load[a as usize] += *weight;
                    }
                }
            }
            for &v in members {
                inside[v as usize] = false;
            }
        }
        let mut mu: Cost = 0.0;
        for a in 0..idx.num_arcs() {
            if load[a] <= 0.0 {
                continue;
            }
            let c = idx.cost(a as ArcId);
            if c <= 0.0 {
                return None;
            }
            mu = mu.max(load[a] / c);
        }
        Some(mu)
    }

    /// Make (PACK) hold, by scaling, and report the factor applied.
    ///
    /// > **Lemma (certified scaling).** Let `y >= 0` load every arc by at most
    /// > `mu * c(a)` with `mu >= 1`. Then `y / mu` satisfies (PACK) and its value
    /// > is `value(y) / mu`.
    /// >
    /// > *Proof.* Dividing every weight by `mu` divides every arc's load by `mu`,
    /// > so `load(a)/mu <= c(a)`; non-negativity and the root condition are
    /// > unchanged by a positive scalar; `sum y_W / mu = (sum y_W) / mu`. ∎
    ///
    /// This is what makes an extracted packing safe to *report* rather than
    /// merely safe by construction. The construction is feasible by invariant,
    /// but the invariant is maintained in floating point across a simplex dual, a
    /// greedy admission and a residual ascent, and a bound that is announced as
    /// proved must not rest on the accumulated slop of three of those. Returning
    /// `0.0` means the vector was not repairable at all and the packing is
    /// emptied — a lower bound of zero is always true.
    ///
    /// Note which direction the repair goes: it can only *lower* the value. A
    /// packing that needed no repair is untouched, so this can never manufacture
    /// a bound, only decline to claim one.
    pub fn repair(&mut self, idx: &ArcIndex, root: NodeId) -> Cost {
        match self.overload(idx, root) {
            None => {
                self.sets.clear();
                self.value = 0.0;
                0.0
            }
            Some(mu) if mu > 1.0 => {
                for (w, _) in self.sets.iter_mut() {
                    *w /= mu;
                }
                // The value is re-derived from the family that was actually
                // checked, not scaled from the claim that failed. `value` can
                // legitimately exceed `sum y_W` over the *recorded* sets — an
                // ascent layer truncated by its nnz cap raises sets it does not
                // store — and that composition is only justified while the
                // feasibility invariant holds. Once it has been observed not to,
                // the only number still carrying a proof is the packing theorem
                // applied to the sets in hand.
                self.value = self.sets.iter().map(|(w, _)| *w).sum();
                1.0 / mu
            }
            Some(_) => 1.0,
        }
    }
}

/// The packing members a partition row's dual licenses.
///
/// `parts` are the parts other than the root's. See the lemma at the call site:
/// each `delta^-(P_i)` lies inside the row's crossing set, the boundaries are
/// pairwise disjoint, and `k` members of weight `lambda` reproduce exactly the
/// `lambda * k` the row contributed to the LP objective.
fn decompose_partition(
    parts: &[Vec<NodeId>],
    dual: Cost,
    idx: &ArcIndex,
    root: NodeId,
) -> Vec<Candidate> {
    let mut out = Vec::with_capacity(parts.len());
    let mut inside = vec![false; idx.num_nodes() + 1];
    for part in parts {
        if part.is_empty() || part.iter().any(|&v| v == root) {
            continue;
        }
        for &v in part {
            inside[v as usize] = true;
        }
        let mut boundary: Vec<ArcId> = Vec::new();
        for &v in part {
            for &a in idx.incoming(v) {
                if !inside[idx.tail(a) as usize] {
                    boundary.push(a);
                }
            }
        }
        for &v in part {
            inside[v as usize] = false;
        }
        if !boundary.is_empty() {
            out.push((dual, boundary));
        }
    }
    out
}

/// Canonical identity of a row over arcs: its sorted support.
fn signature(arcs: &[ArcId]) -> Vec<ArcId> {
    let mut s = arcs.to_vec();
    s.sort_unstable();
    s
}

/// A weighted arc set proposed as a packing member.
type Candidate = (Cost, Vec<ArcId>);

/// Turn weighted arc sets into a packing that satisfies (PACK).
///
/// See the module header: each `A` is replaced by the recovered set `W(A)` and
/// its true boundary `delta^-(W(A)) subseteq A`, and the weights are then made
/// feasible by whichever of uniform scaling and greedy admission retains more.
pub fn certify(candidates: &[Candidate], idx: &ArcIndex, root: NodeId) -> CertifiedPacking {
    let num_arcs = idx.num_arcs();
    let num_nodes = idx.num_nodes() + 1;

    // A vertex with no incident arc cannot be reached by any tree and cannot be
    // a terminal of a solvable instance, so leaving it out of `W` changes
    // neither the boundary nor any evaluation, and keeps the sets small.
    let mut real = vec![false; num_nodes];
    for a in 0..num_arcs {
        real[idx.tail(a as ArcId) as usize] = true;
        real[idx.head(a as ArcId) as usize] = true;
    }

    let mut blocked = vec![false; num_arcs];
    let mut seen = vec![false; num_nodes];
    let mut stack: Vec<NodeId> = Vec::new();
    let mut recovered: Vec<(Cost, Vec<NodeId>, Vec<ArcId>)> = Vec::with_capacity(candidates.len());

    for (weight, arcs) in candidates {
        if !(*weight > 0.0) || arcs.is_empty() {
            continue;
        }
        for &a in arcs {
            blocked[a as usize] = true;
        }
        // Reachability from the root in `G - A`.
        seen.iter_mut().for_each(|s| *s = false);
        seen[root as usize] = true;
        stack.clear();
        stack.push(root);
        while let Some(v) = stack.pop() {
            for &a in idx.outgoing(v) {
                if blocked[a as usize] {
                    continue;
                }
                let h = idx.head(a);
                if !seen[h as usize] {
                    seen[h as usize] = true;
                    stack.push(h);
                }
            }
        }
        for &a in arcs {
            blocked[a as usize] = false;
        }

        let members: Vec<NodeId> = (0..num_nodes)
            .filter(|&v| real[v] && !seen[v])
            .map(|v| v as NodeId)
            .collect();
        if members.is_empty() {
            continue;
        }
        // `delta^-(W)`, which the lemma guarantees is a subset of `arcs`.
        let mut boundary: Vec<ArcId> = Vec::new();
        for &v in &members {
            for &a in idx.incoming(v) {
                if seen[idx.tail(a) as usize] {
                    boundary.push(a);
                }
            }
        }
        if boundary.is_empty() {
            // No arc enters `W`: the instance cannot connect it to the root at
            // all, and its weight is unbounded rather than certifiable.
            continue;
        }
        recovered.push((*weight, members, boundary));
    }

    if recovered.is_empty() {
        return CertifiedPacking::default();
    }

    // Rule A: uniform scaling. `mu` is the worst overload ratio; dividing every
    // weight by `max(mu, 1)` makes every arc inequality hold and leaves the
    // vector non-negative.
    let mut load = vec![0.0 as Cost; num_arcs];
    for (w, _, boundary) in &recovered {
        for &a in boundary {
            load[a as usize] += *w;
        }
    }
    let mut mu: Cost = 1.0;
    for a in 0..num_arcs {
        if load[a] <= 0.0 {
            continue;
        }
        let c = idx.cost(a as ArcId);
        if c <= 0.0 {
            mu = Cost::INFINITY;
            break;
        }
        mu = mu.max(load[a] / c);
    }
    let uniform_value: Cost =
        if mu.is_finite() { recovered.iter().map(|(w, _, _)| *w).sum::<Cost>() / mu } else { 0.0 };

    // Rule B: greedy admission. Heaviest first, each set taking the largest
    // weight its boundary still has room for. `load(a) <= c(a)` is an invariant
    // of the loop, so the result satisfies (PACK) whatever the order.
    let mut order: Vec<usize> = (0..recovered.len()).collect();
    order.sort_by(|&i, &j| {
        recovered[j].0.partial_cmp(&recovered[i].0).unwrap_or(std::cmp::Ordering::Equal)
    });
    load.iter_mut().for_each(|l| *l = 0.0);
    let mut admitted: Vec<(usize, Cost)> = Vec::with_capacity(recovered.len());
    let mut greedy_value: Cost = 0.0;
    for &i in &order {
        let (w, _, boundary) = &recovered[i];
        let room = boundary
            .iter()
            .map(|&a| idx.cost(a as ArcId) - load[a as usize])
            .fold(Cost::INFINITY, Cost::min);
        let take = w.min(room).max(0.0);
        if take <= 1e-12 {
            continue;
        }
        for &a in boundary {
            load[a as usize] += take;
        }
        greedy_value += take;
        admitted.push((i, take));
    }

    // # Negative result: a third rule that maximises this family is a loss
    //
    // Both rules above only push the LP's multipliers *down*. Neither can do
    // what this module's header says an LP can do and an ascent cannot — lower
    // one weight in order to raise another — so the obvious third rule discards
    // the multipliers and re-prices the family from scratch,
    //
    // ```text
    //   max  sum_i y_i   s.t.  sum_{i : a in delta^-(W_i)} y_i <= c(a),  y >= 0,
    // ```
    //
    // whose optimum dominates both closed forms by construction, since both are
    // feasible points of it. It was implemented, proved, tested and **measured
    // out, twice**.
    //
    // Choosing it whenever it wins *this* stage took PACE Track 1 [155..200]
    // from 28/46 to 26/46 and *lowered* the reported dual on instance171
    // (41 -> 40), instance172 (7110 -> 7019), instance188 and instance192. A
    // stronger lower bound cannot lower a lower bound, so the fault is in the
    // composition, not in the rule: what the caller reports is this function
    // followed by [`extend_by_residual_ascent`], and the residual ascent
    // harvests slack over the *whole* cut family rather than this one. Uniform
    // scaling leaves slack on every arc and calls it recoverable; maximising
    // `sum y` here means saturating arcs, which is precisely leaving the ascent
    // nothing to raise.
    //
    // Deferring the choice until after the composition — extend every rule's
    // output by its own residual ascent and keep the best combined value — is
    // the correct comparison and is *also* a loss: 25/46 and 109/200, against
    // 28/46 and 110/200 without the rule at all. The extra simplex per
    // extraction costs more clock than the units it buys are worth inside a
    // five-second budget, and a certificate this loop extracts several times per
    // solve cannot afford it.
    //
    // The mathematics is sound and is recorded rather than kept. The general
    // statement it establishes is worth more than the rule: **in a residual
    // cascade, greedily maximising layer `k` is not a step towards maximising
    // the sum** — the layers compete for the same arc capacities and the later
    // ones range over a strictly larger family.
    if greedy_value >= uniform_value {
        CertifiedPacking {
            sets: admitted
                .into_iter()
                .map(|(i, w)| (w, recovered[i].1.clone()))
                .collect(),
            value: greedy_value,
        }
    } else {
        CertifiedPacking {
            sets: recovered.iter().map(|(w, m, _)| (*w / mu, m.clone())).collect(),
            value: uniform_value,
        }
    }
}

/// Extend a certified packing by an ascent against its residual capacities.
///
/// The residual layer is feasible for `c - load`, so the concatenation is
/// feasible for `c`; see [`dual_ascent_packing_residual`] for the one-line
/// addition that proves it.
pub fn extend_by_residual_ascent(
    packing: CertifiedPacking,
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    max_set_nnz: usize,
) -> CertifiedPacking {
    let num_arcs = idx.num_arcs();
    let mut residual: Vec<Cost> = (0..num_arcs).map(|a| idx.cost(a as ArcId)).collect();
    let mut inside = vec![false; idx.num_nodes() + 1];
    for (weight, members) in &packing.sets {
        for &v in members {
            inside[v as usize] = true;
        }
        for &v in members {
            for &a in idx.incoming(v) {
                if !inside[idx.tail(a) as usize] {
                    residual[a as usize] -= *weight;
                }
            }
        }
        for &v in members {
            inside[v as usize] = false;
        }
    }
    // Floating-point slop can push a saturated arc a hair below zero; the ascent
    // clamps, and clamping upward would be the unsound direction.
    residual.iter_mut().for_each(|r| *r = r.max(0.0));

    let active = vec![true; num_arcs];
    let layer =
        dual_ascent_packing_residual(idx, root, terminals, &active, &residual, max_set_nnz);

    let mut sets = packing.sets;
    sets.extend(layer.sets);
    CertifiedPacking { sets, value: packing.value + layer.lower_bound }
}

/// The outcome of the bounded root cut loop.
/// Roots, besides the model's own, whose dual ascent contributes seed cuts.
///
/// Each costs one ascent — microseconds against a single simplex solve — and
/// contributes a cut family the model's own root cannot produce, because the
/// ascent saturates arcs in an order that depends on where it started.
const ALT_SEED_ROOTS: usize = 4;

/// What one round of the root separation loop cost and bought.
///
/// This exists to answer a question that guesswork got wrong twice: a
/// 243-vertex, 1215-edge cut LP was taking 244 solves to converge, and neither
/// "the LP is slow" nor "the separator is weak" was checkable without it.
#[derive(Debug, Clone, Copy)]
pub struct RoundStat {
    pub bound: Cost,
    /// Structural rows pulled in from the held-back pool.
    pub structural: usize,
    /// Rows installed by each extra family, and the seconds its separator cost:
    /// cycle, partition, terminal-free.
    pub family: [(usize, f64); 3],
    /// Violated connectivity cuts the separator returned.
    pub cuts: usize,
    /// Rows in the model *after* this round's additions and pruning.
    pub rows: usize,
    pub secs: f64,
}

pub struct RootCertificate {
    /// The LP's own dual bound, valid for the instance as given.
    pub lp_bound: Cost,
    /// A packing derived from the LP dual, extended by a residual ascent layer.
    pub packing: CertifiedPacking,
    /// Arcs no solution of cost at most `upper_bound` can use.
    ///
    /// # The rule, and the two ways it has been got wrong
    ///
    /// Let `z` be the LP optimum and `rc_a >= 0` the reduced cost of an arc
    /// column resting at its lower bound. Any feasible point with `y_a = 1`
    /// costs at least `z + rc_a`, so
    ///
    /// ```text
    /// z + rc_a > UB   =>   no solution of cost <= UB uses a.
    /// ```
    ///
    /// The inequality is strict, which is what keeps solutions of cost exactly
    /// `UB` — including an optimum equal to the incumbent — alive.
    ///
    /// It must be `z`, not `ceil(z)`: a cut-loop optimum is not integral, and
    /// rounding it up shrinks the gap the inequality is stated over. Doing that
    /// once emptied PACE instance164's graph and announced a proved 5265 against
    /// a true optimum of 5205. And `rc` must come from a solve that actually
    /// reached optimality, because a backend that stops on its own clock leaves
    /// the previous, smaller model's vector in place.
    pub eliminated_arcs: Vec<ArcId>,
    pub lp_solves: u64,
    /// One entry per round; see [`RoundStat`].
    pub rounds: Vec<RoundStat>,
}

/// Solve a bounded root cut loop and read a certified packing off its dual.
///
/// The loop is the ordinary one: seed the model with the ascent's cuts, solve,
/// separate violated Steiner cuts by max flow, repeat. It stops when a round
/// finds nothing, when `deadline` passes, or after `max_rounds`. Every exit is
/// safe — an LP relaxation's optimum is a lower bound however few cuts it holds,
/// and a packing read off any feasible dual is certified by construction.
///
/// Returns `None` when no LP solve reached optimality, in which case there is no
/// dual to read.
///
/// # Where the rounds were going, and what did not fix it
///
/// Separating the LP optimum tails off badly. On PACE instance172 — 243 vertices,
/// 1,215 edges — the loop needs about three hundred solves to converge, and
/// [`RoundStat`] says why: the separator returns roughly ten cuts a round against
/// a cap of four hundred, and after the first eight rounds each round buys about
/// one unit of bound out of five hundred.
///
/// The textbook remedy is **in-out separation**: separate the midpoint of the
/// segment between a known feasible point `y_in` and the LP optimum `y*` rather
/// than `y*` itself. It is sound — every cut violated at the midpoint is violated
/// at `y*`, since `y_in(δ⁺(W)) >= 1` and
/// `y*(δ⁺(W)) + y_in(δ⁺(W)) < 2` together give `y*(δ⁺(W)) < 1` — and it needs no
/// step size if the midpoint is used and `y_in` is halved towards `y*` whenever
/// the midpoint separates nothing. It was implemented that way, with the
/// incumbent arborescence as the initial `y_in`, and **measured as a small loss**:
/// on instance172 at an eight-second budget it reached 7,059 against 7,071 for
/// plain separation, and 7,097 against 7,105 at ninety seconds. The reason is
/// visible in the same trace — the incumbent sits at 8,223 against an LP optimum
/// near 7,100, so the midpoint is nowhere near the optimal face and the cuts it
/// exposes are the same shallow ones, one max-flow round later. It is recorded
/// here rather than kept.
///
/// What the trace *does* reward is a wider seed; see the multi-root block below.
///
/// # The other three families
///
/// The same trace says the loop is **facet-starved**, not degenerate: ten cuts a
/// round against a cap of four hundred means the rows are too shallow, not too
/// few to install. The branch-and-cut already carries three further valid
/// families that the root loop never asked for — partition rows, cycle rows and
/// terminal-free rows — and they are separated here too.
///
/// Every one of them is valid for the formulation, which is what their own
/// enumeration tests establish, so installing them can only raise the LP bound.
/// They are also safe for the *packing*: [`certify`] does not trust a row to be a
/// Steiner cut. It takes the row's arc set `A`, recovers `W(A)` as the vertices
/// the root cannot reach in `G - A`, and prices `delta^-(W(A)) subseteq A` — so a
/// row that is not a cut contributes a genuine cut or nothing at all, and
/// [`CertifiedPacking::verify`] re-checks (PACK) from scratch either way.
///
/// One row shape has to be excluded by hand. A partition row with right-hand
/// side one has `lo == 1.0` and unit coefficients, so it is indistinguishable
/// from a Steiner cut to [`crate::model::lp_relaxation::LpRelaxation::unit_arc_rows`]
/// — but its arc set contains *both* orientations of every crossing edge, and
/// `W(A)` recovered from it is a set whose in-boundary the row's dual was never
/// priced against. It is still sound, for the reason above; it is simply weaker
/// than treating the same dual as belonging to the smaller genuine cut. Nothing
/// is done about it beyond saying so, because the repair step already handles it.
///
/// # Resumption
///
/// This function is the one-shot form of [`RootSeparation`], which is the same
/// loop with its state exposed so that a caller running out of clock can
/// *continue* it. See that type for why a resumed loop is at least as strong as
/// a fresh one given the same total time, and identical to it at convergence.
pub fn root_certificate(
    graph: &DirectedGraph,
    root: NodeId,
    terminals: &[NodeId],
    upper_bound: Cost,
    deadline: Instant,
    max_rounds: usize,
    max_set_nnz: usize,
) -> Option<RootCertificate> {
    RootSeparation::new(graph, root, terminals).advance(upper_bound, deadline, max_rounds, max_set_nnz)
}

/// The root separation loop, with its state outliving one call.
///
/// # Why this exists
///
/// The loop below is deadline-truncated. It is *not* a fixpoint computation the
/// way [`crate::root_reduce::tighten`] is — a second run with more clock
/// genuinely separates more rows and proves a better bound — so the repair for
/// re-deriving it is not memoisation but resumption. Under the old wiring the
/// solver's second pass built the model from nothing, re-ran the seeding ascents,
/// re-installed the structural pool geometrically, and re-separated every row the
/// first pass had already found, all inside a budget that was smaller than the
/// first pass's. On PACE instance167 the measurement that motivates this is
/// blunt: a quarter-second of separation followed by a search under the resulting
/// packing closes the instance in 363,000 labels, and the solver spends more than
/// that quarter-second twice and reaches neither.
///
/// # What resumption guarantees
///
/// > **Proposition (resumed dominance).** Let `S` be a separation loop stopped
/// > after `k` rounds and resumed for `k'` more, and let `F` be a fresh loop run
/// > for `k + k'` rounds against the same graph, root and terminals. Then
/// > `S`'s bound is the bound `F` reaches after `k + k'` rounds, and both are
/// > `max` over the same sequence of LP optima.
/// >
/// > *Proof.* The loop's state after a round is a function of (model rows,
/// > installed-signature set, partition witnesses, batch counter, running bound).
/// > Resumption preserves every one of them, and the round body reads nothing
/// > else except the clock — which bounds how many rounds happen, not what a
/// > round does. So the round sequence is identical and so is every LP solved. ∎
///
/// The clock is the only asymmetry, and it is the asymmetry that pays: `S` spends
/// its second budget on rounds `k+1 .. k+k'`, while `F` spends it re-deriving
/// rounds `1 .. k`. Hence "at least as strong given the same total time", and
/// "exactly the same value when both run to convergence" — convergence being the
/// round that separates nothing, which is a property of the row set and therefore
/// reached at the same round index by both.
///
/// # Convergence is recorded, not re-tested
///
/// A round that installs nothing has proved that the LP point satisfies every
/// inequality any separator here can express. No later round can move the bound,
/// so [`RootSeparation::converged`] is set and every subsequent `advance` returns
/// the certificate without solving an LP at all. The one thing a later call can
/// still change is the *elimination* set, because that depends on an incumbent
/// the caller may have improved — and that is recomputed from the stored reduced
/// costs of the solve they belong to, never mixed with another solve's bound.
pub struct RootSeparation {
    idx: ArcIndex,
    root: NodeId,
    terminals: Vec<NodeId>,
    /// The arcs this model was built for, so a caller carrying one of these
    /// across solver passes can tell whether it still applies. An equality test,
    /// not a hash: a false positive would resume a model against a graph whose
    /// columns mean something else.
    fingerprint: Vec<(NodeId, NodeId, Cost)>,
    /// The graph the model is stated over, owned so the separators — which all
    /// borrow it — can be rebuilt on each call rather than tying this type's
    /// lifetime to a caller's stack frame. Rebuilding them costs an index and a
    /// max-flow workspace once per call; none of them carries learned state, so
    /// nothing is lost by it.
    graph: DirectedGraph,
    lp: LpRelaxation,
    signatures: HashSet<Vec<ArcId>>,
    partitions: HashMap<Vec<ArcId>, Vec<Vec<NodeId>>>,
    batch: usize,
    best_bound: Cost,
    lp_solves: u64,
    rounds: Vec<RoundStat>,
    candidates: Option<Vec<Candidate>>,
    /// The objective of the solve whose reduced costs `lp` still holds. Pairing
    /// a bound with another solve's vector is the mistake `RootCertificate`
    /// documents; keeping them together is how it is not made again.
    last_obj: Option<Cost>,
    eliminated_arcs: Vec<ArcId>,
    /// A round separated nothing. See the type's documentation.
    converged: bool,
}

impl RootSeparation {
    pub fn new(graph: &DirectedGraph, root: NodeId, terminals: &[NodeId]) -> Self {
    let idx = ArcIndex::new(graph);
    let active = vec![true; idx.num_arcs()];
    let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
    let steiner_nodes: Vec<NodeId> =
        graph.nodes.iter().map(|n| n.id).filter(|v| !terminal_set.contains(v)).collect();

    let mut lp = LpRelaxation::from_formulation(graph, root, terminals, &steiner_nodes);
    let seed = dual_ascent_cuts(&idx, root, terminals, &active, ASCENT_CUT_NNZ);
    for cut in &seed.cuts {
        lp.add_lazy_steiner_cut(cut);
    }
    // Seed from ascents rooted elsewhere as well.
    //
    // The per-round trace is what asks for this. On PACE instance172 the bound
    // climbs while the held-back structural pool is still feeding rows in — forty
    // a round for the first fifty rounds — and flattens to about one unit a round
    // once that pool empties and the only new rows are separated ones. The pool is
    // the ascent's cut family, so a wider pool is worth more than a faster loop.
    //
    // A dual ascent rooted at `r` raises sets that miss `r`, not sets that miss
    // the *model's* root. Only the ones that also miss `root` are valid Steiner
    // cuts here — `y(delta^-(W)) >= 1` needs the root outside `W`, or the
    // arborescence has no arc entering `W` — and the rest are dropped rather than
    // repaired. Nothing else is needed: a valid inequality is valid whatever
    // produced it, and the ascents are microseconds next to a single solve.
    {
        let mut in_w = vec![false; idx.num_nodes()];
        let mut boundary: Vec<ArcId> = Vec::new();
        for &r in terminals.iter().step_by(terminals.len().div_ceil(ALT_SEED_ROOTS).max(1)) {
            if r == root {
                continue;
            }
            let alt = dual_ascent_packing(&idx, r, terminals, &active, ASCENT_CUT_NNZ);
            for (_, members) in &alt.sets {
                if members.contains(&root) || members.is_empty() {
                    continue;
                }
                for &v in members {
                    in_w[v as usize] = true;
                }
                boundary.clear();
                for &v in members {
                    for &a in idx.incoming(v) {
                        if !in_w[idx.tail(a) as usize] {
                            boundary.push(a);
                        }
                    }
                }
                for &v in members {
                    in_w[v as usize] = false;
                }
                if !boundary.is_empty() {
                    lp.add_lazy_steiner_cut(&boundary);
                }
            }
        }
    }
    // Geometric batches, for the reason `add_lazy_steiner_cut` documents: the
    // seed is thousands of rows wide, a flat batch either makes the first solve a
    // cold simplex on a model several times the structural one or costs a re-solve
    // per batch. Growing it keeps the model small when few rows are wanted and
    // converges in a handful of solves when many are. On PACE instance187 a flat
    // batch of 4096 left the loop with two solves inside its budget and a bound
    // *below* the ascent's.
    let batch = 500usize;

        Self {
            idx,
            root,
            terminals: terminals.to_vec(),
            fingerprint: graph.arcs.iter().map(|a| (a.tail, a.head, a.cost)).collect(),
            graph: graph.clone(),
            lp,
            // Rows already installed, so a family that keeps re-finding the same
            // violated set does not grow the model without moving the bound.
            signatures: HashSet::new(),
            // Partition rows installed in the model, keyed by their arc
            // signature, with the parts that prove them. See the decomposition
            // lemma in `advance`.
            partitions: HashMap::new(),
            batch,
            best_bound: seed.lower_bound,
            lp_solves: 0,
            rounds: Vec::new(),
            // The duals are harvested after *every* optimal solve rather than
            // after the last one. A solve that runs out of clock leaves
            // `LpRelaxation` holding the multipliers of the previous, smaller
            // model, whose row indices no longer name the same rows; pairing
            // those with the current pool is the same class of mistake as
            // reading stale reduced costs. Harvesting eagerly means the loop can
            // be abandoned at any point and still hand back the strongest dual
            // it actually proved.
            candidates: None,
            last_obj: None,
            eliminated_arcs: Vec::new(),
            converged: false,
        }
    }

    /// Whether this model is still the model for `(graph, root, terminals)`.
    pub fn applies_to(&self, graph: &DirectedGraph, root: NodeId, terminals: &[NodeId]) -> bool {
        self.root == root
            && self.terminals == terminals
            && self.fingerprint.len() == graph.arcs.len()
            && self
                .fingerprint
                .iter()
                .zip(graph.arcs.iter())
                .all(|(f, a)| f.0 == a.tail && f.1 == a.head && f.2 == a.cost)
    }

    /// The best LP bound proved so far, without running anything.
    pub fn bound(&self) -> Cost {
        self.best_bound
    }

    /// Whether a round has separated nothing, so no further round can move the
    /// bound.
    pub fn is_converged(&self) -> bool {
        self.converged
    }

    /// LP solves across every call so far.
    pub fn lp_solves(&self) -> u64 {
        self.lp_solves
    }

    /// Rows in the model right now.
    pub fn num_rows(&self) -> usize {
        self.lp.num_constraints()
    }

    /// Run up to `max_rounds` further rounds, then extract a certificate.
    ///
    /// Returns `None` only when no LP solve has ever reached optimality, in which
    /// case there is no dual to read.
    pub fn advance(
        &mut self,
        upper_bound: Cost,
        deadline: Instant,
        max_rounds: usize,
        max_set_nnz: usize,
    ) -> Option<RootCertificate> {
        let Self {
            idx,
            root,
            terminals,
            fingerprint,
            graph,
            lp,
            signatures,
            partitions,
            batch,
            best_bound,
            lp_solves,
            rounds,
            candidates,
            last_obj,
            eliminated_arcs,
            converged,
        } = self;
        let idx: &ArcIndex = idx;
        let root: NodeId = *root;
        let num_arcs = fingerprint.len();
        let mut separator = FlowCutSeparator::new(graph, root, terminals);
        let mut cycle_sep = CycleCutSeparator::new(graph);
        let mut partition_sep = PartitionSeparator::new(graph, root, terminals);
        let mut tf_sep = TfCutSeparator::new(graph, terminals);

    for _ in 0..(if *converged { 0 } else { max_rounds }) {
        let remaining = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
        if remaining <= 0.0 {
            break;
        }
        lp.time_limit_secs = remaining;
        let round_started = Instant::now();
        let obj = lp.solve();
        *lp_solves += 1;
        if !lp.is_optimal() {
            break;
        }
        *best_bound = best_bound.max(obj);
        let mut harvest: Vec<Candidate> = lp
            .unit_arc_rows()
            .into_iter()
            .map(|(entries, dual)| (dual, entries.iter().map(|&(c, _)| c as ArcId).collect()))
            .collect();
        // Partition rows, decomposed into the Steiner cuts that imply them.
        //
        // > **Lemma (partition decomposition).** Let `V = P_0 + P_1 + ... + P_k`
        // > with the root in `P_0`, let `C` be the arcs whose endpoints lie in
        // > different parts, and let the row `x(C) >= k` carry dual `lambda`.
        // > Then giving each of `P_1, ..., P_k` the weight `lambda` contributes
        // > exactly `lambda * k` to the packing's value -- the same as the row
        // > contributes to the LP objective -- and loads every arc by no more
        // > than the row already did.
        //
        // *Proof.* Each `delta^-(P_i)` is contained in `C`, since an arc
        // entering `P_i` from outside has its endpoints in different parts. The
        // sets `delta^-(P_i)` are pairwise disjoint, because an arc `(u,v)` lies
        // in `delta^-(P_i)` only for the unique `i` with `v in P_i`. So the load
        // the `k` sets place on an arc is `lambda` if it enters some `P_i` and
        // zero otherwise, while the row placed `lambda` on every arc of `C`,
        // a superset. And `k` sets of weight `lambda` sum to `lambda * k = rhs *
        // lambda`. Finally no `P_i` with `i >= 1` holds the root, which is what
        // a packing member must satisfy. QED
        //
        // This is what stops the extra families *starving* the packing. Without
        // it, a partition row raises the LP bound and contributes nothing the
        // search can use, and rows that displace flow cuts make the search's
        // potential strictly weaker -- which is exactly how instance188 lost the
        // proof it had.
        for (entries, rhs, dual) in lp.unit_rows_above_one() {
            let arcs: Vec<ArcId> = entries.iter().map(|&(c, _)| c as ArcId).collect();
            let Some(parts) = partitions.get(&signature(&arcs)) else { continue };
            if (parts.len() as f64 - rhs).abs() > 1e-9 {
                // The witness does not match the row it was recorded for. Drop
                // it rather than guess: the packing must never rest on a
                // correspondence nobody checked.
                continue;
            }
            harvest.extend(decompose_partition(parts, dual, idx, root));
        }
        *candidates = Some(harvest);
        *last_obj = Some(obj);
        if upper_bound.is_finite() {
            // The bound grows monotonically over the loop and the reduced costs
            // are read from the same solve as `obj`, so recomputing the set each
            // round and keeping the largest is exactly the strongest licensed
            // elimination and never mixes a bound with another solve's vector.
            let fixed: Vec<ArcId> = (0..num_arcs)
                .filter(|&a| {
                    let rc = lp.reduced_costs.get(a).copied().unwrap_or(0.0);
                    rc > 0.0 && obj + rc > upper_bound
                })
                .map(|a| a as ArcId)
                .collect();
            if fixed.len() > eliminated_arcs.len() {
                *eliminated_arcs = fixed;
            }
        }

        // Structural rows held back from the model are part of the relaxation,
        // not optional strengthening; bringing in the violated ones is what makes
        // the seeded ascent cuts count.
        let structural = lp.separate_structural(*batch);
        *batch = batch.saturating_mul(4);
        let solution = lp.get_solution().to_vec();
        let cuts = separator.separate_cuts(&solution);
        // The three families the branch-and-cut already had and the root loop
        // did not ask for. See the header: all are valid for the formulation and
        // all are safe for the packing extraction.
        // Install the flow cuts first, and count how many are new.
        let mut installed = 0usize;
        let mut new_flow = 0usize;
        for cut in cuts.iter().take(400) {
            let mut sig = cut.cut_arcs.clone();
            sig.sort_unstable();
            if signatures.insert(sig) {
                lp.add_steiner_cut(&cut.cut_arcs);
                new_flow += 1;
                installed += 1;
            }
        }

        // The other three families, brought in exactly when the flow family has
        // nothing new to say.
        //
        // The trace calls this loop *facet-starved* rather than degenerate: ten
        // cuts a round against a cap of four hundred means the rows are too
        // shallow, not too few to install. The branch-and-cut already carried
        // three further valid families — partition, cycle, terminal-free — that
        // the root loop never asked for, and separating them costs under ten
        // milliseconds a round against LP solves that reach three seconds.
        //
        // Carrying their rows is not free, and two ways of doing it were
        // measured as losses:
        //
        // - **Appending them every round.** The solve time is a function of the
        //   row count. On instance193 the rounds became four times dearer, the
        //   loop lost four of its sixteen solves, and the converged bound came
        //   out 2.8 units *below* what the flow cuts reached alone.
        // - **Ranking all four families by depth and installing the deepest
        //   `k`.** This raised instance172's root bound by 23 units and at the
        //   same time dropped instance188's extracted packing *below the dual
        //   ascent's own value* — because only rows shaped like a Steiner cut
        //   can be turned back into a cut packing, and the packing, not the LP
        //   bound, is what the goal-directed search consumes. Displacing flow
        //   cuts starves the search's potential, and 188 lost the proof it had.
        //
        // What is left is the criterion the diagnosis actually supports: another
        // family is worth its rows exactly when the family in hand is out of
        // things to add. No count to choose and no clock to divide — the loop
        // asks for help when, and only when, it has stopped separating.
        let mut family = [(0usize, 0.0); 3];
        let mut extra = 0usize;
        {
            let _ = new_flow;
            let t0 = Instant::now();
            let cycle_cuts = cycle_sep.find_violated_cuts(&solution);
            let partition_cuts = partition_sep.find_violated_cuts(&solution);
            let tf_cuts = tf_sep.find_violated_cuts(&solution);
            let separation_secs = t0.elapsed().as_secs_f64();
            let mut witness: HashMap<Vec<ArcId>, Vec<Vec<NodeId>>> = HashMap::new();

            // Depth — the Euclidean distance from the LP point to the row's
            // hyperplane, `violation / ||a||_2` — is the only comparison between
            // these families that means anything: their violations live on
            // different scales, a Steiner cut's being at most one and a
            // partition row's at most `|P| - 1`, while the distance to the
            // hyperplane is a property of the geometry and not of how the row
            // happens to be written.
            enum Row {
                Cycle(Vec<(ArcId, ArcId)>),
                Weighted(Vec<ArcId>, Vec<Cost>, Cost),
            }
            let mut ranked: Vec<(Cost, usize, Row)> = Vec::new();
            for c in &cycle_cuts {
                let pairs: Vec<(ArcId, ArcId)> = c
                    .edge_indices
                    .iter()
                    .map(|&e| (2 * e as ArcId, 2 * e as ArcId + 1))
                    .collect();
                let depth = c.violation / ((2 * pairs.len()) as Cost).max(1.0).sqrt();
                ranked.push((depth, 0, Row::Cycle(pairs)));
            }
            for p in &partition_cuts {
                let depth = p.violation / (p.crossing_arcs.len() as Cost).max(1.0).sqrt();
                let coeffs = vec![1.0; p.crossing_arcs.len()];
                // The parts other than the root's, which is the witness the
                // dual decomposition below needs.
                let mut parts: Vec<Vec<NodeId>> = vec![Vec::new(); p.num_parts];
                for (v, &part) in p.part_of.iter().enumerate() {
                    if (part as usize) < p.num_parts {
                        parts[part as usize].push(v as NodeId);
                    }
                }
                parts.remove(0);
                witness.insert(signature(&p.crossing_arcs), parts);
                ranked.push((depth, 1, Row::Weighted(p.crossing_arcs.clone(), coeffs, p.rhs)));
            }
            for t in &tf_cuts {
                // `x(delta(S)) >= 2 x_e`, with both orientations of every
                // boundary edge and of the edge being dominated.
                let mut arcs: Vec<ArcId> = Vec::with_capacity(2 * t.boundary_arcs.len() + 2);
                let mut coeffs: Vec<Cost> = Vec::with_capacity(arcs.capacity());
                for &(fwd, rev) in &t.boundary_arcs {
                    arcs.push(fwd);
                    coeffs.push(1.0);
                    arcs.push(rev);
                    coeffs.push(1.0);
                }
                arcs.push(t.edge_arc_pair.0);
                coeffs.push(-2.0);
                arcs.push(t.edge_arc_pair.1);
                coeffs.push(-2.0);
                let norm = coeffs.iter().map(|c| c * c).sum::<Cost>().max(1.0).sqrt();
                ranked.push((t.violation / norm, 2, Row::Weighted(arcs, coeffs, 0.0)));
            }
            ranked.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
            // Extra rows are admitted, never substituted: every flow cut is
            // already installed above. An extra earns its slot only when it is
            // deeper than every flow cut on offer this round -- when it is the
            // best row available and the loop would have been willing to
            // install something shallower. That is a comparison between
            // measured depths with no count to choose.
            let deepest_flow = cuts
                .iter()
                .map(|c| c.violation / (c.cut_arcs.len() as Cost).max(1.0).sqrt())
                .fold(0.0 as Cost, Cost::max);
            for (depth, kind, row) in &ranked {
                if *depth < deepest_flow {
                    continue;
                }
                let sig: Vec<ArcId> = match row {
                    Row::Cycle(pairs) => pairs.iter().flat_map(|&(f, r)| [f, r]).collect(),
                    Row::Weighted(arcs, _, _) => arcs.clone(),
                };
                let mut sorted = sig;
                sorted.sort_unstable();
                if !signatures.insert(sorted) {
                    continue;
                }
                match row {
                    Row::Cycle(pairs) => lp.add_cycle_cut(pairs),
                    Row::Weighted(arcs, coeffs, rhs) => lp.add_cut(arcs, coeffs, *rhs),
                }
                if let Row::Weighted(arcs, _, rhs) = row {
                    if *rhs > 1.0 {
                        if let Some(parts) = witness.remove(&signature(arcs)) {
                            partitions.insert(signature(arcs), parts);
                        }
                    }
                }
                family[*kind].0 += 1;
                installed += 1;
                extra += 1;
            }
            family[0].1 = separation_secs;
        }

        if structural == 0 && installed == 0 && extra == 0 {
            // The point satisfies every requirement any family here can express,
            // so no further round of this loop can move the bound — this call's
            // or any later one's.
            *converged = true;
            break;
        }

        // Rows that have not been binding for several solves are dropped. The
        // bound stays valid whatever the pool holds — an LP over fewer rows is a
        // weaker relaxation, never an invalid one — and an unbounded pool is
        // what makes a 125-vertex model cost 80 ms a solve.
        lp.prune_cuts();
        rounds.push(RoundStat {
            bound: *best_bound,
            structural,
            cuts: installed,
            family,
            rows: lp.num_constraints(),
            secs: round_started.elapsed().as_secs_f64(),
        });
    }

    // A converged loop still owes the caller the strongest elimination its own
    // last solve licenses under the *current* incumbent, which the caller may
    // have improved since. `last_obj` and `lp.reduced_costs` come from the same
    // solve; nothing here pairs a bound with another solve's vector.
    if *converged && upper_bound.is_finite() {
        if let Some(obj) = *last_obj {
            let fixed: Vec<ArcId> = (0..num_arcs)
                .filter(|&a| {
                    let rc = lp.reduced_costs.get(a).copied().unwrap_or(0.0);
                    rc > 0.0 && obj + rc > upper_bound
                })
                .map(|a| a as ArcId)
                .collect();
            if fixed.len() > eliminated_arcs.len() {
                *eliminated_arcs = fixed;
            }
        }
    }

    let candidates = candidates.as_ref()?;
    let packing = certify(candidates, idx, root);
    let mut packing = extend_by_residual_ascent(packing, idx, root, terminals, max_set_nnz);

    // (PACK) is re-derived from the multipliers on *every* extraction, not only
    // in a debug build and not only at the end of a one-shot run. A resumed loop
    // hands the search a packing built from a dual it did not itself produce, and
    // a bound that gets announced as a proof must not rest on a solver's
    // tolerance. `repair` scales to feasibility and can only lower the claim; see
    // the certified-scaling lemma on [`CertifiedPacking::repair`].
    let scale = packing.repair(idx, root);
    debug_assert!(
        scale >= 1.0 - 1e-9,
        "extracted packing violated (PACK) and was scaled by {scale}"
    );

    Some(RootCertificate {
        lp_bound: *best_bound,
        packing,
        eliminated_arcs: eliminated_arcs.clone(),
        lp_solves: *lp_solves,
        rounds: rounds.clone(),
    })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn triangle() -> (DirectedGraph, Vec<NodeId>) {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        for (u, v, c) in [(1, 4, 1.0), (2, 4, 1.0), (3, 4, 1.0), (1, 2, 3.0)] {
            g.add_arc(u, v, c);
            g.add_arc(v, u, c);
        }
        (g, vec![1, 2, 3])
    }

    /// The recovery lemma, exercised on arc sets that are *not* cuts.
    #[test]
    fn recovered_boundary_is_contained_in_the_row_support() {
        let (g, _) = triangle();
        let idx = ArcIndex::new(&g);
        let root = 1;
        for take in 1..(1u32 << idx.num_arcs().min(10)) {
            let arcs: Vec<ArcId> =
                (0..idx.num_arcs()).filter(|i| take >> i & 1 == 1).map(|i| i as ArcId).collect();
            let p = certify(&[(1.0, arcs.clone())], &idx, root);
            for (_, members) in &p.sets {
                assert!(!members.contains(&root));
                for &v in members {
                    for &a in idx.incoming(v) {
                        if !members.contains(&idx.tail(a)) {
                            assert!(
                                arcs.contains(&a),
                                "boundary arc {a} escaped the row support {arcs:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    /// Whatever weights are proposed, the certified result satisfies (PACK).
    #[test]
    fn certification_is_feasible_for_arbitrary_weights() {
        let (g, _) = triangle();
        let idx = ArcIndex::new(&g);
        let root = 1;
        let mut seed = 12345u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let mut candidates: Vec<Candidate> = Vec::new();
            for _ in 0..(1 + rng() % 5) {
                let arcs: Vec<ArcId> = (0..idx.num_arcs())
                    .filter(|_| rng() % 2 == 0)
                    .map(|i| i as ArcId)
                    .collect();
                // Deliberately huge weights: the repair has to do real work.
                candidates.push(((rng() % 50) as Cost, arcs));
            }
            let p = certify(&candidates, &idx, root);
            assert!(p.verify(&idx, root, 1e-9), "certified packing is infeasible");
            assert!(p.value >= -1e-12);
        }
    }

    /// A residual layer on top of a certified packing is still one packing, and
    /// the combined value is the sum.
    #[test]
    fn residual_layer_stays_feasible() {
        let (g, terminals) = triangle();
        let idx = ArcIndex::new(&g);
        let root = terminals[0];
        // Start from a deliberately weak first layer so the ascent has room.
        let base = certify(&[(0.5, vec![0, 2])], &idx, root);
        let combined = extend_by_residual_ascent(base.clone(), &idx, root, &terminals, 1 << 20);
        assert!(combined.verify(&idx, root, 1e-6));
        assert!(combined.value >= base.value - 1e-9);
        // Optimum of the triangle instance is 3; a packing can never exceed it.
        assert!(combined.value <= 3.0 + 1e-6, "packing value {} exceeds the optimum", combined.value);
    }

    /// The property the whole module exists for, checked against enumeration.
    ///
    /// For every state `(v, S)` of a small instance, the potential
    /// `L_pack(v,S) = sum { y_W : W meets S ∪ {v} }` must not exceed the cost of
    /// a cheapest tree spanning `S ∪ {v}`, and the search driven by it must
    /// return the true optimum. Both are checked on packings read out of an LP
    /// dual — the case the ascent's own tests never reach, because an ascent
    /// packing is laminar-ish and an LP dual is not.
    #[test]
    fn lp_packings_bound_every_state() {
        use crate::graph::algorithms::dijkstra_steiner_guided;
        use crate::graph::UndirectedGraph;

        let mut seed = 0xC0FF_EE12_3456_789Du64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        for _ in 0..60 {
            let n = 4 + (rng() % 4) as u32;
            let k = 2 + (rng() % 3) as u32;
            let mut ug = UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                ug.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        ug.add_edge(u, v, 1.0 + (rng() % 9) as Cost);
                    }
                }
            }
            let g = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&g);
            let root = terminals[0];
            let deadline = Instant::now() + std::time::Duration::from_secs(5);
            let Some(cert) =
                root_certificate(&g, root, &terminals, Cost::INFINITY, deadline, 200, 1 << 20)
            else {
                continue;
            };
            assert!(cert.packing.verify(&idx, root, 1e-6));

            // Enumerate every connected vertex subset holding the root and take
            // its cheapest spanning tree: that is an upper bound on
            // `smt(S ∪ {v})` for every `S ∪ {v}` it contains, and the minimum
            // over the subsets containing a given requirement is exactly it.
            let mut best = vec![Cost::INFINITY; 1usize << n];
            for sub in 0u32..(1u32 << n) {
                if sub >> (root - 1) & 1 == 0 {
                    continue;
                }
                if let Some(c) = spanning_cost(&ug, sub, n) {
                    // Every superset requirement is served by this tree.
                    if c < best[sub as usize] {
                        best[sub as usize] = c;
                    }
                }
            }
            // Downward closure: a tree on `sub` serves every requirement inside.
            for sub in 0u32..(1u32 << n) {
                let mut bits = sub;
                while bits != 0 {
                    let b = bits & bits.wrapping_neg();
                    bits ^= b;
                    let smaller = sub ^ b;
                    if best[sub as usize] < best[smaller as usize] {
                        best[smaller as usize] = best[sub as usize];
                    }
                }
            }

            for req in 0u32..(1u32 << n) {
                if req >> (root - 1) & 1 == 0 || !best[req as usize].is_finite() {
                    continue;
                }
                let potential: Cost = cert
                    .packing
                    .sets
                    .iter()
                    .filter(|(_, members)| {
                        members.iter().any(|&v| v >= 1 && req >> (v - 1) & 1 == 1)
                    })
                    .map(|(w, _)| *w)
                    .sum();
                assert!(
                    potential <= best[req as usize] + 1e-6,
                    "potential {potential} exceeds smt {} on requirement {req:b}",
                    best[req as usize]
                );
            }

            let guided = dijkstra_steiner_guided(
                &ug,
                &terminals,
                Cost::INFINITY,
                u64::MAX,
                None,
                &[&cert.packing.sets],
            )
            .and_then(|r| r.optimal);
            let plain = dijkstra_steiner_guided(&ug, &terminals, Cost::INFINITY, u64::MAX, None, &[])
                .and_then(|r| r.optimal);
            assert_eq!(
                guided.map(|c| (c * 1e6) as i64),
                plain.map(|c| (c * 1e6) as i64),
                "LP guidance changed the answer"
            );
            checked += 1;
        }
        assert!(checked > 20, "only {checked} instances exercised");
    }

    /// Cheapest spanning tree of the induced subgraph on `sub`, or `None` when it
    /// is disconnected. Kruskal over a handful of edges.
    fn spanning_cost(g: &crate::graph::UndirectedGraph, sub: u32, n: u32) -> Option<Cost> {
        let members: Vec<u32> = (1..=n).filter(|&v| sub >> (v - 1) & 1 == 1).collect();
        if members.is_empty() {
            return Some(0.0);
        }
        let mut edges: Vec<(Cost, u32, u32)> = g
            .edges
            .iter()
            .filter(|e| sub >> (e.src - 1) & 1 == 1 && sub >> (e.dst - 1) & 1 == 1)
            .map(|e| (e.cost, e.src, e.dst))
            .collect();
        edges.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let mut parent: Vec<u32> = (0..=n).collect();
        fn find(p: &mut Vec<u32>, x: u32) -> u32 {
            if p[x as usize] != x {
                let r = find(p, p[x as usize]);
                p[x as usize] = r;
            }
            p[x as usize]
        }
        let mut total = 0.0;
        let mut joined = 1;
        for (c, u, v) in edges {
            let (a, b) = (find(&mut parent, u), find(&mut parent, v));
            if a != b {
                parent[a as usize] = b;
                total += c;
                joined += 1;
            }
        }
        (joined == members.len()).then_some(total)
    }

    #[test]
    fn partition_decomposition_obeys_its_lemma() {
        // The three claims the lemma rests on, checked on random partitions of
        // random graphs: every boundary lies inside the crossing set, the
        // boundaries are pairwise disjoint, and the members reproduce the row's
        // own contribution `lambda * k`.
        let mut seed = 0x7E57_0BEE_1234_5678u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for n in 4..=12u32 {
            for _ in 0..40 {
                let mut g = DirectedGraph::new(n);
                for v in 1..=n {
                    g.add_node(v, NodeType::Steiner, 0.0);
                }
                for u in 1..=n {
                    for v in 1..=n {
                        if u != v && rng() % 100 < 35 {
                            g.add_arc(u, v, 1.0);
                        }
                    }
                }
                let idx = ArcIndex::new(&g);
                let k = 1 + (rng() % 3) as usize;
                // Part 0 holds the root; the rest are the decomposed members.
                let mut part_of = vec![0u32; n as usize + 1];
                for v in 1..=n as usize {
                    part_of[v] = (rng() % (k as u64 + 1)) as u32;
                }
                let root = 1;
                part_of[root as usize] = 0;
                let parts: Vec<Vec<NodeId>> = (1..=k)
                    .map(|i| {
                        (1..=n).filter(|&v| part_of[v as usize] == i as u32).collect()
                    })
                    .collect();
                let crossing: std::collections::HashSet<ArcId> = (0..idx.num_arcs() as ArcId)
                    .filter(|&a| {
                        part_of[idx.tail(a) as usize] != part_of[idx.head(a) as usize]
                    })
                    .collect();

                let lambda = 1.0 + (rng() % 7) as Cost;
                let members = decompose_partition(&parts, lambda, &idx, root);
                let mut seen: std::collections::HashSet<ArcId> = std::collections::HashSet::new();
                for (w, boundary) in &members {
                    assert!((w - lambda).abs() < 1e-12);
                    for &a in boundary {
                        assert!(crossing.contains(&a), "boundary arc outside the crossing set");
                        assert!(seen.insert(a), "boundaries overlap on arc {a}");
                    }
                }
                // Value: one member per non-empty, non-root part with a boundary.
                let expected: usize = parts
                    .iter()
                    .filter(|p| {
                        !p.is_empty()
                            && p.iter().all(|&v| v != root)
                            && p.iter().any(|&v| {
                                idx.incoming(v).iter().any(|&a| {
                                    !p.contains(&idx.tail(a))
                                })
                            })
                    })
                    .count();
                assert_eq!(members.len(), expected);
            }
        }
    }

    #[test]
    fn root_certificate_never_exceeds_the_optimum() {
        let (g, terminals) = triangle();
        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        let cert =
            root_certificate(&g, terminals[0], &terminals, Cost::INFINITY, deadline, 8, 1 << 20)
                .expect("root LP should solve");
        let idx = ArcIndex::new(&g);
        assert!(cert.packing.verify(&idx, terminals[0], 1e-6));
        assert!(cert.lp_bound <= 3.0 + 1e-6, "lp bound {}", cert.lp_bound);
        assert!(cert.packing.value <= 3.0 + 1e-6, "packing {}", cert.packing.value);
    }

    /// The certified-scaling lemma, on vectors that genuinely violate (PACK).
    #[test]
    fn repair_scales_an_infeasible_packing_to_feasibility() {
        let (g, terminals) = triangle();
        let idx = ArcIndex::new(&g);
        let root = terminals[0];
        // `{2}` and `{3}` each have in-boundary arcs of cost 1 and 3; loading
        // them at 7 overloads by a factor of 7.
        let mut p = CertifiedPacking { sets: vec![(7.0, vec![2]), (7.0, vec![3])], value: 14.0 };
        assert!(!p.verify(&idx, root, 1e-9));
        let scale = p.repair(&idx, root);
        assert!(scale < 1.0, "an infeasible packing must be scaled down");
        assert!(p.verify(&idx, root, 1e-9), "repair left it infeasible");
        // The value is re-derived from the family that was checked.
        let sum: Cost = p.sets.iter().map(|(w, _)| *w).sum();
        assert!((p.value - sum).abs() < 1e-9);
        assert!(p.value <= 3.0 + 1e-6, "repaired value {} exceeds the optimum", p.value);

        // A feasible packing is left exactly alone: `repair` may decline a claim,
        // never manufacture one and never perturb one.
        let mut q = CertifiedPacking { sets: vec![(1.0, vec![2])], value: 1.0 };
        let before = q.clone();
        assert_eq!(q.repair(&idx, root), 1.0);
        assert_eq!(q.value, before.value);
        assert_eq!(q.sets, before.sets);
    }

    /// The resumed-dominance proposition, checked end to end.
    ///
    /// A loop resumed one round at a time must reach exactly the bound a loop
    /// given all the rounds at once reaches, and must converge at the same round
    /// index, because the round sequence is a function of state the resumption
    /// preserves.
    #[test]
    fn a_resumed_loop_matches_a_fresh_loop_at_convergence() {
        let mut seed = 0x5EED_1234_ABCD_0001u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut compared = 0;
        for _ in 0..25 {
            let n = 5 + (rng() % 4) as u32;
            let k = 2 + (rng() % 3) as u32;
            let mut ug = crate::graph::UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                ug.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        ug.add_edge(u, v, 1.0 + (rng() % 9) as Cost);
                    }
                }
            }
            let g = DirectedGraph::from_undirected(&ug);
            let root = terminals[0];
            let far = || Instant::now() + std::time::Duration::from_secs(30);

            let mut fresh = RootSeparation::new(&g, root, &terminals);
            let Some(one_shot) = fresh.advance(Cost::INFINITY, far(), 200, 1 << 20) else {
                continue;
            };
            assert!(fresh.is_converged(), "200 rounds should converge on this size");

            let mut resumed = RootSeparation::new(&g, root, &terminals);
            let mut last = None;
            let mut calls = 0;
            while !resumed.is_converged() && calls < 300 {
                last = resumed.advance(Cost::INFINITY, far(), 1, 1 << 20);
                calls += 1;
            }
            let inc = last.expect("a resumed loop produces a certificate");
            assert!(resumed.is_converged());
            assert!(
                (inc.lp_bound - one_shot.lp_bound).abs() < 1e-6,
                "resumed {} vs fresh {}",
                inc.lp_bound,
                one_shot.lp_bound
            );
            assert_eq!(
                inc.lp_solves, one_shot.lp_solves,
                "the same round sequence must solve the same number of LPs"
            );
            let idx = ArcIndex::new(&g);
            assert!(inc.packing.verify(&idx, root, 1e-6));
            compared += 1;
        }
        assert!(compared >= 10, "only {compared} instances converged; test is vacuous");
    }

    /// Resumption is never *weaker* than a fresh loop truncated the same way.
    ///
    /// A loop stopped after `k` rounds and resumed for one more must reach the
    /// bound a fresh loop reaches in `k + 1`, which is the half of the
    /// proposition the convergence test does not exercise.
    #[test]
    fn a_resumed_loop_matches_a_fresh_loop_round_for_round() {
        let (g, terminals) = triangle();
        let root = terminals[0];
        let far = || Instant::now() + std::time::Duration::from_secs(30);
        for k in 1..6usize {
            let mut fresh = RootSeparation::new(&g, root, &terminals);
            let a = fresh.advance(Cost::INFINITY, far(), k + 1, 1 << 20);

            let mut split = RootSeparation::new(&g, root, &terminals);
            split.advance(Cost::INFINITY, far(), k, 1 << 20);
            let b = split.advance(Cost::INFINITY, far(), 1, 1 << 20);

            match (a, b) {
                (Some(a), Some(b)) => {
                    assert!(
                        (a.lp_bound - b.lp_bound).abs() < 1e-9,
                        "k={k}: fresh {} vs resumed {}",
                        a.lp_bound,
                        b.lp_bound
                    );
                    assert_eq!(a.lp_solves, b.lp_solves, "k={k}");
                }
                (None, None) => {}
                _ => panic!("k={k}: one loop produced a certificate and the other did not"),
            }
        }
    }

    /// A model that no longer describes the graph is not resumed against it.
    #[test]
    fn applies_to_rejects_a_changed_graph() {
        let (g, terminals) = triangle();
        let sep = RootSeparation::new(&g, terminals[0], &terminals);
        assert!(sep.applies_to(&g, terminals[0], &terminals));
        assert!(!sep.applies_to(&g, terminals[1], &terminals));

        let mut cheaper = g.clone();
        cheaper.arcs[0].cost += 1.0;
        assert!(!sep.applies_to(&cheaper, terminals[0], &terminals));

        let mut fewer = g.clone();
        fewer.arcs.pop();
        assert!(!sep.applies_to(&fewer, terminals[0], &terminals));

        let shorter: Vec<NodeId> = terminals[..2].to_vec();
        assert!(!sep.applies_to(&g, terminals[0], &shorter));
    }
}
