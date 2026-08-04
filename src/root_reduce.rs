//! Ascend-and-prune: alternate dual ascent, primal heuristics, and reduced-cost
//! elimination until the instance stops shrinking or optimality is proved.
//!
//! Each round does three things:
//!
//! 1. get an upper bound from the shortest-path heuristic, guided by the reduced
//!    costs of the previous ascent;
//! 2. run dual ascent from several roots for a lower bound plus reduced costs;
//! 3. delete everything the reduced costs prove cannot appear in a solution
//!    cheaper than the incumbent, then re-run the classical reductions on the
//!    smaller graph.
//!
//! Rounds compound: elimination makes the next ascent tighter, which eliminates
//! more. On most SteinLib B/C instances this closes the problem outright and the
//! branch-and-cut engine is never entered.
//!
//! # Why root-specific arc fixings may not be unioned
//!
//! Reduced-cost fixing from root `r` proves: *every `r`-arborescence using arc `a`
//! costs at least `LB + slack(a)`*. That is a statement about one orientation.
//! An undirected tree `T` is oriented differently by different roots, so an arc
//! excluded by root `r1` may well be the orientation `r2` needs.
//!
//! Unioning arc fixings across roots is therefore unsound: root `r1` can exclude
//! `(u,v)` and root `r2` exclude `(v,u)` while a cheap undirected tree uses edge
//! `{u,v}` — its `r1`-orientation is `(v,u)` and its `r2`-orientation is `(u,v)`,
//! each surviving its own root's fixing, yet the union deletes the edge.
//!
//! What *is* safe is to derive, separately for each root, the purely undirected
//! conclusion "no tree cheaper than the incumbent uses edge `{u,v}`" — which needs
//! **both** orientations excluded **by that one root** — and union those. Each is
//! a valid statement about undirected trees on its own, so their union is too.
//! [`round`] does exactly that, and the arc-level mask handed to branch-and-cut
//! comes from a single root.

use std::collections::HashMap;
use std::time::Instant;

use crate::graph::algorithms::{
    dual_ascent_masked, reduced_cost_distances, reduced_cost_fixings, ArcIndex, DualAscentResult,
};
use crate::graph::{costs_are_integral, tighten_dual, Cost, DirectedGraph, NodeId, NodeType, UndirectedGraph};
use crate::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use crate::heuristics::key_vertex::KeyVertexWorkspace;
use crate::heuristics::sph::{shortest_path_heuristic, SphResult, SphWorkspace};
use crate::heuristics::{iterated_local_search, IlsStats, IlsWorkspace};
use crate::preprocessing::preprocess_bounded;
use crate::graph::SteinerInstance;

/// Widest decomposition the exact recombination will run its dynamic programme
/// over.
///
/// This is a work bound, not a quality dial: the DP's table is
/// `Bell(width + 2)` per bag, so a width of eleven is already a hundred
/// thousand signatures on a bag and every unit above it costs a factor of five.
/// Measured on the reduced PACE instances the unions that matter decompose at
/// three to eight, so nothing this cap refuses was ever going to finish.
const EXACT_RECOMB_WIDTH: usize = 11;

/// Floor on the time the exact steps may be predicted to take, in seconds.
///
/// The allowance is otherwise self-scaling: an exact step may cost no more than
/// the iterated local search that produced the trees it works on, which needs no
/// clock fraction and adapts to the instance by construction. On an instance the
/// construction solved outright that measures as zero, and this floor is what
/// still lets a decomposition that costs microseconds run.
const EXACT_MIN_SECS: f64 = 0.02;

/// Pool members the exact recombination may consider as parents.
///
/// # This is a cap on *probes*, and lifting it was measured as a loss
///
/// [`crate::heuristics::recombine_pool`] chooses how many parents to admit by
/// binary search on the measured width of the ground set they span, so the
/// constant looks like the fixed prefix that criterion exists to replace, and
/// the pool it is applied to is much larger than the constant: on PACE
/// instance196 the local search leaves 106 distinct optima and twelve of them
/// span 84 vertices at width five against a cap of eleven.
///
/// Lifting it entirely — letting the width search see the whole pool — was
/// implemented and A/B'd, and it is **worse**. It grows the ground set on some
/// instances (instance171: 51 -> 55 vertices; instance173: 59 -> 71) and
/// improves the incumbent on none of 171, 172, 173, 195, 196, while the extra
/// `O(log)` decompositions cost four Track 1 proofs (182, 188, 192, 193) and one
/// on Track 2. The binary search's probes are not free and the ones it adds are
/// the expensive end of the range.
///
/// So the twelve stays, and what it bounds is stated honestly: it is a budget on
/// how many decompositions the search may run, not a belief about how many
/// parents are useful. The measurement that would change it is a probe schedule
/// whose cost does not grow with the prefix, not a larger constant.
const EXACT_RECOMB_PARENTS: usize = 12;

/// Outcome of the tightening loop.
#[derive(Clone)]
pub struct Reduced {
    pub graph: UndirectedGraph,
    pub terminals: Vec<NodeId>,
    pub root: NodeId,
    /// Valid lower bound on the optimum of the instance handed in.
    pub lower_bound: Cost,
    /// Cost of the best solution found, or infinity.
    pub upper_bound: Cost,
    /// Arcs of the best solution, in the *final* reduced graph's arc numbering.
    /// `None` when the incumbent predates the last shrink.
    pub incumbent_arcs: Option<Vec<u32>>,
    /// The tree `upper_bound` is the cost of, carried with the graph it is a
    /// tree *of*.
    ///
    /// # Why an edge list of the current graph is not enough
    ///
    /// `upper_bound` is a number the loop carries across shrinks with only the
    /// contraction offset subtracted. That is sound as a *bound* — the reduction
    /// preserves an optimum, so the carried number still dominates the reduced
    /// optimum — and it is not a *witness*: after a shrink there may be no tree
    /// of the current graph attaining it. §61 is the record of two attempts to
    /// recover the evidence after the fact from `incumbent_arcs`, and of why
    /// both were wrong: an arc index survives a renumbering while naming a
    /// different edge, so a cost re-derived from it is a fiction. The lesson
    /// stated there is exact — *a witness is only a witness while the numbering
    /// it is stated in is still the graph's* — and the repair it implies is to
    /// **keep the numbering**, not to guess at it afterwards.
    ///
    /// So the witness carries its own graph. Re-basing onto the current graph is
    /// attempted at every shrink and taken when it is exact (see
    /// [`Witness::rebase_onto`]), which keeps the stored graph small; when it is
    /// not exact the snapshot stands, and the snapshot cannot fail.
    ///
    /// See [`Reduced::verify_witness`] for the invariant that makes it a
    /// statement about `upper_bound` and not merely about itself.
    pub witness: Option<Witness>,
    /// Certificate backing `lower_bound`, from the best root.
    pub certificate: Option<DualAscentResult>,
    /// Cost of the edges contracted into the objective while tightening. Every
    /// bound in this struct is stated for `graph`; the corresponding bound for
    /// the instance handed to [`tighten`] is `offset` plus that value.
    pub offset: Cost,
    pub rounds: u32,
    /// Whether the loop stopped because it had nothing left to do.
    ///
    /// `true` means the last round killed no vertex and no edge, or optimality
    /// was proved, or the instance became trivial — in every case a *fixpoint*
    /// of the reduction operator was reached. `false` means the loop was cut
    /// short by its deadline or its round cap and would have gone on.
    ///
    /// The distinction is what lets a later pass skip re-deriving a fixpoint it
    /// already has. Every round is a deterministic function of the graph, the
    /// terminals, the configuration and the two bounds, so a converged run
    /// re-executed on its own output — with an upper bound no better than the
    /// one it finished with — kills nothing again. A run cut off by the clock
    /// carries no such guarantee: given more time it does more.
    pub converged: bool,
}

/// A tree, and the graph it is a tree of.
#[derive(Clone)]
pub struct Witness {
    /// A graph the tightening passed through — not necessarily the final one.
    pub graph: UndirectedGraph,
    pub terminals: Vec<NodeId>,
    /// Edge ids of [`Witness::graph`].
    pub edges: Vec<u32>,
    /// Cost recomputed from [`Witness::graph`] when the witness was taken.
    pub cost: Cost,
    /// The tightening's accumulated contraction offset at that moment.
    pub offset: Cost,
}

impl Witness {
    /// Recompute the cost from the stored graph and check the edges connect the
    /// stored terminals. `None` when they do not.
    ///
    /// Everything is read back out of [`Witness::graph`]: the edge ids are
    /// bounds-checked against it, the costs are its own, and connectivity is
    /// recomputed by union-find over the endpoints *it* reports. Nothing is
    /// taken on trust from the numbering the tree was found in, because keeping
    /// that numbering is the entire mechanism.
    pub fn verify(&self) -> Option<Cost> {
        if self.terminals.len() < 2 {
            return self.edges.is_empty().then_some(0.0);
        }
        let mut cost = 0.0;
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
        let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for &e in &self.edges {
            if !seen.insert(e) {
                return None;
            }
            let edge = self.graph.edges.get(e as usize)?;
            cost += edge.cost;
            uf.entry(edge.src).or_insert(edge.src);
            uf.entry(edge.dst).or_insert(edge.dst);
            let (a, b) = (find(&mut uf, edge.src), find(&mut uf, edge.dst));
            uf.insert(a, b);
        }
        let root = *self.terminals.first()?;
        uf.contains_key(&root).then_some(())?;
        let rr = find(&mut uf, root);
        for &t in &self.terminals {
            if !uf.contains_key(&t) || find(&mut uf, t) != rr {
                return None;
            }
        }
        Some(cost)
    }

    /// Re-state the witness over `new`, given a node map. Returns `None` unless
    /// every edge has an image of the same cost on the mapped endpoints.
    ///
    /// Matching on *cost as well as endpoints* is what makes this safe under
    /// parallel edges: two edges may share endpoints, and picking one of a
    /// different cost would change the witness's value while leaving it
    /// connected. That is the exact shape of §61's second failure.
    fn rebase_onto(
        &self,
        new: &UndirectedGraph,
        new_terminals: &[NodeId],
        map: &dyn Fn(NodeId) -> Option<NodeId>,
    ) -> Option<Witness> {
        let mut index: HashMap<(NodeId, NodeId), Vec<(u32, Cost)>> = HashMap::new();
        for e in &new.edges {
            let key = if e.src <= e.dst { (e.src, e.dst) } else { (e.dst, e.src) };
            index.entry(key).or_default().push((e.id, e.cost));
        }
        let mut taken: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut out = Vec::with_capacity(self.edges.len());
        let mut cost = 0.0;
        for &e in &self.edges {
            let edge = self.graph.edges.get(e as usize)?;
            let (u, v) = (map(edge.src)?, map(edge.dst)?);
            if u == v {
                // Both endpoints were merged: the edge is inside a contraction
                // and its cost has moved to the offset. Not representable here.
                return None;
            }
            let key = if u <= v { (u, v) } else { (v, u) };
            let pick = index
                .get(&key)?
                .iter()
                .find(|(id, c)| (c - edge.cost).abs() < 1e-9 && !taken.contains(id))?;
            taken.insert(pick.0);
            out.push(pick.0);
            cost += pick.1;
        }
        Some(Witness {
            graph: new.clone(),
            terminals: new_terminals.to_vec(),
            edges: out,
            cost,
            offset: self.offset,
        })
    }
}

impl Reduced {
    pub fn proved_optimal(&self, tolerance: Cost) -> bool {
        self.upper_bound.is_finite() && self.lower_bound >= self.upper_bound - tolerance
    }

    /// The value the witness proves is attainable, **on the scale of the graph
    /// handed to [`tighten`]** — that is, `cost + offset`.
    ///
    /// # The invariant that makes this a statement about `upper_bound`
    ///
    /// > **Proposition (witness invariant).** Let `(G_j, W_j, c_j, o_j)` be the
    /// > graph, edge set, cost and accumulated offset recorded at the moment the
    /// > incumbent was last improved. Then at every later point of the loop
    /// >
    /// > ```text
    /// > upper_bound + offset = c_j + o_j,
    /// > ```
    /// >
    /// > and `W_j` is a tree of `G_j` spanning its terminals, of cost `c_j`.
    ///
    /// *Proof.* At the improvement `upper_bound := c_j` and `offset = o_j`, so
    /// the identity holds there. Only three later statements touch either side.
    /// `offset += rg.offset` together with `upper_bound -= rg.offset` preserves
    /// the sum. A further improvement re-establishes the snapshot and with it the
    /// identity. `lower_bound := upper_bound` on a proof of optimality touches
    /// neither. A re-basing replaces the snapshot only when the new `c + o`
    /// equals the old, by construction. ∎
    ///
    /// *Corollary.* `upper_bound + offset` is the cost of a tree of `G_j`, and
    /// `G_j` is reachable from the graph handed to [`tighten`] by contractions
    /// charging exactly `o_j`, so by the contraction lemma
    /// ([`crate::preprocessing::ReducibleGraph::contract_edge`]) there is a tree
    /// of *that* graph of cost `c_j + o_j = upper_bound + offset`. A report of
    /// `upper_bound + offset` therefore rests on an exhibited object.
    ///
    /// Returns `None` when there is no witness or it fails to verify — in which
    /// case `upper_bound` is a number with nothing behind it, and the caller
    /// must not report it as achieved.
    pub fn verify_witness(&self) -> Option<Cost> {
        let w = self.witness.as_ref()?;
        let c = w.verify()?;
        ((c - w.cost).abs() < 1e-6).then_some(c + w.offset)
    }

    /// The same reduction, restated for its **own** graph.
    ///
    /// # The double charge this removes
    ///
    /// A `Reduced` is stated for the graph [`tighten`] was *handed*: `offset` is
    /// the cost contracted on the way to `graph`, and every bound in the struct
    /// is `graph`-scale. A caller that carries `graph` forward and hands it to a
    /// later pass has already added `offset` to its own running total — the graph
    /// it is now handing in *is* `graph`, and the offset from a graph to itself
    /// is zero. Reusing the struct unchanged therefore charges `offset` twice:
    /// the pass reports `primal + offset` and the caller adds its accumulated
    /// `offset` on top.
    ///
    /// The consequence is not merely a loose number. Both bounds are inflated by
    /// the same amount, the caller's merge keeps the *smaller* primal — so the
    /// primal stays right — and then clamps the dual to it, which can turn an
    /// inflated dual into a proof of optimality that was never made. It is
    /// latent rather than live on the current benchmark, where `tighten`'s own
    /// offset measures zero on every PACE instance sampled, because the classical
    /// preprocessing has already done every contraction available before
    /// `tighten` runs. Latent is not a reason to leave it.
    ///
    /// > **Proposition.** `as_identity` preserves both invariants of the struct.
    /// >
    /// > *Proof.* (i) Every bound is stated for `graph`, and no bound is touched.
    /// > (ii) The witness invariant is `upper_bound + offset == w.cost +
    /// > w.offset`; subtracting the same `offset` from the left side's `offset`
    /// > and the right side's `w.offset` preserves the equation. Hence
    /// > `verify_witness` and `upper_bound_is_witnessed` answer exactly as
    /// > before. ∎
    ///
    /// `witness.offset` may become negative, which is arithmetically fine and
    /// semantically honest: it records how much of the accumulated contraction
    /// had *already* been charged when the witness was taken, now measured from a
    /// later origin.
    pub fn as_identity(&self) -> Reduced {
        let shift = self.offset;
        let mut out = self.clone();
        out.offset = 0.0;
        if let Some(w) = out.witness.as_mut() {
            w.offset -= shift;
        }
        out
    }

    /// Whether `upper_bound + offset` is exactly what the witness attains.
    pub fn upper_bound_is_witnessed(&self) -> bool {
        self.verify_witness()
            .is_some_and(|v| (v - (self.upper_bound + self.offset)).abs() < 1e-6)
    }
}

pub struct ReduceConfig {
    /// Maximum roots to run dual ascent from per round.
    pub roots_per_round: usize,
    /// Starting vertices tried by the shortest-path heuristic per round.
    pub heuristic_starts: usize,
    /// Maximum tightening rounds.
    pub max_rounds: u32,
    /// Perturb-and-merge iterations per round. Bounded by `deadline` as well.
    pub ils_iterations: u32,
    /// Cost of a solution already known, used as the elimination cutoff from the
    /// first round. Feeding back an incumbent found later by branch-and-cut lets
    /// the reduced costs eliminate far more than the heuristic's own bound would.
    pub initial_upper_bound: Cost,
    /// A tree attaining `initial_upper_bound`, if the caller has one.
    ///
    /// Required to satisfy `cost + offset == initial_upper_bound`, stated on the
    /// scale of the graph handed to [`tighten`]. Supplying `None` says the bound
    /// is unwitnessed, and the loop propagates that honestly rather than
    /// inventing evidence for it.
    pub initial_witness: Option<Witness>,
    /// A lower bound already proved for the graph handed to [`tighten`].
    ///
    /// # Why a pass may not re-derive one it was given
    ///
    /// Elimination power is exactly `UB - LB`, and the loop's own `LB` is a dual
    /// ascent, which on near-uniform costs saturates almost everything and is
    /// degenerate. On PACE instance083 the ascent reaches 3,100,512 while the
    /// root cut loop proves 3,100,519 against an incumbent of 3,100,541: the
    /// gap the fixing runs at is 29 units or 22 depending only on which of the
    /// two numbers the round starts from, and the second was computed and thrown
    /// away — every pass restarted at zero and re-derived the weaker one.
    ///
    /// This is a bound only. It never enters `reduced_cost_fixings`, which needs
    /// a bound and *its own* reduced costs; that pairing is what
    /// [`ReduceConfig::initial_dual`] carries.
    pub initial_lower_bound: Cost,
    /// A certified dual of the cut relaxation for the graph handed to
    /// [`tighten`], with its arc prices.
    ///
    /// Used as one more root in the elimination, under the same union rule as
    /// every other root: the undirected conclusion only. See
    /// [`crate::model::ArcDual`] for the pricing proposition, and this module's
    /// header for why the arc-level fixings of two roots may not be unioned.
    ///
    /// It is stated in the arc numbering of `DirectedGraph::from_undirected` on
    /// the graph handed in, and is used only while that graph is unchanged —
    /// the first round. Afterwards the eliminations have renumbered everything
    /// and the vector no longer names the arcs it was computed for.
    pub initial_dual: Option<crate::model::ArcDual>,
    pub deadline: Option<Instant>,
    pub verbose: bool,
}

impl Default for ReduceConfig {
    fn default() -> Self {
        Self {
            roots_per_round: 4,
            heuristic_starts: 64,
            max_rounds: 8,
            ils_iterations: 400,
            initial_upper_bound: Cost::INFINITY,
            initial_witness: None,
            initial_lower_bound: 0.0,
            initial_dual: None,
            deadline: None,
            verbose: false,
        }
    }
}

/// Pick roots spread through the terminal list. Dual ascent is root-dependent in
/// strength (though not in validity), so sampling beats always using the first.
fn root_candidates(terminals: &[NodeId], want: usize) -> Vec<NodeId> {
    if terminals.is_empty() {
        return Vec::new();
    }
    let want = want.min(terminals.len());
    (0..want).map(|i| terminals[i * terminals.len() / want]).collect()
}

/// Starting vertices for the heuristic: a spread of terminals.
fn heuristic_starts(terminals: &[NodeId], want: usize) -> Vec<NodeId> {
    root_candidates(terminals, want)
}

pub fn tighten(
    graph: UndirectedGraph,
    terminals: Vec<NodeId>,
    config: &ReduceConfig,
) -> Reduced {
    let mut graph = graph;
    let mut terminals = terminals;
    // A bound the caller has already proved for this graph. A pass that inherits
    // one must not re-derive a weaker one; see [`ReduceConfig::initial_lower_bound`].
    let mut lower_bound: Cost = config.initial_lower_bound.max(0.0);
    let mut upper_bound = config.initial_upper_bound;
    let mut certificate: Option<DualAscentResult> = None;
    let mut incumbent_arcs: Option<Vec<u32>> = None;
    // The tree `upper_bound` is the cost of, with the graph it lives in. Starts
    // as whatever the caller could exhibit for `initial_upper_bound`; a caller
    // that supplies a bound without a tree is telling this loop that the bound
    // is unwitnessed, and the loop propagates that rather than inventing one.
    let mut witness: Option<Witness> = config.initial_witness.clone();
    let mut offset: Cost = 0.0;
    let mut rounds = 0;
    let mut converged = false;

    let mut root = *terminals.first().unwrap_or(&1);

    for r in 0..config.max_rounds {
        rounds = r + 1;
        if let Some(d) = config.deadline {
            if Instant::now() >= d {
                break;
            }
        }
        if terminals.len() < 2 {
            converged = true;
            upper_bound = upper_bound.min(0.0);
            lower_bound = 0.0;
            incumbent_arcs = Some(Vec::new());
            // Fewer than two terminals: the empty tree spans them. It witnesses
            // the bound only when it *is* the bound — that is, when the `min`
            // above actually took zero.
            //
            // PACE Track 1's instance080 is why this distinction is written out
            // rather than assumed. There the loop reaches a one-vertex graph with
            // `upper_bound = -3` and `offset = 1410`: the incumbent was found in
            // round one at 1407, the eliminations then removed the trees
            // attaining it and the contractions charged 1410, so the *carried*
            // arithmetic is right — `-3 + 1410 = 1407`, the cost of a tree of the
            // round-one graph — while the final graph attains only 1574. The
            // empty tree here costs 0 and witnesses 1410, which is a **different
            // and worse** value than the bound. Installing it produced exactly
            // §61's version-two answer of 1574 against a reference of 1571.
            //
            // So the snapshot from round one stands, and it is the snapshot that
            // is right: `upper_bound + offset` is the cost of a tree, of *that*
            // graph, and the contraction lemma lifts it to this one.
            if upper_bound >= -1e-9 {
                upper_bound = 0.0;
                witness = Some(Witness {
                    graph: graph.clone(),
                    terminals: terminals.clone(),
                    edges: Vec::new(),
                    cost: 0.0,
                    offset,
                });
            }
            break;
        }

        // The supplied dual names the arcs of the graph handed in, so it applies
        // to the first round and to no later one: by the second round the
        // eliminations have deleted and renumbered, and a vector indexed by the
        // old arc ids would price the wrong arcs. `applies` is an equality on the
        // arc count *and* on the round index, not a heuristic.
        let supplied_dual = config
            .initial_dual
            .as_ref()
            .filter(|d| r == 0 && d.reduced.len() == 2 * graph.edges.len());
        let outcome = round(&graph, &terminals, config, upper_bound, lower_bound, supplied_dual);

        // With integral costs every tree costs an integer, so a fractional dual
        // bound can be lifted to the next one.
        let integral = costs_are_integral(graph.edges.iter().map(|e| e.cost));
        lower_bound = lower_bound.max(tighten_dual(outcome.lower_bound, integral));
        if outcome.upper_bound < upper_bound {
            upper_bound = outcome.upper_bound;
            incumbent_arcs = outcome.incumbent_arcs;
        }
        // A tree of this graph attaining `upper_bound` resets the snapshot: the
        // round found it *here*, so the numbering it is stated in is the
        // graph's. Taken on ties as well as improvements, and only when it
        // actually attains the bound.
        //
        // The clone is bounded by `max_rounds` over a graph the tightening has
        // already reduced, and it is what makes the guarantee unconditional. A
        // witness that cannot fail is worth a few copies of a graph that no
        // longer has to be guessed at.
        if let Some(edges) = outcome.incumbent_edges {
            let cost: Cost = edges
                .iter()
                .filter_map(|&e| graph.edges.get(e as usize))
                .map(|e| e.cost)
                .sum();
            if cost <= upper_bound + 1e-9 {
                upper_bound = upper_bound.min(cost);
                witness = Some(Witness {
                    graph: graph.clone(),
                    terminals: terminals.clone(),
                    edges,
                    cost,
                    offset,
                });
            }
        }
        if outcome.certificate.is_some() {
            certificate = outcome.certificate;
            root = outcome.root;
        }

        if config.verbose {
            eprintln!(
                "[reduce] round {rounds}: |V|={} |E|={} LB={:.1} UB={:.1} kill {}n/{}e                  | ils {} iters, {} gains, {:.1} -> {:.1}",
                graph.num_nodes,
                graph.edges.len(),
                lower_bound,
                upper_bound,
                outcome.dead_nodes.len(),
                outcome.dead_edges.len(),
                outcome.ils.iterations,
                outcome.ils.improvements,
                outcome.ils.seed_cost,
                outcome.ils.final_cost,
            );
        }

        // Optimality proved: everything better than the incumbent is excluded.
        if upper_bound.is_finite() && lower_bound >= upper_bound - 1e-6 {
            lower_bound = upper_bound;
            converged = true;
            break;
        }

        if outcome.dead_nodes.is_empty() && outcome.dead_edges.is_empty() {
            converged = true;
            break;
        }

        // Shrink, then re-run the classical reductions on the smaller graph.
        let Some((g2, t2, shrink_map)) =
            shrink(&graph, &terminals, &outcome.dead_nodes, &outcome.dead_edges)
        else {
            break;
        };
        // Follow the witness across the shrink, so the snapshot it carries stays
        // the *smallest* graph it is a tree of. `shrink_map[v] == 0` means `v`
        // did not survive, and the elimination is entitled to remove a vertex the
        // incumbent used — it only promises to keep the trees *cheaper* than the
        // incumbent, and the incumbent is not cheaper than itself. So a failure
        // here is expected rather than anomalous, and costs nothing: the previous
        // snapshot stands.
        let witness_in_g2 = witness.as_ref().and_then(|w| {
            w.rebase_onto(&g2, &t2, &|v| {
                let m = *shrink_map.get(v as usize)?;
                (m != 0).then_some(m)
            })
        });
        let instance = as_instance(&g2, &t2);
        // The incumbent is a tree of `g2` of cost `upper_bound` unless an earlier
        // elimination already removed it, in which case the loop is already
        // running under "every tree cheaper than the incumbent survives" and the
        // region bounds preserve exactly that.
        let (rg, _) = preprocess_bounded(&instance, &g2, config.deadline, upper_bound);
        let (ri, ru) = rg.to_instance();
        if ri.terminals.is_empty() {
            break;
        }
        // Contractions moved `rg.offset` out of the graph and into the
        // objective. Both bounds are stated for the graph, so both shift down.
        if rg.offset > 0.0 {
            offset += rg.offset;
            lower_bound = (lower_bound - rg.offset).max(0.0);
            upper_bound -= rg.offset;
        }
        // And across the classical reductions' own renumbering. A contraction
        // merges two vertices, so an edge of the witness between them has no
        // image; `rebase_onto` refuses rather than dropping it, because dropping
        // it would silently change the witness's cost — which is the whole thing
        // being protected.
        //
        // The replacement is taken **only when it preserves `cost + offset`**,
        // which is the invariant [`Reduced::verify_witness`] rests on. A tree
        // that survives a contraction it does not use keeps its cost while the
        // offset grows, so its sum rises: it is a *worse* witness than the
        // snapshot, and taking it would break the identity with `upper_bound`.
        let renumber = rg.node_renumbering();
        if let Some(rebased) =
            witness_in_g2.and_then(|w| w.rebase_onto(&ru, &ri.terminals, &|v| renumber.get(&v).copied()))
        {
            let old_sum = witness.as_ref().map(|w| w.cost + w.offset);
            let new_sum = rebased.cost + offset;
            if old_sum.is_some_and(|s| (s - new_sum).abs() < 1e-6) {
                witness = Some(Witness { offset, ..rebased });
            }
        }
        graph = ru;
        terminals = ri.terminals;
        // Node ids changed, so an incumbent recorded in the old numbering is
        // no longer meaningful as an arc list; its cost stays valid.
        incumbent_arcs = None;
        certificate = None;
        if !terminals.contains(&root) {
            root = terminals[0];
        }
    }

    if !terminals.contains(&root) {
        root = *terminals.first().unwrap_or(&1);
    }

    // The invariant, checked rather than asserted in prose. A build that
    // violates it is a build whose reports rest on nothing, so it is worth a
    // debug assertion at every exit.
    debug_assert!(
        witness.as_ref().is_none_or(|w| {
            !upper_bound.is_finite() || ((w.cost + w.offset) - (upper_bound + offset)).abs() < 1e-6
        }),
        "witness invariant broken"
    );

    Reduced {
        graph,
        terminals,
        root,
        lower_bound,
        upper_bound,
        incumbent_arcs,
        witness,
        certificate,
        offset,
        rounds,
        converged,
    }
}

struct RoundOutcome {
    lower_bound: Cost,
    upper_bound: Cost,
    incumbent_arcs: Option<Vec<u32>>,
    /// The same tree as edges of the graph the round ran on.
    incumbent_edges: Option<Vec<u32>>,
    certificate: Option<DualAscentResult>,
    root: NodeId,
    dead_nodes: Vec<NodeId>,
    dead_edges: Vec<u32>,
    ils: IlsStats,
}

/// One ascent/heuristic/elimination pass over a fixed graph.
#[allow(clippy::too_many_arguments)]
fn round(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    config: &ReduceConfig,
    incoming_ub: Cost,
    incoming_lb: Cost,
    supplied_dual: Option<&crate::model::ArcDual>,
) -> RoundOutcome {
    let directed = DirectedGraph::from_undirected(graph);
    let idx = ArcIndex::new(&directed);
    let num_arcs = idx.num_arcs();
    let num_edges = graph.edges.len();
    let active = vec![true; num_arcs];

    let mut is_terminal = vec![false; idx.num_nodes()];
    for &t in terminals {
        is_terminal[t as usize] = true;
    }

    let true_costs: Vec<Cost> = (0..num_arcs).map(|a| idx.cost(a as u32)).collect();
    let mut ws = SphWorkspace::new(idx.num_nodes());
    let mut kws = KeyPathWorkspace::new(idx.num_nodes());
    let mut vws = KeyVertexWorkspace::new(idx.num_nodes());

    let roots = root_candidates(terminals, config.roots_per_round);
    let primary = *roots.first().unwrap_or(&terminals[0]);

    // Every constructed tree goes through key-path exchange before it is scored:
    // the construction alone lands several percent above the optimum on the
    // larger instances.
    // Each pool entry keeps both what it spans and how it spans it: the vertex
    // set for the spanning-tree recombination, the arcs for the exact one.
    let mut pool: Vec<(Cost, Vec<NodeId>, Vec<u32>)> = Vec::new();

    let polish = |r: SphResult,
                      root: NodeId,
                      kws: &mut KeyPathWorkspace,
                      ws: &mut SphWorkspace|
     -> SphResult {
        match key_path_exchange(&idx, &active, root, &r, &is_terminal, 6, kws, ws) {
            Some(better) => better,
            None => r,
        }
    };

    // Phase attribution. A round is six phases and "the round took 2.3 s" is not
    // a statement anything can act on until it says which. Off unless
    // `SJ_ROUND_TRACE` is set; the clock reads cost one `Instant::now()` per
    // phase, not per inner iteration.
    let trace = std::env::var_os("SJ_ROUND_TRACE").is_some();
    let round_start = Instant::now();
    let mut phase = round_start;
    let mark = |name: &str, phase: &mut Instant| {
        if trace {
            let now = Instant::now();
            eprintln!(
                "[round] {name:<10} {:6.3}s  (cumulative {:6.3}s)",
                now.duration_since(*phase).as_secs_f64(),
                now.duration_since(round_start).as_secs_f64(),
            );
            *phase = now;
        }
    };

    let expired = || config.deadline.is_some_and(|d| Instant::now() >= d);
    // The construction phase will use every second it is given: one run is
    // `|R|` Dijkstras and the key-path exchange on top of it costs about as much
    // again, so sixty-four starts on a graph with three hundred terminals is
    // measured in seconds. Cap it at a share of the round, because the dual
    // ascent that follows is what drives the eliminations and it must run.
    let primal_deadline = config.deadline.map(|d| {
        Instant::now() + d.saturating_duration_since(Instant::now()).mul_f64(0.4)
    });
    let primal_expired = || primal_deadline.is_some_and(|d| Instant::now() >= d);

    // Order matters here, and it is the whole point of the round.
    //
    // Elimination power is exactly `UB - LB`, so nothing may be eliminated until
    // the best available upper bound exists. And the best upper bound is not the
    // one greedy construction produces against the true costs: on PACE
    // instance161 the best of twenty-five such starts, key-path-polished, costs
    // 7,090 against an optimum of 5,199, while the *same* construction run
    // against the dual ascent's reduced costs reaches 5,354. Arcs the dual leaves
    // tight are the arcs a good tree wants; that is what the reduced costs are.
    //
    // So the round runs: a cheap greedy seed, then the ascents and the guided
    // construction they enable, then iterated local search from the best of
    // everything, and only then the eliminations — against a bound that has had
    // every chance to come down first.
    let mut lower_bound = 0.0;
    let mut certificate: Option<DualAscentResult> = None;
    let mut best_root = primary;
    let mut best_solution: Option<(SphResult, NodeId)> = None;

    let offer = |r: SphResult,
                     root: NodeId,
                     pool: &mut Vec<(Cost, Vec<NodeId>, Vec<u32>)>,
                     best: &mut Option<(SphResult, NodeId)>| {
        pool.push((r.cost, nodes_of(&idx, &r.arcs, root), r.arcs.clone()));
        if best.as_ref().is_none_or(|(b, _)| r.cost < b.cost - 1e-9) {
            *best = Some((r, root));
        }
    };

    // A few greedy starts, mostly to populate the pool and to guarantee some
    // feasible tree exists before the ascents run.
    for s in heuristic_starts(terminals, config.heuristic_starts) {
        if primal_expired() {
            break;
        }
        if let Some(r) = shortest_path_heuristic(
            &idx, &active, &true_costs, primary, s, terminals, &is_terminal, &mut ws,
        ) {
            let r = polish(r, primary, &mut kws, &mut ws);
            offer(r, primary, &mut pool, &mut best_solution);
        }
    }

    mark("greedy", &mut phase);

    // The ascents. Certificates are kept so the eliminations can run afterwards,
    // once the upper bound has finished improving.
    let mut ascents: Vec<(NodeId, DualAscentResult)> = Vec::new();
    for &r in &roots {
        if expired() {
            break;
        }
        let da = dual_ascent_masked(&idx, r, terminals, &active);
        if da.lower_bound > lower_bound {
            lower_bound = da.lower_bound;
            certificate = Some(da.clone());
            best_root = r;
        }

        for s in heuristic_starts(terminals, config.heuristic_starts.min(4)) {
            if expired() {
                break;
            }
            if let Some(sol) = shortest_path_heuristic(
                &idx, &active, &da.reduced_costs, r, s, terminals, &is_terminal, &mut ws,
            ) {
                let sol = polish(sol, r, &mut kws, &mut ws);
                offer(sol, r, &mut pool, &mut best_solution);
            }
        }
        ascents.push((r, da));
    }

    // The supplied certified dual, as one more root.
    //
    // It is *not* an ascent and does not pretend to be: `steps` is empty, so
    // `verify_certificate` would have nothing to replay. What the elimination
    // needs is only what [`crate::model::ArcDual`]'s proposition delivers — a
    // valid bound together with non-negative arc prices that any minimal
    // arborescence pays on top of it — and that is what is packed here. The
    // union rule is unchanged: this root contributes the undirected conclusion
    // only, exactly like every other.
    if let Some(d) = supplied_dual {
        if d.reduced.len() == num_arcs {
            let synthetic = DualAscentResult {
                lower_bound: d.value,
                reduced_costs: d.reduced.clone(),
                root: d.root,
                steps: Vec::new(),
                cuts: Vec::new(),
                sets: Vec::new(),
            };
            if config.verbose {
                eprintln!(
                    "[reduce] supplied dual {:.1} against the round's own ascent {:.1},                      cutoff {:.1}: gap {:.1} -> {:.1}",
                    d.value,
                    lower_bound,
                    incoming_ub,
                    incoming_ub - lower_bound,
                    incoming_ub - d.value.max(lower_bound)
                );
            }
            if d.value > lower_bound {
                lower_bound = d.value;
            }
            ascents.push((d.root, synthetic));
        }
    }

    mark("ascents", &mut phase);

    // Iterated local search from the best tree anyone found, guided or not.
    let mut ils_ws = IlsWorkspace::new(num_arcs);
    let mut ils_stats = IlsStats::default();
    // What the exact steps below are allowed to be predicted to cost: whatever
    // the local search that produced their input cost. See [`EXACT_MIN_SECS`].
    let mut exact_secs = EXACT_MIN_SECS;
    let mut upper_bound = incoming_ub;
    let mut incumbent_arcs: Option<Vec<u32>> = None;
    if let Some((s, r)) = best_solution.take() {
        let ils_start = Instant::now();
        let (best, st) = iterated_local_search(
            &idx,
            &active,
            r,
            terminals,
            &is_terminal,
            s,
            incoming_lb.max(lower_bound),
            config.ils_iterations,
            config.deadline,
            &mut ils_ws,
            &mut ws,
            &mut kws,
            &mut vws,
        );
        exact_secs = ils_start.elapsed().as_secs_f64().max(EXACT_MIN_SECS);
        ils_stats = st;
        // Every distinct local optimum the loop visited, not just the cheapest.
        // They are what the exact recombination selects its parents from.
        for r0 in ils_ws.pool() {
            pool.push((r0.cost, nodes_of(&idx, &r0.arcs, r), r0.arcs.clone()));
        }
        pool.push((best.cost, nodes_of(&idx, &best.arcs, r), best.arcs.clone()));
        if best.cost < upper_bound - 1e-9 {
            upper_bound = best.cost;
            incumbent_arcs = Some(best.arcs);
        }
    }

    // The topological moves that used to run here — key-vertex elimination and
    // vertex insertion — are now part of the iterated local search's own
    // neighbourhood, which is the only place they can change where the loop
    // goes rather than merely tidying what it returned. See
    // [`crate::heuristics::ils`]. They still run once on the incumbent when the
    // loop did not produce it, which happens when a guided construction beat
    // every local optimum outright.
    // A round in which no tree was constructed at all has nothing to polish;
    // otherwise the incumbent is already a local optimum of that neighbourhood.
    mark("ils", &mut phase);

    // Recombination, solved exactly.
    //
    // The union of the vertex sets of several good solutions spans a subgraph
    // containing each of them, so the cheapest tree inside it is no worse than
    // the best input and is frequently strictly better: it can mix a cheap
    // corridor from one solution with a cheap corridor from another. The old
    // code approximated that cheapest tree by a minimum spanning tree, which is
    // the one step in the solver whose ground set was small enough to solve
    // exactly and was being solved most crudely.
    //
    // It is now solved exactly, because a union of good trees is a *near-tree*:
    // its cyclomatic number counts the edges by which the parents disagree, and
    // treewidth is bounded by that. See
    // [`crate::heuristics::exact_recombination`], which decomposes the ground
    // set and dispatches on the width it measures — and which chooses how many
    // parents to admit by that same measured width, rather than by a fixed
    // prefix nobody had looked at. The spanning-tree merge stays as the fallback
    // for the unions that decompose too wide.
    let mut grown: Option<SphResult> = None;
    if pool.len() >= 2 {
        pool.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        pool.dedup_by(|a, b| (a.0 - b.0).abs() < 1e-9 && a.1 == b.1);
        let parents: Vec<SphResult> = pool
            .iter()
            .take(EXACT_RECOMB_PARENTS)
            .map(|(c, _, a)| SphResult { cost: *c, arcs: a.clone() })
            .collect();
        let exact = crate::heuristics::recombine_pool(
            &idx,
            primary,
            &parents,
            terminals,
            &is_terminal,
            EXACT_RECOMB_WIDTH,
            exact_secs,
            config.deadline,
        );
        match exact {
            Some((merged, stat)) => {
                if config.verbose {
                    eprintln!(
                        "[recomb] exact: |V'|={} |E'|={} width={} induced={} {:.1} -> {:.1}                          (pool {})",
                        stat.nodes,
                        stat.edges,
                        stat.width,
                        stat.induced,
                        upper_bound,
                        merged.cost,
                        pool.len(),
                    );
                }
                if merged.cost < upper_bound - 1e-9 {
                    upper_bound = merged.cost;
                    incumbent_arcs = Some(merged.arcs.clone());
                }
                grown = Some(merged);
            }
            None => {
                for take in [2usize, 3, 5, 8] {
                    if take > pool.len() || expired() {
                        break;
                    }
                    let mut union: Vec<NodeId> =
                        pool[..take].iter().flat_map(|(_, v, _)| v.iter().copied()).collect();
                    union.sort_unstable();
                    union.dedup();
                    let Some(merged) = crate::heuristics::sph::mst_prune(
                        &idx,
                        &active,
                        primary,
                        &union,
                        &is_terminal,
                        &mut ws,
                    ) else {
                        continue;
                    };
                    let merged = polish(merged, primary, &mut kws, &mut ws);
                    if merged.cost < upper_bound - 1e-9 {
                        upper_bound = merged.cost;
                        incumbent_arcs = Some(merged.arcs);
                    }
                }
            }
        }
    }

    mark("recomb", &mut phase);

    // Grow the exact neighbourhood until the width cap binds.
    //
    // The recombination above is limited by what the local search happened to
    // visit, and the measurement says that is nowhere near what can be solved:
    // on PACE instance171 a pool of ninety distinct local optima spanned 52 of
    // 241 vertices and decomposed at width four against a cap of eleven. So the
    // ground set is grown — the rest of the graph offered in increasing order of
    // the ascent's reduced costs, every batch that keeps the width inside the
    // cap accepted — and solved exactly. What comes back is the optimum of a
    // subgraph containing the incumbent, so it can only improve it, and no
    // key-path, key-vertex or spanning-tree move confined to that subgraph can
    // beat it. See [`crate::heuristics::exact_recombination::grow_and_solve`].
    let seed = grown
        .map(|g| g.arcs)
        .or_else(|| incumbent_arcs.clone())
        .filter(|_| upper_bound.is_finite());
    if let Some(seed) = seed {
        if !expired() {
            // Arcs the dual leaves tight are the arcs a cheap tree wants, which
            // is the same reason the guided construction uses them.
            let guide = certificate
                .as_ref()
                .map(|c| c.reduced_costs.clone())
                .unwrap_or_else(|| true_costs.clone());
            let out = crate::heuristics::exact_recombination::grow_and_solve(
                &idx,
                primary,
                &seed,
                terminals,
                &is_terminal,
                &guide,
                EXACT_RECOMB_WIDTH,
                exact_secs,
                config.deadline,
            );
            if let Some((better, stat)) = out {
                if config.verbose {
                    eprintln!(
                        "[grow] |V'|={} |E'|={} width={} {:.1} -> {:.1}",
                        stat.nodes, stat.edges, stat.width, upper_bound, better.cost
                    );
                }
                if better.cost < upper_bound - 1e-9 {
                    upper_bound = better.cost;
                    incumbent_arcs = Some(better.arcs);
                }
            }
        }
    }

    mark("grow", &mut phase);

    // Eliminate last, against the bound every phase above has been improving.
    //
    // Each ascent proves, for its own root `r`, that no `r`-arborescence cheaper
    // than `upper_bound` uses a given arc. Only the purely undirected conclusion
    // — both orientations excluded by the *same* root — may be unioned across
    // roots; see the module comment for the counterexample.
    let mut dead_nodes: Vec<NodeId> = Vec::new();
    let mut dead_edges: Vec<u32> = Vec::new();
    let mut edge_dead = vec![false; num_edges];
    let mut node_dead = vec![false; idx.num_nodes()];
    let mut arc_dead = vec![false; num_arcs];

    // The strongest certificate first, and that one runs whatever the clock says.
    //
    // # Why the deadline must not reach this block
    //
    // Every phase above this one improves a *bound*. This is the only phase that
    // makes the graph smaller, and it was the only phase the deadline could
    // cancel outright — so a round that spent its clock on the primal returned a
    // slightly better incumbent and not one deleted element, and the next round
    // started on exactly the same graph.
    //
    // On PACE instance161 that is the whole of the dense group's reduction
    // failure. At a five-second limit the round reports `kill 0n/0e` and the
    // graph stays at 40,857 edges; the *same round*, under the *same* bounds
    // `LB = 5134`, `UB = 5260`, given more clock deletes **7,478 edges**, and
    // the fixpoint then runs 40,857 -> 21,426. Nothing about the mathematics was
    // missing. The round was cancelled one step before it did its job.
    //
    // The step is affordable unconditionally, which is what licenses ignoring
    // the deadline for one root: it is two reduced-cost Dijkstras and a linear
    // scan over the arcs, `O(m + n log n)`, with no enumeration and no LP —
    // milliseconds on the graphs where the phases above cost seconds. The
    // remaining roots stay under the clock, because their cost is a multiple of
    // that and their marginal value is small: the first root is the one with the
    // best certificate, and elimination power is `UB - LB`.
    if upper_bound.is_finite() && !ascents.is_empty() {
        let best_first = ascents
            .iter()
            .position(|(r, _)| *r == best_root)
            .unwrap_or(0);
        let order: Vec<usize> =
            std::iter::once(best_first).chain((0..ascents.len()).filter(|&i| i != best_first)).collect();
        for (nth, &i) in order.iter().enumerate() {
            let (r, da) = &ascents[i];
            if nth > 0 && expired() {
                break;
            }
            let dists = reduced_cost_distances(&idx, *r, terminals, &da.reduced_costs, &active);
            let fix = reduced_cost_fixings(&idx, *r, terminals, da, &dists, &active, upper_bound);

            arc_dead.iter_mut().for_each(|f| *f = false);
            for &a in &fix.arcs {
                arc_dead[a as usize] = true;
            }
            for e in 0..num_edges {
                if !edge_dead[e] && arc_dead[2 * e] && arc_dead[2 * e + 1] {
                    edge_dead[e] = true;
                    dead_edges.push(e as u32);
                }
            }
            for &v in &fix.nodes {
                if !node_dead[v as usize] {
                    node_dead[v as usize] = true;
                    dead_nodes.push(v);
                }
            }
        }
    }

    // A tree attaining `upper_bound`, even when the round did not *improve* it.
    //
    // `incumbent_arcs` is set only on a strict improvement, which is the right
    // rule for an incumbent and the wrong one for a witness: a round that ties
    // the bound it was handed has still constructed a tree of that cost, and
    // that tree is exactly the evidence the bound needs. Without this a warm
    // start at the true optimum would be unprovable — the heuristic matches it,
    // never beats it, and nothing is ever recorded.
    let witness_arcs = incumbent_arcs.clone().or_else(|| {
        pool.iter()
            .filter(|(c, _, _)| *c <= upper_bound + 1e-9)
            .min_by(|a, b| a.0.total_cmp(&b.0))
            .map(|(_, _, arcs)| arcs.clone())
    });
    // The tree as *edges of `graph`*, translated here where the arc index that
    // names those arcs is still in scope. Doing it later — from an arc list and
    // a graph that have drifted apart — is precisely §61's failure.
    let incumbent_edges = witness_arcs.as_ref().and_then(|a| arcs_to_edges(graph, &idx, a));

    mark("eliminate", &mut phase);

    RoundOutcome {
        lower_bound,
        upper_bound,
        incumbent_arcs,
        incumbent_edges,
        certificate,
        root: best_root,
        dead_nodes,
        dead_edges,
        ils: ils_stats,
    }
}

/// Translate an arborescence's arcs into undirected edges of `graph`.
///
/// Matched by endpoint pair *and* cost, and each edge is used at most once, so a
/// graph with parallel edges cannot answer with a cheaper twin. `None` when any
/// arc has no such edge left, which is the only honest answer: a witness that
/// cannot be named in the current graph is not a witness.
fn arcs_to_edges(graph: &UndirectedGraph, idx: &ArcIndex, arcs: &[u32]) -> Option<Vec<u32>> {
    let mut index: HashMap<(NodeId, NodeId), Vec<(u32, Cost)>> = HashMap::new();
    for e in &graph.edges {
        let key = if e.src <= e.dst { (e.src, e.dst) } else { (e.dst, e.src) };
        index.entry(key).or_default().push((e.id, e.cost));
    }
    let mut taken: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(arcs.len());
    for &a in arcs {
        let (t, h, c) = (idx.tail(a), idx.head(a), idx.cost(a));
        let key = if t <= h { (t, h) } else { (h, t) };
        let pick = index
            .get(&key)?
            .iter()
            .find(|(id, ec)| (ec - c).abs() < 1e-9 && !taken.contains(id))?;
        taken.insert(pick.0);
        out.push(pick.0);
    }
    Some(out)
}

/// Vertex set touched by an arc list, always including the root.
fn nodes_of(idx: &ArcIndex, arcs: &[u32], root: NodeId) -> Vec<NodeId> {
    let mut v: Vec<NodeId> = Vec::with_capacity(arcs.len() + 1);
    v.push(root);
    for &a in arcs {
        v.push(idx.tail(a));
        v.push(idx.head(a));
    }
    v.sort_unstable();
    v.dedup();
    v
}

/// Build a smaller graph without the eliminated nodes and edges.
/// Returns `None` if nothing would change.
/// Returns the smaller graph, its terminals, and the node renumbering — indexed
/// by old id, zero where the vertex did not survive — so a witness can follow
/// the shrink instead of being discarded by it.
fn shrink(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    dead_nodes: &[NodeId],
    dead_edges: &[u32],
) -> Option<(UndirectedGraph, Vec<NodeId>, Vec<u32>)> {
    if dead_nodes.is_empty() && dead_edges.is_empty() {
        return None;
    }
    let n = graph.num_nodes as usize + 1;
    let mut node_dead = vec![false; n];
    for &v in dead_nodes {
        node_dead[v as usize] = true;
    }
    // Terminals are never removable.
    for &t in terminals {
        node_dead[t as usize] = false;
    }
    let mut edge_dead = vec![false; graph.edges.len()];
    for &e in dead_edges {
        edge_dead[e as usize] = true;
    }

    let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
    let mut map = vec![0u32; n];
    let mut next = 1u32;
    let mut out = UndirectedGraph::new(0);
    for node in &graph.nodes {
        if node_dead[node.id as usize] {
            continue;
        }
        map[node.id as usize] = next;
        let nt = if terminal_set.contains(&node.id) { NodeType::Terminal } else { NodeType::Steiner };
        out.add_node(next, nt, node.weight);
        next += 1;
    }
    out.num_nodes = next - 1;

    for edge in &graph.edges {
        if edge_dead[edge.id as usize]
            || node_dead[edge.src as usize]
            || node_dead[edge.dst as usize]
        {
            continue;
        }
        out.add_edge(map[edge.src as usize], map[edge.dst as usize], edge.cost);
    }

    let mut new_terminals: Vec<NodeId> = terminals.iter().map(|&t| map[t as usize]).collect();
    new_terminals.sort_unstable();
    Some((out, new_terminals, map))
}

/// Wrap a graph as a `SteinerInstance` so the reduction package can consume it.
pub fn as_instance(graph: &UndirectedGraph, terminals: &[NodeId]) -> SteinerInstance {
    SteinerInstance {
        name: String::from("reduced"),
        comment: String::new(),
        num_nodes: graph.num_nodes,
        num_edges: graph.edges.len() as u32,
        num_terminals: terminals.len() as u32,
        nodes: graph.nodes.clone(),
        edges: graph.edges.clone(),
        terminals: terminals.to_vec(),
        root: terminals.first().copied(),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    fn line_instance() -> (UndirectedGraph, Vec<NodeId>) {
        // 1(T) -1- 2 -1- 3(T) plus a costly detour that must be eliminated.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 4, 50.0);
        g.add_edge(4, 3, 50.0);
        (g, vec![1, 3])
    }

    #[test]
    fn proves_optimality_without_branching() {
        let (g, t) = line_instance();
        let out = tighten(g, t, &ReduceConfig::default());
        assert!((out.upper_bound - 2.0).abs() < 1e-9, "UB {}", out.upper_bound);
        assert!(out.proved_optimal(1e-6), "LB {} UB {}", out.lower_bound, out.upper_bound);
    }

    #[test]
    fn lower_bound_never_exceeds_the_optimum() {
        let mut seed = 0xDEADBEEFCAFEu64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..300 {
            let n = 5 + (rng() % 4) as u32;
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
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };

            let out = tighten(g, terminals, &ReduceConfig::default());
            assert!(
                out.lower_bound <= opt + 1e-6,
                "LB {} > optimum {opt}",
                out.lower_bound
            );
            assert!(
                out.upper_bound >= opt - 1e-6,
                "UB {} < optimum {opt}",
                out.upper_bound
            );
            if out.proved_optimal(1e-6) {
                assert!(
                    (out.upper_bound - opt).abs() < 1e-6,
                    "claimed optimal {} but true optimum is {opt}",
                    out.upper_bound
                );
            }
        }
    }

    /// [`Reduced::as_identity`] preserves every claim the struct makes, at a
    /// **non-zero** offset.
    ///
    /// # Why the `Reduced` is built rather than produced
    ///
    /// The obvious gate — reduce a contractible instance and restate the result —
    /// cannot reach a non-zero offset at all, and finding that out is worth
    /// recording. `tighten` runs `preprocess_bounded` only *after* a round that
    /// killed something: a round that proves optimality, and a round that kills
    /// nothing, both `break` before the contraction step. On instances small
    /// enough for a test the first round proves optimality, and on the PACE
    /// instances measured the first round kills nothing, so `offset` is zero in
    /// both regimes — 0 of 300 constructed reductions contracted, and every PACE
    /// instance sampled reports `offset=0.0`. That is exactly why the double
    /// charge was latent rather than live, and it is also why a gate built on the
    /// pipeline would assert nothing.
    ///
    /// So the proposition is gated on its own terms: `Reduced` values with
    /// randomly chosen non-zero offsets and real witnesses, checked for the two
    /// invariants the proposition claims to preserve.
    #[test]
    fn restating_a_reduction_for_its_own_graph_preserves_every_claim() {
        let mut seed = 0x0DDB_A11B_ADC0_FFEEu64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut witnessed, mut unwitnessed, mut checked) = (0, 0, 0);
        for _ in 0..400 {
            let n = 4 + (rng() % 6) as u32;
            let mut g = UndirectedGraph::new(n);
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= 2 + (rng() % 2) as u32;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for v in 1..n {
                g.add_edge(v, v + 1, 1.0 + (rng() % 9) as f64);
            }
            // The path spans every terminal, so it is a genuine witness.
            let edges: Vec<u32> = (0..g.edges.len() as u32).collect();
            let cost: Cost = g.edges.iter().map(|e| e.cost).sum();
            let offset = (rng() % 500) as Cost + 1.0;
            let w_offset = (rng() % 500) as Cost;
            // Honest half the time, a value the witness does not attain the other
            // half: `as_identity` must preserve *whichever* answer holds.
            let honest = rng() % 2 == 0;
            let upper_bound =
                if honest { cost + w_offset - offset } else { cost + w_offset - offset + 7.0 };
            let out = Reduced {
                graph: g.clone(),
                terminals: terminals.clone(),
                root: terminals[0],
                lower_bound: (rng() % 100) as Cost,
                upper_bound,
                incumbent_arcs: None,
                witness: Some(Witness {
                    graph: g.clone(),
                    terminals: terminals.clone(),
                    edges,
                    cost,
                    offset: w_offset,
                }),
                certificate: None,
                offset,
                rounds: 1,
                converged: true,
            };
            assert_eq!(out.upper_bound_is_witnessed(), honest, "the fixture is wrong");
            if honest {
                witnessed += 1;
            } else {
                unwitnessed += 1;
            }

            let id = out.as_identity();
            assert!(id.offset.abs() < 1e-12, "offset not zeroed");
            assert_eq!(id.lower_bound.to_bits(), out.lower_bound.to_bits());
            assert_eq!(id.upper_bound.to_bits(), out.upper_bound.to_bits());
            assert_eq!(id.graph.edges.len(), out.graph.edges.len());
            // The claim that matters.
            assert_eq!(
                id.upper_bound_is_witnessed(),
                out.upper_bound_is_witnessed(),
                "as_identity changed whether the bound is witnessed at offset {offset}"
            );
            // And the value the witness proves attainable moves by exactly the
            // offset that was removed, which is what makes the caller's own
            // running total right.
            let a = out.verify_witness().unwrap();
            let b = id.verify_witness().unwrap();
            assert!(
                (a - offset - b).abs() < 1e-9,
                "witness value {a} - offset {offset} != restated {b}"
            );
            checked += 1;
        }
        assert!(
            checked > 350 && witnessed > 100 && unwitnessed > 100,
            "{checked} restatements, {witnessed} witnessed and {unwitnessed} not —              the gate did not exercise both answers"
        );
    }

    /// The invariant the whole pipeline rests on, under a **loose** cutoff.
    ///
    /// Every bound-based rule in the round preserves the trees strictly cheaper
    /// than the incumbent it is given, not the optimum outright. So the test
    /// that means something is: hand the tightening an upper bound strictly
    /// above the optimum, and check that the optimum is still *in the graph it
    /// returns*, at `reduced optimum + offset`.
    ///
    /// The default configuration never exercises this. Its heuristics find the
    /// optimum on graphs this small, so the cutoff is always tight and the rules
    /// are allowed to delete everything but the incumbent. PACE Track 1's
    /// instance184 is what asks for it: an experiment that left the heuristic
    /// five units above the optimum produced a graph in which the search
    /// exhausted below the cutoff and the incumbent was announced as proved.
    #[test]
    fn a_loose_cutoff_still_leaves_the_optimum_in_the_graph() {
        let mut seed = 0xFEED_FACE_1234_5678u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        for _ in 0..400 {
            let n = 5 + (rng() % 4) as u32;
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
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };

            for slack in [1.0, 2.0, 5.0] {
                let cfg = ReduceConfig {
                    initial_upper_bound: opt + slack,
                    ..ReduceConfig::default()
                };
                let out = tighten(g.clone(), terminals.clone(), &cfg);
                let red_edges: Vec<(NodeId, NodeId, Cost)> =
                    out.graph.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
                let max_id = out.graph.nodes.iter().map(|x| x.id).max().unwrap_or(0);
                let Some(red_opt) = brute_force(max_id, &red_edges, &out.terminals) else {
                    continue;
                };
                assert!(
                    (red_opt + out.offset - opt).abs() < 1e-6,
                    "reduced optimum {red_opt} + offset {} != optimum {opt} at cutoff {}",
                    out.offset,
                    opt + slack
                );
                assert!(out.lower_bound <= opt + 1e-6, "LB {} > optimum {opt}", out.lower_bound);
                // The witness, on the same runs. Under a *loose* cutoff the loop
                // has room to shrink under the incumbent, which is precisely the
                // regime in which the carried bound and the graph it is stated
                // for come apart.
                if let Some(v) = out.verify_witness() {
                    assert!(
                        (v - (out.upper_bound + out.offset)).abs() < 1e-6,
                        "witness value {v} != upper bound {} + offset {}",
                        out.upper_bound,
                        out.offset
                    );
                    assert!(v >= opt - 1e-6, "witness value {v} below the optimum {opt}");
                }
                checked += 1;
            }
        }
        assert!(checked > 200, "only {checked} cases were exercised");
    }

    /// The same invariant, with a **supplied lower bound and a supplied dual**.
    ///
    /// The dual is a real one: the root cut loop is run on the same graph and its
    /// certified arc pricing handed to `tighten`, so the test exercises the
    /// object the pipeline actually passes and not a hand-made stand-in. Three
    /// things are asserted at three cutoff slacks:
    ///
    /// - `reduced optimum + offset == original optimum` — the eliminations the
    ///   stronger dual licenses must still leave an optimum in the graph, and a
    ///   *loose* cutoff is the case that can catch a bound-based rule being
    ///   wrong, since a tight one leaves nothing to delete;
    /// - the reported lower bound never exceeds the optimum;
    /// - a supplied bound is never *lost*: the loop reports at least what it was
    ///   handed, which is the defect `initial_lower_bound` exists to fix.
    #[test]
    fn a_supplied_dual_and_lower_bound_still_leave_the_optimum_in_the_graph() {
        use crate::model::RootSeparation;
        let mut seed = 0x51DE_51DE_9999_0007u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        let mut with_dual = 0;
        for case in 0..260 {
            let n = 5 + (rng() % 5) as u32;
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
                        let c = if case % 3 == 0 { 1.0 } else { 1.0 + (rng() % 9) as f64 };
                        g.add_edge(u, v, c);
                        edges.push((u, v, c));
                    }
                }
            }
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };

            // A genuine certified dual for this graph, from the loop the
            // pipeline uses.
            let directed = DirectedGraph::from_undirected(&g);
            let mut sep = RootSeparation::new(&directed, terminals[0], &terminals);
            let deadline = Instant::now() + std::time::Duration::from_secs(10);
            let dual = sep
                .advance(Cost::INFINITY, deadline, 60, 1 << 20)
                .and_then(|c| c.arc_dual);
            if let Some(d) = &dual {
                assert!(
                    d.value <= opt + 1e-6,
                    "case {case}: certified dual {} exceeds the optimum {opt}",
                    d.value
                );
                assert!(
                    d.reduced.iter().all(|&r| r >= 0.0),
                    "case {case}: a negative arc price reached the reduction"
                );
                with_dual += 1;
            }

            for slack in [1.0, 2.0, 5.0] {
                let cfg = ReduceConfig {
                    initial_upper_bound: opt + slack,
                    initial_lower_bound: dual.as_ref().map_or(0.0, |d| d.value),
                    initial_dual: dual.clone(),
                    ..ReduceConfig::default()
                };
                let out = tighten(g.clone(), terminals.clone(), &cfg);
                let red_edges: Vec<(NodeId, NodeId, Cost)> =
                    out.graph.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
                let max_id = out.graph.nodes.iter().map(|x| x.id).max().unwrap_or(0);
                let Some(red_opt) = brute_force(max_id, &red_edges, &out.terminals) else {
                    continue;
                };
                assert!(
                    (red_opt + out.offset - opt).abs() < 1e-6,
                    "case {case}: reduced optimum {red_opt} + offset {} != optimum {opt} \
                     at cutoff {} under a supplied dual",
                    out.offset,
                    opt + slack
                );
                assert!(
                    out.lower_bound <= opt + 1e-6,
                    "case {case}: LB {} > optimum {opt}",
                    out.lower_bound
                );
                if let Some(d) = &dual {
                    // The bound handed in must never be thrown away. `tighten`
                    // restates its bound for the graph it ends on, so the
                    // comparison is against `lower_bound + offset`.
                    assert!(
                        out.lower_bound + out.offset >= d.value - 1e-6,
                        "case {case}: supplied bound {} lost, loop reports {} + {}",
                        d.value,
                        out.lower_bound,
                        out.offset
                    );
                }
                checked += 1;
            }
        }
        assert!(checked > 150, "only {checked} cases were exercised");
        assert!(with_dual > 40, "only {with_dual} cases actually carried a dual");
    }

    /// A bound with no tree behind it is never announced as achieved.
    ///
    /// The pipeline is handed an incumbent *below the optimum* — a value no tree
    /// attains — which is the state §61 diagnoses reached by a heuristic that
    /// stalled above the optimum and a chain of carried bounds that lost track of
    /// what produced them. Under it the bound-based rules delete a great deal
    /// (correctly: nothing cheaper than the cutoff exists, so everything is
    /// eliminable), the frontier exhausts below the cutoff, and the old code
    /// reported `Optimal` at the fiction.
    ///
    /// The assertion is the whole of the correctness claim: whatever the solver
    /// says, it never says `Optimal` at a value the instance cannot achieve.
    #[test]
    fn an_unwitnessed_incumbent_is_never_reported_as_proved() {
        use crate::branch_and_bound::{SolveStatus, SolverConfig};
        let mut seed = 0x1BAD_5EED_9876_4321u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        for _ in 0..120 {
            let n = 5 + (rng() % 4) as u32;
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
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };
            let instance = as_instance(&g, &terminals);
            for deficit in [1.0, 2.0, 5.0] {
                if opt - deficit <= 0.0 {
                    continue;
                }
                let cfg = SolverConfig {
                    time_limit_secs: 2.0,
                    verbose: false,
                    initial_upper_bound: opt - deficit,
                    ..SolverConfig::default()
                };
                let r = crate::solver::solve(&instance, cfg);
                if r.status == SolveStatus::Optimal {
                    assert!(
                        (r.primal_bound - opt).abs() < 1e-6,
                        "claimed Optimal {} against a true optimum of {opt} \
                         under a fictional incumbent of {}",
                        r.primal_bound,
                        opt - deficit
                    );
                }
                // And whatever it claims, a finite primal must be achievable.
                if r.primal_bound.is_finite() {
                    assert!(
                        r.primal_bound >= opt - 1e-6,
                        "primal {} below the optimum {opt}",
                        r.primal_bound
                    );
                }
                checked += 1;
            }
        }
        assert!(checked > 100, "only {checked} cases were exercised");
    }

    /// A near-tree with more terminals than Dreyfus-Wagner can address, so the
    /// pipeline is actually entered.
    ///
    /// The small dense graphs above never reach [`crate::solver::finish`]: with
    /// three terminals on eight vertices `try_dreyfus_wagner` closes them before
    /// the tightening runs, and the paths that report `primal = dual =
    /// root_upper_bound` are never touched. Instrumenting the test showed 291 of
    /// 291 cases taking that shortcut — the test passed and proved nothing, which
    /// is exactly the sort of measurement §63's closing note warns about.
    ///
    /// A weighted grid: narrow enough for the reference dynamic programme to
    /// solve exactly, dense and terminal-rich enough that neither Dreyfus-Wagner
    /// nor the classical reduction disposes of it first.
    ///
    /// Both easier generators were tried and both were useless, which is worth
    /// recording because the *test passing* said nothing in either case. Small
    /// dense graphs are closed by `try_dreyfus_wagner` before the tightening
    /// runs; near-trees are closed by the classical reduction, which contracts
    /// the instance to fewer than two terminals and returns `trivial_result`. A
    /// grid has minimum degree two everywhere, no degree-one chains to contract,
    /// and more terminals than `dw_is_affordable` admits.
    pub(crate) fn grid_instance(rng: &mut dyn FnMut() -> u64) -> Option<(SteinerInstance, Cost)> {
        use crate::graph::algorithms::steiner_td::reference::{raw_dp, RawCensus};
        use crate::graph::algorithms::tree_decomposition::decompose;
        let rows = 5 + (rng() % 2) as u32;
        let cols = 7 + (rng() % 3) as u32;
        let n = rows * cols;
        let id = |r: u32, c: u32| r * cols + c + 1;
        // Enough terminals that Dreyfus-Wagner is refused, spread over the grid.
        let mut is_t = vec![false; n as usize + 1];
        let k = 26 + (rng() % 5) as usize;
        let mut placed = 0;
        let mut v = 1u32;
        while placed < k && v <= n {
            if rng() % 3 != 0 {
                is_t[v as usize] = true;
                placed += 1;
            }
            v += 1;
            if v > n && placed < k {
                v = 1;
            }
        }
        let mut g = UndirectedGraph::new(n);
        let mut terminals = Vec::new();
        for v in 1..=n {
            let t = is_t[v as usize];
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            if t {
                terminals.push(v);
            }
        }
        for r in 0..rows {
            for c in 0..cols {
                if c + 1 < cols {
                    g.add_edge(id(r, c), id(r, c + 1), 1.0 + (rng() % 9) as f64);
                }
                if r + 1 < rows {
                    g.add_edge(id(r, c), id(r + 1, c), 1.0 + (rng() % 9) as f64);
                }
            }
        }
        let td = decompose(&g, 12, None)?;
        let mut census = RawCensus::default();
        let opt = raw_dp(&g, &terminals, &td, 3_000_000, None, &mut census)?;
        Some((as_instance(&g, &terminals), opt))
    }

    #[test]
    fn an_unwitnessed_incumbent_is_never_proved_on_the_full_pipeline() {
        use crate::branch_and_bound::{SolveStatus, SolverConfig};
        let mut seed = 0x51DE_57ED_9E37_79B9u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        let mut entered = 0;
        for _ in 0..40 {
            let Some((instance, opt)) = grid_instance(&mut rng) else { continue };
            for deficit in [1.0, 3.0] {
                if opt - deficit <= 0.0 {
                    continue;
                }
                for preprocess in [true, false] {
                let cfg = SolverConfig {
                    time_limit_secs: 3.0,
                    verbose: false,
                    preprocess,
                    initial_upper_bound: opt - deficit,
                    ..SolverConfig::default()
                };
                let r = crate::solver::solve(&instance, cfg);
                entered += 1;
                if r.status == SolveStatus::Optimal {
                    assert!(
                        (r.primal_bound - opt).abs() < 1e-6,
                        "claimed Optimal {} against a true optimum of {opt} \
                         under a fictional incumbent of {}",
                        r.primal_bound,
                        opt - deficit
                    );
                }
                if r.primal_bound.is_finite() {
                    assert!(
                        r.primal_bound >= opt - 1e-6,
                        "primal {} below the optimum {opt}",
                        r.primal_bound
                    );
                }
                checked += 1;
                }
            }
        }
        assert!(checked > 30 && entered > 30, "only {checked}/{entered} cases were exercised");
    }

    /// The positive control: a *true* incumbent, supplied without a tree, must
    /// not cost the solver its proof.
    ///
    /// This is the case version one of the check got wrong (§61), taking PACE
    /// Track 1's instance080 and instance157 from proved to unproved by reading
    /// an absent witness as evidence against a perfectly good bound. Here the
    /// round ties the supplied value, records the tree it tied it with, and the
    /// proof stands.
    #[test]
    fn a_true_incumbent_supplied_without_a_tree_is_still_proved() {
        use crate::branch_and_bound::{SolveStatus, SolverConfig};
        let mut seed = 0x2CAFE_1234_5678_9ABu64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut proved, mut total) = (0, 0);
        for _ in 0..80 {
            let n = 5 + (rng() % 4) as u32;
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
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };
            let instance = as_instance(&g, &terminals);
            let cfg = SolverConfig {
                time_limit_secs: 2.0,
                verbose: false,
                initial_upper_bound: opt,
                ..SolverConfig::default()
            };
            let r = crate::solver::solve(&instance, cfg);
            total += 1;
            if r.status == SolveStatus::Optimal {
                assert!((r.primal_bound - opt).abs() < 1e-6);
                proved += 1;
            }
        }
        assert!(total > 40, "only {total} cases ran");
        assert!(
            proved * 10 >= total * 9,
            "a true incumbent cost the proof on {} of {total} instances",
            total - proved
        );
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
        if best.is_finite() { Some(best) } else { None }
    }
}
