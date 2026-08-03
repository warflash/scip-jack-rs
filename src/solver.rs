//! Top-level solve pipeline.
//!
//! ```text
//! read -> classical reductions -> ascend-and-prune -> exact finish
//! ```
//!
//! The exact finish is dynamic programming when the terminal set is small enough
//! for it to be cheap, and branch-and-cut otherwise. Most SteinLib B/C instances
//! never reach it: ascend-and-prune closes the bound at the root.
//!
//! Between the goal-directed search and the branch-and-cut sits one conditional
//! step. The search's A* potential is a dual-ascent cut packing, and that packing
//! is *maximal* — no set missing the root admits any increase — so a search it
//! fails to close cannot be helped by any further ascent. When that happens, and
//! only then, a bounded root cut loop runs and its dual is turned back into a
//! packing by [`crate::model::lp_packing`]; the search is retried against the
//! pointwise maximum of the two. Everything that step costs comes out of budget
//! the first attempt has already been shown not to need.

use std::time::Instant;

use crate::branch_and_bound::{BranchAndCutSolver, SolveStatus, SolverConfig};
use crate::graph::algorithms::{
    dreyfus_wagner, dual_ascent_packing, ArcIndex, PackingAdmission, SteinerSearch,
    MAX_PACKING_LAYERS,
};
use crate::graph::{costs_are_integral, tighten_dual, Cost, DirectedGraph, SteinerInstance, UndirectedGraph};
use crate::io;
use crate::model::{
    hyp_certificate, hyp_work, verify_solution, RootSeparation, HYP_UNITS_PER_SECOND,
    HYP_WORK_CEILING,
};
use crate::preprocessing::preprocess_until;
use crate::root_reduce::{tighten, ReduceConfig, Witness};

/// Only dispatch to the Dreyfus-Wagner DP when its `3^k * n` term is affordable.
/// The old code keyed off the terminal count alone, which is meaningless without
/// the graph size: 15 terminals on 500 nodes is 7e9 operations.
const DW_WORK_BUDGET: f64 = 5e7;

/// Labels the goal-directed search may settle before abandoning itself.
///
/// This is a memory guard, not a performance dial: each settled label holds a
/// cost and a bitmask, so a few million of them is the point at which the search
/// stops being cheaper than the branch-and-cut it would hand back to. The search
/// is exact when it finishes and yields a valid dual bound when it does not, so
/// the only thing this constant can cost is time.
const DS_LABEL_BUDGET: u64 = 6_000_000;

/// Vertex entries the ascent may record while building the packing that guides
/// the search. A truncated packing is still a packing, so this only bounds
/// memory; it cannot make a bound invalid.
const DS_PACKING_NNZ: usize = 8_000_000;

/// Separation rounds the root certificate LP may run before reading its dual.
///
/// This bounds work, not quality: every round leaves a valid LP bound and a
/// certifiable dual, and the loop already stops early when a round separates
/// nothing — which is the point at which the cut relaxation has been solved
/// exactly and further rounds cannot move anything.
const ROOT_CERT_ROUNDS: usize = 40;

/// Counters that let a test check it reached the code it is testing.
///
/// A gate that passes because the path never executed proves nothing, and on this
/// pipeline the multi-pass path is reached only by instances the first pass fails
/// to close — which the obvious small random generator never produces. These are
/// bumped at the two writebacks the feedback loop consists of, and the gates
/// assert they moved.
#[cfg(test)]
pub(crate) mod probe {
    use std::sync::atomic::AtomicUsize;
    /// Times a pass handed the next one a strictly positive lower bound.
    pub static CARRIED_BOUNDS: AtomicUsize = AtomicUsize::new(0);
    /// Of those, the ones that came from the branch-and-cut. Counted separately
    /// because the proposition that licenses them is a different one, and a gate
    /// that only ever reached the search's writeback has not tested it.
    pub static CARRIED_BNC_BOUNDS: AtomicUsize = AtomicUsize::new(0);
    /// Times a pass handed the next one a tree it had verified.
    pub static CARRIED_WITNESSES: AtomicUsize = AtomicUsize::new(0);
    /// Times a reduction was actually handed one of those trees.
    pub static CONSUMED_WITNESSES: AtomicUsize = AtomicUsize::new(0);
}

#[derive(Debug, Clone)]
pub struct SolveResult {
    pub status: SolveStatus,
    pub primal_bound: f64,
    pub dual_bound: f64,
    pub gap_pct: f64,
    pub nodes_processed: u64,
    pub cuts_added: u64,
    pub lp_solves: u64,
    pub time_secs: f64,
    pub verified: bool,
    pub method: SolveMethod,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SolveMethod {
    DreyfusWagner,
    /// Proved at the root by dual ascent and reduced-cost elimination.
    AscendAndPrune,
    /// Proved exactly by dynamic programming over a tree decomposition, whose
    /// cost is exponential in the width and indifferent to the terminal count.
    TreeDecomposition,
    BranchAndCut,
}

fn dw_is_affordable(num_terminals: usize, num_nodes: u32, num_edges: usize) -> bool {
    if num_terminals < 2 || num_terminals > 24 {
        return false;
    }
    // Both terms matter. The subset-merge step is `3^k * n`, but each of the
    // `2^k` subsets also runs one Dijkstra, which is `m log n`. On PACE
    // instance023 — 9 terminals, 640 vertices, 204,453 edges — the first term is
    // 13 million and the second is 105 million, and a budget that looked only at
    // the first spent twelve seconds inside a five-second limit.
    let k = num_terminals as i32;
    let n = num_nodes as f64;
    let merge = 3f64.powi(k) * n;
    let search = 2f64.powi(k) * (num_edges as f64 + n * n.max(2.0).log2());
    merge + search <= DW_WORK_BUDGET
}

/// Solve a Steiner tree instance held in memory.
pub fn solve(instance: &SteinerInstance, config: SolverConfig) -> SolveResult {
    let start = Instant::now();
    let deadline = start + std::time::Duration::from_secs_f64(config.time_limit_secs.max(0.001));

    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }

    // Cost that classical reduction contracted out of the graph. Every bound
    // below is stated for `work_graph`; the bound for `instance` is this plus
    // that value, and the addition happens once, at the very end.
    let mut base_offset: Cost = 0.0;
    let (work_graph, terminals) = if config.preprocess {
        // Reduction gets at most a third of the budget. It is worth a lot, but a
        // dense instance can absorb the whole limit in one sweep and leave the
        // solver with no time to find a solution at all.
        let reduce_deadline = start + std::time::Duration::from_secs_f64(
            (config.time_limit_secs.max(0.001) / 3.0).max(0.05),
        );
        let (rg, pr) = preprocess_until(instance, &graph, Some(reduce_deadline));
        base_offset = pr.lower_bound_offset;
        let (ri, ru) = rg.to_instance();
        if config.verbose {
            eprintln!(
                "[reduce] classical: {} -> {} nodes, {} -> {} edges, {} -> {} terminals, offset {:.1}",
                instance.num_nodes,
                ri.num_nodes,
                instance.num_edges,
                ri.num_edges,
                instance.terminals.len(),
                ri.terminals.len(),
                base_offset
            );
        }
        if config.verbose {
            eprintln!("[time] classical reduction took {:.2}s", start.elapsed().as_secs_f64());
        }
        (ru, ri.terminals)
    } else {
        (graph, instance.terminals.clone())
    };

    if terminals.len() < 2 {
        return trivial_result(start, base_offset, SolveMethod::AscendAndPrune);
    }

    if let Some(mut r) = try_dreyfus_wagner(&work_graph, &terminals, start) {
        r.primal_bound += base_offset;
        r.dual_bound += base_offset;
        return r;
    }

    // Ascend-and-prune, then branch-and-cut, then — if the search improved the
    // incumbent without proving it — ascend-and-prune again with that better
    // cutoff. The heuristic's own bound is often several percent off, and the
    // reduced-cost eliminations scale with `UB - LB`, so a tighter cutoff
    // discovered during the search can collapse the instance on a second pass.
    // Each pass hands the next one its *own* reduced instance, not the graph it
    // started from.
    //
    // Tightening is a fixpoint computation and it is monotone: every round
    // deletes and contracts, and nothing it does is ever undone. Re-running it
    // from the original graph therefore repeats work the previous pass already
    // did — and repeats it under a *shorter* deadline, so it does not even get as
    // far. On PACE instance161 the first pass took the graph from 40,857 edges to
    // 33,379 and the bound from 5,134 to 5,138; the second pass, restarting from
    // scratch with a third of the clock, returned 40,857 edges and 5,134, and the
    // solver then finished on the weaker of the two. Carrying the instance
    // forward makes the passes compound instead of compete, and it is also what
    // lets the goal-directed search resume: an unchanged graph is the case
    // [`SteinerSearch::applies_to`] recognises.
    let mut pass_graph = work_graph;
    let mut pass_terminals = terminals;
    // Cost already contracted out of `pass_graph` by earlier passes. Every
    // bound a pass reports is stated for its own graph; this is what puts them
    // back on a common scale.
    let mut carried_offset: Cost = 0.0;
    // A caller-supplied incumbent value is on the *original* instance's scale;
    // `base_offset` has already been contracted out of `pass_graph`.
    let mut incoming_ub = config.initial_upper_bound - base_offset;
    let mut best: Option<SolveResult> = None;
    // The goal-directed search, carried across passes. When the second pass's
    // tightening lands on the same reduced instance — which is the usual case
    // once the first pass has already run the reductions to a fixpoint — the
    // search continues instead of starting over. See [`SteinerSearch`].
    let mut search_cache: Option<SteinerSearch> = None;
    // The root separation loop, carried the same way and for the same reason.
    // Unlike the tightening fixpoint this is not redundant work — the loop is
    // deadline-truncated, so a second run with more clock genuinely separates
    // more — which is why the repair is resumption rather than memoisation. See
    // [`RootSeparation`].
    let mut sep_cache: Option<RootSeparation> = None;
    // Root bounds an earlier pass proved, restated for the current pass's graph
    // exactly as `incoming_ub` is, and a note on whether the branch-and-cut has
    // been observed to do anything on this instance. The first pass assumes it
    // does; only a pass that watched it solve nothing says otherwise.
    let mut carried_lower_bound: Cost = 0.0;
    let mut branch_and_cut_works = true;
    // What the width attempt already spent, and on which graph.
    //
    // [`try_decomposition`] is deterministic: the same graph, the same ordering
    // portfolio, the same dynamic programme, in that order. An attempt cut off by
    // the deadline is therefore cut off at exactly the same place when it is
    // re-run on the same graph with *less* clock — and a later pass always has
    // less, because the passes share one budget and the earlier one has already
    // spent from it. Re-running it is not a second chance; it is a guaranteed
    // repetition of a truncated computation, and on the wide instances it
    // consumes the entire window. PACE instance092 spends every pass inside a
    // width attempt that cannot finish, which is why its branch-and-cut reports
    // `Nodes: 0 | LPs: 0 | Time: 0.00s` while the root separation loop converges
    // the same instance in 0.43 s at exactly its optimum.
    //
    // So the seconds it was granted are remembered together with the shape of the
    // graph they were granted on, and the attempt is skipped only when both say it
    // would repeat itself. A pass whose reduction shrank the graph gets a fresh
    // attempt: that is a different computation. A pass that somehow has *more*
    // clock gets one too.
    //
    // This is a refusal to repeat, not a refusal to try, and it can only move
    // seconds from a stage that provably cannot use them to one that might. It
    // never changes the answer of an attempt that ran.
    let mut td_truncated: Option<(usize, usize, usize, f64)> = None;
    // No pass has run, so no bound has been exhibited yet.
    let mut carried_primal_witnessed = false;
    // Dual bound per second, as the goal-directed search itself was observed to
    // produce it. See `finish` for what it is compared against.
    let mut search_rate: Cost = 0.0;

    // A tree an earlier pass exhibited on the graph this pass is handed. See
    // [`witness_from_arcs`] for why only a tree of *that* graph may travel.
    let mut carried_witness: Option<Witness> = None;
    // A converged tightening carried into the next pass; see below.
    let mut reuse: Option<crate::root_reduce::Reduced> = None;
    // The root cut loop's certified dual, restated for the graph the next pass
    // will tighten. See [`ReduceConfig::initial_dual`].
    let mut carried_dual: Option<crate::model::ArcDual> = None;
    for pass in 0..2 {
        // Split the remaining budget explicitly. Tightening will happily use
        // every second it is given — on SteinLib e13 two rounds of it consumed a
        // twenty-second limit whole and the search was handed 0.02s — so it gets
        // a share, not the whole clock.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let reduce_deadline = Instant::now() + remaining.mul_f64(0.35);
        let reduce_config = ReduceConfig {
            deadline: Some(reduce_deadline),
            verbose: config.verbose,
            initial_upper_bound: incoming_ub,
            // What the previous pass proved, handed forward instead of being
            // re-derived. `carried_lower_bound` is already restated for this
            // pass's graph; `carried_dual` is checked against it below.
            initial_lower_bound: carried_lower_bound,
            initial_dual: carried_dual.take(),
            // A tree for `incoming_ub`, when the pass that found it found it on
            // *this* graph. Only then does the identity
            // `cost + offset == initial_upper_bound` hold on the scale this
            // reduction is stated in, which is what `initial_witness` asserts.
            initial_witness: carried_witness
                .take()
                .filter(|w| (w.cost + w.offset - incoming_ub).abs() < 1e-6)
                .inspect(|_| {
                    #[cfg(test)]
                    probe::CONSUMED_WITNESSES
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }),
            ..ReduceConfig::default()
        };
        let tighten_start = Instant::now();
        // A tightening that reached a fixpoint, on a graph nothing has changed
        // since, with an incumbent no better than the one it finished with, is a
        // function whose arguments have not moved. Re-evaluating it is the one
        // thing a three-second budget cannot afford to do twice: on PACE
        // instance167 it cost 0.71 s of five, and the goal-directed search that
        // spent the rest was 3 units short of a proof it reaches in 363,000
        // labels. See [`Reduced::converged`] for why the skip preserves the
        // answer exactly rather than approximately.
        let reused = reuse.take();
        let reused_here = reused.is_some();
        let reduced = match reused {
            Some(r) => r,
            None => tighten(pass_graph.clone(), pass_terminals.clone(), &reduce_config),
        };
        let tighten_secs = tighten_start.elapsed().as_secs_f64();
        // Reusable next time when it converged and nothing downstream can have
        // strengthened its hypotheses. The upper-bound test is made below, once
        // the pass has reported what it found.
        // Restated for its own graph, which is the graph the next pass is handed.
        // See [`Reduced::as_identity`] for the offset that would otherwise be
        // charged twice.
        let reusable = reduced
            .converged
            .then(|| (reduced.as_identity(), reduced.upper_bound, reduced.lower_bound));
        // The bound the fixpoint converged under, on its own reduced graph — the
        // scale the next pass's dual is stated in.
        let reused_lower_bound = reduced.lower_bound;
        // Whether this pass can exhibit a tree for the bound it will report.
        let witnessed_here = reduced.upper_bound_is_witnessed() || carried_primal_witnessed;
        // What the next pass will start from, before `finish` consumes `reduced`.
        let next_graph = reduced.graph.clone();
        let next_terminals = reduced.terminals.clone();
        let next_offset = reduced.offset;
        // Did the reduction move the graph at all?
        //
        // This is the evidence the half-window reservation below is spent on, and
        // it is a property of the instance rather than of the clock.
        let reduction_moved = reduced.graph.num_nodes != pass_graph.num_nodes
            || reduced.graph.edges.len() != pass_graph.edges.len()
            || reduced.terminals.len() != pass_terminals.len()
            || next_offset > 1e-9;
        // Cap the first search so an unproved-but-improved incumbent still
        // leaves time for the second tightening pass to exploit it — **while
        // there is evidence that a second pass has anything to exploit it with**.
        //
        // # What the reservation buys, and when it buys nothing
        //
        // Half of pass 0's window is held back for pass 1. Pass 1 differs from
        // pass 0 in exactly one respect: it hands the reduction a better cutoff.
        // So the reservation buys one thing — a second reduction under a tighter
        // incumbent — and a tightening that returned *the graph it was handed*,
        // with no vertex removed, no edge removed and nothing contracted, has just
        // measured that the reduction is not the stage that is paying here.
        //
        // That is not a small effect and it is not hypothetical. On PACE
        // instance094 the pass-0 tightening spends 2.23 s of five and reports
        // `kill 0n/0e`; the pass-1 tightening spends another 0.75 s and reports
        // `kill 0n/0e` again; and the branch-and-cut — the only stage moving the
        // bound on this instance, at about a million units a second — is handed
        // 1.53 s and then 0.49 s, of which roughly 1.3 s goes into *building its
        // model*, twice. instance087 and instance095 are the same shape.
        //
        // # Why this is a statement about the instance and not about five seconds
        //
        // The condition is "the reduction changed nothing", which is a fact about
        // the graph and the reduction operator. It fires identically at one second
        // and at a thousand: at a larger budget the reduction still either moves
        // the graph or does not, and when it does the reservation is still made.
        // It is also self-correcting in the direction SS98 requires — a reduction
        // that *is* working keeps its successor's window, exactly as the
        // branch-and-cut keeps its share until it has been seen to lose the
        // comparison.
        //
        // # What it costs when it is wrong
        //
        // A second pass whose reduction *would* have fired under the better
        // cutoff loses its chance. The trade is measured rather than assumed: the
        // stage that gains the seconds is the one whose rate was measured on this
        // instance in this call, and the stage that loses them measured zero.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let pass_deadline = if pass == 0 && reduction_moved {
            Instant::now() + remaining.mul_f64(0.5)
        } else {
            deadline
        };
        if config.verbose {
            eprintln!(
                "[time] pass {pass}: tighten {}took {:.2}s and {}, search gets {:.2}s, \
                 elapsed {:.2}s",
                if reused_here { "(reused fixpoint) " } else { "" },
                tighten_secs,
                if reduction_moved {
                    "moved the graph, so a window is reserved for a second pass"
                } else {
                    "returned the graph it was handed, so no window is reserved"
                },
                pass_deadline.saturating_duration_since(Instant::now()).as_secs_f64(),
                start.elapsed().as_secs_f64(),
            );
        }
        // `finish` reports for `pass_graph`; `carried_offset` puts it back on the
        // scale of the graph the loop started with, which is what `best` holds.
        let mut outcome = finish(
            reduced,
            &config,
            start,
            pass_deadline,
            &mut search_cache,
            &mut sep_cache,
            &mut carried_lower_bound,
            &mut branch_and_cut_works,
            &mut td_truncated,
            &mut search_rate,
            &mut carried_witness,
            carried_primal_witnessed,
        );
        // What the next pass may inherit: this pass reported a primal, and it is
        // exhibited exactly when the pass either witnessed its own bound or was
        // handed a witnessed one. `Feasible` outcomes carry the same evidence —
        // `exact_report` only downgrades the *proof*, not the tree.
        //
        // A pass that *exhibited its own tree* is witnessed whatever it inherited:
        // `carried_witness` is set only from a solution `verify_solution` accepted
        // and `Witness::verify` then re-derived from the graph's own edge list. It
        // is the one case the inherited flag used to lose, because the flag is a
        // statement about the bound the reduction carried and not about the tree
        // the branch-and-cut found.
        carried_primal_witnessed =
            (witnessed_here || carried_witness.is_some()) && outcome.primal_bound.is_finite();
        outcome.primal_bound += carried_offset;
        outcome.dual_bound += carried_offset;
        // Both bounds are valid for the same instance, so keep the better of
        // each. A pass that fails to improve the incumbent can still have
        // pushed the dual bound up, and discarding that would throw away the
        // only progress it made.
        best = Some(match best {
            None => outcome,
            Some(b) => merge(b, outcome, config.gap_tolerance.max(1e-6)),
        });
        let done = best.as_ref().map(|b| b.status == SolveStatus::Optimal).unwrap_or(false);
        if done || Instant::now() >= deadline {
            break;
        }
        let Some(b) = best.as_ref() else { break };
        if !b.primal_bound.is_finite() || b.primal_bound >= incoming_ub + carried_offset {
            break;
        }
        pass_graph = next_graph;
        pass_terminals = next_terminals;
        carried_offset += next_offset;
        // Restated for the graph the next pass will run on.
        incoming_ub = b.primal_bound - carried_offset;
        // The separation's certified dual, if the model it came from is the
        // graph the next pass will actually run on. The test is `applies_to`'s —
        // same arcs, same costs, same root, same terminals — an equality and not
        // a hash, because a false positive would price the wrong arcs.
        //
        // It is stated on the reduced graph's scale, which is the scale the next
        // pass tightens in, so no rebasing is needed or applied.
        carried_dual = sep_cache.as_ref().and_then(|s| {
            let directed = DirectedGraph::from_undirected(&pass_graph);
            let root = *pass_terminals.first()?;
            s.applies_to(&directed, root, &pass_terminals).then(|| s.arc_dual()).flatten()
        });
        // The fixpoint survives into the next pass exactly when that pass would
        // start it from the same graph with an upper bound no better than the one
        // it converged under — and now, with a **dual** no stronger than the one
        // it converged under either.
        //
        // The second half is the same argument as the first. Elimination power is
        // `UB - LB`, so a pass handed a better `LB` and its arc prices is handed
        // new information exactly as a pass handed a better `UB` is, and reusing
        // the old fixpoint discards it: on instance083 the second pass reported
        // the ascent's 3,100,512 while the cut loop was holding 3,100,519 for the
        // same graph, because `tighten` never ran.
        //
        // The test is on the dual's own value against the fixpoint's, both stated
        // on the reduced graph. A dual no stronger buys nothing that would restart
        // the fixpoint, and §39's saving is kept in that case.
        let dual_is_stronger = carried_dual
            .as_ref()
            .is_some_and(|d| d.value > reused_lower_bound + 1e-9);
        reuse = reusable
            .filter(|(_, ub, _)| incoming_ub >= ub - 1e-9)
            .filter(|_| !dual_is_stronger)
            .map(|(r, _, _)| r);
        // `finish` already restated `carried_lower_bound` for the graph it ran
        // on, which is the graph the next pass is handed. Nothing to rebase here;
        // see the proposition at the top of `finish`.
        if pass_terminals.len() < 2 {
            break;
        }
    }

    let mut result =
        best.unwrap_or_else(|| trivial_result(start, Cost::INFINITY, SolveMethod::AscendAndPrune));
    result.primal_bound += base_offset;
    result.dual_bound += base_offset;
    // The gap is relative, so it has to be recomputed once both bounds are back
    // on the original instance's scale: contracting `base_offset` out of the
    // graph shrinks the denominator and inflates the reported percentage.
    result.gap_pct = if result.primal_bound.is_finite() && result.dual_bound > f64::NEG_INFINITY {
        (((result.primal_bound - result.dual_bound) / result.primal_bound.abs().max(1e-10)) * 100.0)
            .max(0.0)
    } else {
        100.0
    };
    result.time_secs = start.elapsed().as_secs_f64();
    result
}

/// Combine two solve outcomes for the same instance: best primal, best dual.
fn merge(a: SolveResult, b: SolveResult, tolerance: Cost) -> SolveResult {
    let (primal_from, other) = if b.primal_bound < a.primal_bound { (b, a) } else { (a, b) };
    let mut out = primal_from;
    // A dual bound above a known feasible value is a contradiction: one of the
    // two is wrong. Clamping is the sound direction — the primal is achieved by
    // an actual tree — but it must never be how a proof gets manufactured, which
    // is why the status below is recomputed from the clamped numbers and not
    // inherited.
    debug_assert!(
        other.dual_bound <= out.primal_bound + 1e-6 || !out.primal_bound.is_finite(),
        "dual bound {} exceeds a feasible primal {}",
        other.dual_bound,
        out.primal_bound
    );
    out.dual_bound = out.dual_bound.max(other.dual_bound).min(out.primal_bound);
    out.nodes_processed += other.nodes_processed;
    out.cuts_added += other.cuts_added;
    out.lp_solves += other.lp_solves;
    out.gap_pct = if out.primal_bound.is_finite() && out.dual_bound > f64::NEG_INFINITY {
        (((out.primal_bound - out.dual_bound) / out.primal_bound.abs().max(1e-10)) * 100.0).max(0.0)
    } else {
        100.0
    };
    if out.primal_bound.is_finite() && out.dual_bound >= out.primal_bound - tolerance {
        out.status = SolveStatus::Optimal;
        out.gap_pct = 0.0;
    } else if out.status == SolveStatus::Optimal {
        // The surviving status came from whichever pass had the better primal;
        // it says nothing about the merged bounds.
        out.status = SolveStatus::Feasible;
    }
    out
}

/// Finish a tightened instance: exact DP when cheap, otherwise branch-and-cut.
/// Report an exact value obtained on the reduced graph.
///
/// `value` is the proved optimum of that graph, so `value + offset` is the cost
/// of a tree of the instance the tightening was handed — the contraction lemma
/// lifts it. `root_upper_bound` may be lower, which happens exactly when the
/// bound-based reductions removed the trees attaining it; that is legitimate and
/// is why the minimum is taken.
///
/// It is legitimate *given a real tree for `root_upper_bound`*. Without one the
/// two numbers disagree with no way to decide between them, so nothing is
/// claimed proved: the primal is still the better of the two — both are upper
/// bounds however the disagreement resolves — and the dual falls back to what
/// was actually certified.
#[allow(clippy::too_many_arguments)]
fn exact_report(
    value: Cost,
    root_upper_bound: Cost,
    root_lower_bound: Cost,
    ub_witnessed: bool,
    offset: Cost,
    start: Instant,
    method: SolveMethod,
) -> SolveResult {
    // Without a tree for `root_upper_bound` it is a cutoff and nothing more, so
    // it may not appear in a *primal* position: a primal bound is a claim that
    // some tree achieves it. `value` always may — every tree of the reduced
    // graph is a tree of the original, and the contraction lemma adds `offset`.
    let best = if ub_witnessed { value.min(root_upper_bound) } else { value };
    let proved = ub_witnessed || value <= root_upper_bound + 1e-9;
    let dual = if proved { best } else { root_lower_bound.min(best) };
    SolveResult {
        status: if proved { SolveStatus::Optimal } else { SolveStatus::Feasible },
        primal_bound: best + offset,
        dual_bound: dual + offset,
        gap_pct: if proved {
            0.0
        } else {
            ((best - dual) / best.abs().max(1e-10) * 100.0).max(0.0)
        },
        nodes_processed: 0,
        cuts_added: 0,
        lp_solves: 0,
        time_secs: start.elapsed().as_secs_f64(),
        verified: true,
        method,
    }
}

/// A tree the branch-and-cut exhibited, restated as a [`Witness`] of the graph
/// it ran on.
///
/// # Why this is the only tree the loop may forward
///
/// [`ReduceConfig::initial_witness`] is a claim that the bound handed in is the
/// cost of a tree **of the graph handed in**. A `Reduced`'s own witness does not
/// satisfy that for the *next* pass: it is stated on some ancestor graph, and the
/// contraction lemma lifts a tree of a descendant to an ancestor, never the other
/// way. Forwarding it would assert that the shrunken graph still attains a bound
/// the eliminations may have removed the trees for, which is exactly SS61's
/// failure. The branch-and-cut's solution is different in kind: it is a tree of
/// `work_graph` itself, found on `work_graph`, and `work_graph` is precisely the
/// graph the next pass tightens.
///
/// Nothing is taken on trust from the arc numbering. `DirectedGraph::from_undirected`
/// emits the two arcs of edge `i` at `2i` and `2i+1`, so the map is `a / 2`; the
/// witness is then re-verified against the graph's own edge list and its own
/// terminals, and is discarded unless the recomputed cost is the claimed one.
fn witness_from_arcs(
    graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    arcs: &[u32],
    value: Cost,
) -> Option<Witness> {
    let mut edges: Vec<u32> = arcs.iter().map(|&a| a / 2).collect();
    edges.sort_unstable();
    edges.dedup();
    let w = Witness {
        graph: graph.clone(),
        terminals: terminals.to_vec(),
        edges,
        cost: value,
        offset: 0.0,
    };
    let c = w.verify()?;
    ((c - value).abs() < 1e-6).then_some(w)
}

fn finish(
    reduced: crate::root_reduce::Reduced,
    config: &SolverConfig,
    start: Instant,
    deadline: Instant,
    search_cache: &mut Option<SteinerSearch>,
    sep_cache: &mut Option<RootSeparation>,
    carried_lower_bound: &mut Cost,
    branch_and_cut_works: &mut bool,
    td_truncated: &mut Option<(usize, usize, usize, f64)>,
    search_rate: &mut Cost,
    // A tree this pass exhibited on the graph the next pass will tighten. See
    // [`witness_from_arcs`].
    carried_witness: &mut Option<Witness>,
    // Whether the bound this pass started from was itself exhibited by an
    // earlier pass. A pass that never improves the incumbent inherits its
    // witness from the pass that found it, and inherits nothing when there was
    // none.
    carried_primal_witnessed: bool,
) -> SolveResult {

    if config.verbose {
        eprintln!(
            "[reduce] after {} rounds: |V|={} |E|={} |R|={} LB={:.1} UB={:.1} offset={:.1}",
            reduced.rounds,
            reduced.graph.num_nodes,
            reduced.graph.edges.len(),
            reduced.terminals.len(),
            reduced.lower_bound,
            reduced.upper_bound,
            reduced.offset,
        );
    }

    // Everything below is stated for `reduced.graph`; this puts the contracted
    // cost back on at each exit.
    let offset = reduced.offset;

    // `carried_lower_bound` arrives stated for the graph that was handed to
    // `tighten`, and leaves stated for `reduced.graph` — which is the graph the
    // next pass will be handed. The rebase happens exactly here, once, and the
    // caller does not repeat it.
    //
    // > **Proposition (the rebase is valid).** If `L <= OPT(G_in)` then
    // > `L - offset <= OPT(reduced.graph)`.
    // >
    // > *Proof.* `tighten` reaches `reduced.graph` from `G_in` by deletions and
    // > by contractions charging exactly `offset`, and the contraction lemma
    // > gives `OPT(G_in) = OPT(reduced.graph) + offset` whenever an optimum
    // > survives — which is the invariant `tighten` maintains against its own
    // > cutoff. So `L - offset <= OPT(G_in) - offset = OPT(reduced.graph)`. ∎
    //
    // Before this was written down the same number was rebased *twice*: the
    // hypergraphic certificate wrote a bound stated for `reduced.graph` and the
    // caller then subtracted `offset` from it again, and the pass after that
    // compared a bound on one graph's scale against a bound on another's. The
    // first error only lost strength; the second is the direction that can
    // over-claim, and it was reachable exactly when a later pass contracted more
    // than an earlier one. Both are closed by having one place that owns the
    // scale.
    *carried_lower_bound = (*carried_lower_bound - offset).max(0.0);

    // Can `upper_bound` be *exhibited*?
    //
    // This is the question §61 leaves open, and it is not rhetorical: `finish`
    // reports `primal = dual = root_upper_bound` on several paths, and on PACE
    // Track 1's instance184 — under a primal heuristic since reverted — it
    // reported `Optimal 3404` against a reference of 3399. The number came from
    // a bound the loop had carried across shrinks with nobody left holding a tree
    // for it.
    //
    // [`Reduced::verify_witness`] answers it by recomputing a stored tree's cost
    // from the graph that tree is stated in, and the invariant proved there says
    // the answer is `upper_bound + offset` exactly when the bound is honest. A
    // pass that inherited its bound from an earlier one inherits that pass's
    // answer, which was gated here in the same way.
    //
    // What the flag gates is only the *claim of achievement*. It never changes a
    // cutoff, never discards a bound, and never touches the reduction — the
    // second of §61's two failed repairs did all three, and produced three wrong
    // answers of its own.
    let ub_witnessed = reduced.upper_bound_is_witnessed() || carried_primal_witnessed;
    if config.verbose && reduced.upper_bound.is_finite() && !ub_witnessed {
        eprintln!(
            "[witness] upper bound {:.1} has no tree behind it; \
             optimality will not be claimed on it alone",
            reduced.upper_bound + offset
        );
    }

    if reduced.proved_optimal(config.gap_tolerance.max(1e-6)) && ub_witnessed {
        let value = reduced.upper_bound + offset;
        return SolveResult {
            status: SolveStatus::Optimal,
            primal_bound: value,
            dual_bound: value,
            gap_pct: 0.0,
            nodes_processed: 0,
            cuts_added: 0,
            lp_solves: 0,
            time_secs: start.elapsed().as_secs_f64(),
            verified: true,
            method: SolveMethod::AscendAndPrune,
        };
    }

    let work_graph = reduced.graph;
    let terminals = reduced.terminals;
    let root = reduced.root;

    let root_lower_bound = reduced.lower_bound;
    let root_upper_bound = reduced.upper_bound;
    let incumbent_arcs = reduced.incumbent_arcs;

    // Goal-directed exact search on the reduced instance.
    //
    // This is where the incumbent finally pays for itself: the search prunes
    // every label whose own cost plus a lower bound on the rest already exceeds
    // it, so a tight upper bound collapses the state space rather than merely
    // bounding the answer. It is attempted whenever the terminal set is
    // addressable, and it bounds and abandons itself rather than being gated on
    // a guess about how long it will take.
    //
    // An abandoned run is not wasted: its frontier is a valid lower bound on the
    // optimum of `work_graph`, derived combinatorially, and it is fed to the
    // branch-and-cut below as a seed.
    // Anything an earlier pass proved about this instance is still true of it.
    let mut search_lower_bound = root_lower_bound.max(*carried_lower_bound);
    if terminals.len() >= 2 {
        run_search(
            &work_graph,
            &terminals,
            root_lower_bound,
            root_upper_bound,
            config,
            deadline,
            *branch_and_cut_works,
            search_cache,
            sep_cache,
            &mut search_lower_bound,
            search_rate,
        );
        // Everything the search and the certificate loop proved is a lower bound
        // on `work_graph`'s optimum, which is the scale the next pass tightens
        // in. Carrying it is the dual half of the loop: elimination power is
        // exactly `UB - LB`, so a pass handed a better `LB` deletes more, and a
        // pass that re-derives its own weaker ascent instead throws the
        // difference away. See the writeback after the branch-and-cut for the
        // case that measures largest.
        #[cfg(test)]
        if search_lower_bound > *carried_lower_bound + 1e-9 {
            probe::CARRIED_BOUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        *carried_lower_bound = carried_lower_bound.max(search_lower_bound);
        if let Some(value) = search_cache.as_ref().and_then(|s| s.optimum()) {
            // The search runs on a graph that keeps only trees at or below the
            // incumbent, so the incumbent still wins ties.
            return exact_report(
                value,
                root_upper_bound,
                root_lower_bound,
                ub_witnessed,
                offset,
                start,
                SolveMethod::DreyfusWagner,
            );
        }
    }

    // The width-parameterised exact finish.
    //
    // Every other exact route in this solver is exponential in the *terminal
    // count*: Dreyfus-Wagner is `3^k`, Dijkstra-Steiner is `2^k` and cannot
    // address more than 64 terminals at all. That leaves a whole class of
    // instance unsolvable in principle rather than in practice — a graph of
    // small treewidth with hundreds of terminals — and the class is not
    // exotic: on PACE Track 2 the reduced instances decompose at width 4 to 23
    // while carrying up to 2,284 terminals, and six of the first sixty are
    // unproved at five seconds for exactly this reason. The dynamic programme
    // in [`crate::graph::algorithms::steiner_td`] is indifferent to how many
    // terminals there are, so it closes them outright: 638 terminals at width
    // six in 0.06 s.
    //
    // It is attempted before anything else because when it works it is a
    // complete proof and it is cheap, and refused before anything else when it
    // cannot: the gate is a *minimum-degree* elimination ordering at the
    // encoding's own width limit, which aborts at the first oversized bag. On
    // every SteinLib series and on all of PACE Track 1 that abort takes under
    // ten milliseconds and the whole step costs nothing, because those
    // instances decompose at width 25 to 84. Only when the cheap ordering
    // proves the graph narrow is the slower minimum-fill ordering run to
    // sharpen it.
    let td_shape = (work_graph.num_nodes as usize, work_graph.edges.len(), terminals.len());
    let td_window = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
    let td_repeats = td_truncated
        .map(|(n, e, t, granted)| (n, e, t) == td_shape && td_window <= granted + 1e-9)
        .unwrap_or(false);
    if td_repeats {
        if config.verbose {
            eprintln!(
                "[td] skipped: the same graph was already given {:.2}s and was cut off;                  {td_window:.2}s cannot get further",
                td_truncated.map(|x| x.3).unwrap_or(0.0)
            );
        }
    } else if let Some((value, secs)) = {
        let (out, truncated) = try_decomposition(&work_graph, &terminals, deadline);
        if truncated {
            *td_truncated = Some((td_shape.0, td_shape.1, td_shape.2, td_window));
        }
        out
    } {
        if config.verbose {
            eprintln!("[td] exact by tree decomposition: {value:.1} in {secs:.2}s");
        }
        return exact_report(
            value,
            root_upper_bound,
            root_lower_bound,
            ub_witnessed,
            offset,
            start,
            SolveMethod::TreeDecomposition,
        );
    }


    // The hypergraphic relaxation, when its subset table is affordable and the
    // search has already been shown not to need the budget.
    //
    // This is a *different* relaxation, not a strengthening of the bidirected cut
    // one, and where it fits it can be dramatically stronger: PACE instance024 has
    // 640 vertices, 204,454 edges and nine terminals after reduction, and its dual
    // certifies 1,756 — the optimum — in 0.17 s, against 1,752 from the dual
    // ascent and 1,752 from a twenty-second cut loop that manages eighteen solves
    // on a graph that dense.
    //
    // It runs *after* the goal-directed search rather than before it, for the
    // reason the certificate loop already runs late: on 024 and 025 the binding
    // constraint is the primal, not the dual — the heuristic reaches 1,757 against
    // a true 1,756 — and the search is what closes them. Given the budget first,
    // the certificate took that budget, proved a bound nobody needed, and cost
    // instance025 its proof on three runs out of three.
    //
    // The bound is taken as a maximum with the others and never added to them;
    // see [`crate::model::hypergraphic`] for why its state potential is not handed
    // to the search at all.
    if *carried_lower_bound <= 0.0 {
        let hyp_units = hyp_work(terminals.len(), work_graph.num_nodes, work_graph.edges.len());
        let hyp_secs = hyp_units / HYP_UNITS_PER_SECOND;
        let budget = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
        // An attempt that runs out of clock costs its budget and returns nothing,
        // so the decision comes from the estimate before the work starts. The
        // deadline is still passed, at three times the estimate, so a mis-estimate
        // cannot run away.
        if hyp_units <= HYP_WORK_CEILING && hyp_secs * 2.0 <= budget {
            if let Some(h) = hyp_certificate(
                &work_graph,
                &terminals,
                Some(Instant::now() + std::time::Duration::from_secs_f64(hyp_secs * 3.0)),
            ) {
                if config.verbose {
                    eprintln!(
                        "[hyp] bound {:.1} over {} partitions (ascent {:.1})",
                        h.lower_bound,
                        h.partitions.len(),
                        root_lower_bound
                    );
                }
                search_lower_bound = search_lower_bound.max(h.lower_bound);
                *carried_lower_bound = carried_lower_bound.max(h.lower_bound);
            } else if config.verbose {
                eprintln!("[hyp] no certificate");
            }
        } else if config.verbose {
            eprintln!(
                "[hyp] skipped: {} terminals, {} nodes, {} edges, {:.2}s estimated against {:.2}s",
                terminals.len(),
                work_graph.num_nodes,
                work_graph.edges.len(),
                hyp_secs,
                budget,
            );
        }
    }
    if search_lower_bound >= root_upper_bound - config.gap_tolerance.max(1e-6)
        && root_upper_bound.is_finite()
        // The path §61 names: the frontier reaches the incumbent and the
        // incumbent is announced as proved, with nothing between the claim and a
        // number. Without a tree for that number the claim is not made, and the
        // branch-and-cut below gets the rest of the budget instead.
        && ub_witnessed
    {
        return SolveResult {
            status: SolveStatus::Optimal,
            primal_bound: root_upper_bound + offset,
            dual_bound: root_upper_bound + offset,
            gap_pct: 0.0,
            nodes_processed: 0,
            cuts_added: 0,
            lp_solves: 0,
            time_secs: start.elapsed().as_secs_f64(),
            verified: true,
            method: SolveMethod::AscendAndPrune,
        };
    }
    let root_lower_bound = search_lower_bound;
    let directed = DirectedGraph::from_undirected(&work_graph);
    let mut solver = BranchAndCutSolver::new(directed.clone(), root, terminals.clone());
    let remaining = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
    solver.config = SolverConfig { time_limit_secs: remaining, ..config.clone() };
    solver.seed_bounds(root_lower_bound, root_upper_bound);
    // The incumbent's arc numbering matches `work_graph` only when it survived
    // the last shrink; `tighten` clears it otherwise, so this is always safe.
    if let Some(arcs) = incumbent_arcs {
        solver.seed_incumbent(arcs);
    }

    let bnc_started = Instant::now();
    let (solution, stats) = solver.solve();
    let bnc_secs = bnc_started.elapsed().as_secs_f64();

    let mut verified = false;
    // A primal bound is a claim that some tree achieves it, so an unwitnessed
    // `root_upper_bound` may not start one. The branch-and-cut's own solution is
    // checked by `verify_solution` and may.
    let mut primal = if ub_witnessed { root_upper_bound } else { Cost::INFINITY };
    if let Some(ref sol) = solution {
        let vr = verify_solution(&directed, root, &terminals, sol);
        verified = vr.is_valid;
        if verified && sol.objective_value < primal {
            primal = sol.objective_value;
            // The tree that improved the incumbent, carried with the graph it is
            // a tree *of* — which is the graph the next pass is handed. This is
            // the primal half of the loop: without it the next reduction is given
            // a number and told to take it on faith, and SS61 is the record of what
            // that costs.
            *carried_witness = witness_from_arcs(&work_graph, &terminals, &sol.arcs, primal);
            #[cfg(test)]
            if carried_witness.is_some() {
                probe::CARRIED_WITNESSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
    if !primal.is_finite() {
        verified = false;
    } else if solution.is_none() {
        // The incumbent came from the heuristic during ascend-and-prune; it was
        // built and pruned to a tree by construction.
        verified = true;
    }

    // The branch-and-cut runs on a graph that only retains solutions cheaper than
    // `root_upper_bound`, so its dual bound proves nothing above that value.
    //
    // An infeasible search is the strongest outcome available here rather than an
    // error: reduced-cost elimination deletes everything that cannot appear in a
    // solution *strictly cheaper than the incumbent*, so running out of feasible
    // solutions is exactly the proof that the incumbent is optimal.
    let integral = costs_are_integral(directed.arcs.iter().map(|a| a.cost));
    // "No solution cheaper than the incumbent" proves the incumbent optimal only
    // if the incumbent exists.
    let dual = if stats.status == SolveStatus::Infeasible && primal.is_finite() && ub_witnessed {
        primal
    } else {
        tighten_dual(stats.dual_bound.max(root_lower_bound), integral).min(primal)
    };
    let gap_pct = if primal.is_finite() && dual > f64::NEG_INFINITY {
        ((primal - dual) / primal.abs().max(1e-10)) * 100.0
    } else {
        100.0
    };

    // What the branch-and-cut proved, handed to the pass that tightens next.
    //
    // # The measurement this closes
    //
    // On PACE instance094 the first pass's branch-and-cut takes the dual from
    // 102,550,329 to 104,033,839 in 1.53 s. The second pass then re-derives the
    // bound from scratch — no pass has ever written one down — and its own ascent
    // reports 102,516,601, which is *below* where the previous pass finished. The
    // second branch-and-cut is seeded with that weaker number and spends its 0.49 s
    // climbing back to 103,680,514, and the 1.5 million units the first pass
    // proved are re-proved rather than used. The reduction in between runs at a
    // gap of 2.4 % and deletes nothing, which is exactly SS50's thesis read
    // backwards: the reduction is starved because nobody hands it the bound that
    // has already been proved.
    //
    // # Why it is a valid bound for the graph the next pass tightens
    //
    // > **Proposition.** Let `U` be the cutoff `work_graph` was reduced under and
    // > let `U` be *witnessed*. Then `dual <= OPT(work_graph)`.
    // >
    // > *Proof.* The branch-and-cut runs on `work_graph` minus arcs its own
    // > reduced-cost fixing proved absent from every tree of cost `< U`; call that
    // > `R`. So either `OPT(work_graph) < U`, in which case an optimal tree
    // > survives and `OPT(R) = OPT(work_graph)`; or `OPT(work_graph) >= U`, and
    // > since `U` is witnessed there is a tree of `work_graph` of cost `U`, so
    // > `OPT(work_graph) = U`. In the first case `dual <= stats.dual_bound <=
    // > OPT(R) = OPT(work_graph)`. In the second, `dual <= primal <= U =
    // > OPT(work_graph)`, because a witnessed `U` is admitted into `primal`. ∎
    //
    // The witness hypothesis is not decoration. Without it `primal` is the
    // branch-and-cut's own tree, which is a tree of `R` and may cost more than
    // `U`; then `dual <= OPT(R)` is all that is available and `OPT(R)` may exceed
    // `OPT(work_graph)`. That is SS61's shape, and the bound is simply not carried
    // in that case rather than being carried with a hope.
    if ub_witnessed {
        #[cfg(test)]
        if dual > *carried_lower_bound + 1e-9 {
            probe::CARRIED_BOUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            probe::CARRIED_BNC_BOUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        *carried_lower_bound = carried_lower_bound.max(dual);
    }

    // Whether the branch-and-cut earns its half of the next window, for the next
    // pass to act on.
    //
    // This used to read `lp_solves > 0 || nodes_processed > 0`, which measures
    // *activity* and not progress, and the difference is half the budget on the
    // instances where it matters. On PACE instance167 the branch-and-cut solves
    // twelve LPs, opens one node, and moves the dual bound by a single unit in
    // 1.06 s, while the goal-directed search it took the second off was moving
    // it by about six units a second — and on the strength of "it did something"
    // it keeps taking half of every subsequent search window.
    //
    // The comparison that means something is between the two stages' *observed
    // rates of dual improvement*, both measured on this instance, in this pass,
    // in the same units of bound per second. Neither is estimated and neither is
    // a clock fraction: each stage is timed doing the thing it is being asked to
    // keep doing.
    //
    // The measurement is one-directional and self-correcting: it is taken after
    // the run, so the branch-and-cut always gets its share until it has been
    // seen to lose the comparison. SteinLib c18, where it closes the instance in
    // 0.38 s after the search fails, keeps its share because a completed proof
    // wins the comparison outright.
    let bnc_rate = if bnc_secs > 1e-9 { (dual - root_lower_bound).max(0.0) / bnc_secs } else { 0.0 };
    *branch_and_cut_works = matches!(stats.status, SolveStatus::Optimal | SolveStatus::Infeasible)
        || primal < root_upper_bound - 1e-6
        || bnc_rate >= *search_rate;
    if config.verbose {
        eprintln!(
            "[B&C] dual {:.1} -> {:.1} in {:.2}s = {:.2}/s against the search's {:.2}/s:              {} its share of the next window",
            root_lower_bound,
            dual,
            bnc_secs,
            bnc_rate,
            search_rate,
            if *branch_and_cut_works { "keeps" } else { "loses" },
        );
    }

    // `Optimal` is reported if and only if the bounds being reported prove it.
    //
    // The status must not be an independent flag that can drift away from the
    // numbers beside it. It did drift: the search could leave a node unfinished,
    // read the resulting empty queue as an exhausted tree, and return `Optimal`
    // alongside a dual bound several percent below the primal — PACE
    // instance200 was announced as a proved 6491 against a true optimum of 6393.
    // This is the last line of defence, and it is a cheap one.
    let proved = primal.is_finite() && dual >= primal - config.gap_tolerance.max(1e-6);
    let status = if proved {
        SolveStatus::Optimal
    } else if stats.status == SolveStatus::Optimal {
        SolveStatus::Feasible
    } else {
        stats.status
    };

    SolveResult {
        status,
        primal_bound: primal + offset,
        dual_bound: dual + offset,
        gap_pct: gap_pct.max(0.0),
        nodes_processed: stats.nodes_processed,
        cuts_added: stats.cuts_added,
        lp_solves: stats.lp_solves,
        time_secs: start.elapsed().as_secs_f64(),
        verified,
        method: SolveMethod::BranchAndCut,
    }
}

/// Labels in the first slice of the search's own doubling schedule.
///
/// This is a *granularity*, not a tuning dial, and the distinction is what keeps
/// [`potential_will_not_close`] honest. The schedule doubles, so whatever the
/// right moment to re-decide is, a doubling schedule reaches a slice boundary
/// within a factor of two of it and has spent at most twice the labels getting
/// there. Any starting value has that property; this one is the search's own
/// deadline-polling granularity, so a slice is never shorter than the interval
/// at which the search already checks its clock.
const SEARCH_SLICE_LABELS: u64 = 4096;

/// Whether the potential the search is running under will fail to close the
/// instance inside the budget it has left.
///
/// # The measurement
///
/// A* under a valid potential `h` settles labels in nondecreasing `g + h`, and
/// it terminates when it pops the goal state, whose key is the optimum. So the
/// whole run is a march of the frontier key from zero to `OPT <= UB`, and the
/// only question is how many labels sit in the interval that is left.
///
/// Two quantities are read off the search's own trace over the slice just run:
///
/// ```text
/// rate  = (frontier_after - frontier_before) / labels_in_slice     [bound/label]
/// speed = labels_in_slice / seconds_in_slice                       [label/second]
/// ```
///
/// and two are known: the remaining gap `UB - frontier_after` and the remaining
/// seconds. The projection is
///
/// ```text
/// labels_needed    = (UB - frontier) / rate
/// labels_available = speed * seconds_left
/// ```
///
/// and the predicate is `labels_needed > labels_available`.
///
/// # What it does and does not claim
///
/// It is an *estimate of the schedule*, and it is stated as one. Label density
/// per unit of key is not constant — it generally rises, because the number of
/// states within reach grows with the key — so `labels_needed` is optimistic and
/// the predicate fires later than a perfect oracle would. In the other direction
/// it targets `UB` rather than `OPT`, which is pessimistic. Neither error is
/// bounded and neither needs to be, because of what the predicate is allowed to
/// do:
///
/// > **Proposition (scheduling cannot change an answer).** Whatever this returns,
/// > the search's completed answer is unchanged.
/// >
/// > *Proof.* Its only effect is whether a further packing is built and offered
/// > to the search. A packing is offered through
/// > [`SteinerSearch::add_packing`], which is sound for *any* valid packing by
/// > the resumption theorem on [`SteinerSearch`], and every packing this solver
/// > can produce is verified against (PACK) before it is offered. The set of
/// > labels the search must settle to reach the goal state is determined by the
/// > graph and the cutoff, not by the potential; the potential determines only
/// > the order. So a search that reaches the goal state reaches it with the same
/// > `g`, and a search that does not reports a frontier maximum, which is a valid
/// > lower bound under any valid potential. ∎
///
/// It may also *refuse*: `rate > 0` and a projection that fits leave the LP
/// unbuilt, which is exactly what protects the instances where the cheap
/// potential is enough. On SteinLib c18 and PACE instance024/025 the frontier
/// advances steadily and the projection fits, so nothing is built — the
/// behaviour the old phase order was measured into having, now derived from the
/// instance rather than assumed from the phase number.
///
/// # A frontier that does not move is not evidence that it will not
///
/// A slice over which the frontier stands still yields no rate, and the first
/// version of this predicate read that as an infinite projection and diverted
/// the budget. That is wrong, and it cost a proof: PACE Track 1's instance026
/// has a gap of *one* unit — the frontier sits at 1750 against an incumbent of
/// 1751 — and the search pops the goal state at 23,640 labels. Diverting at
/// 8,192 because it had not moved yet lost an instance the ascent packing closes
/// outright.
///
/// The honest reading of a stall is the one the same argument gives. If the
/// frontier has stood still for `M` labels, the observation supports exactly one
/// statement about how many more are needed: **at least `M`**, since `M` have
/// already been spent without moving it. So a stall diverts the budget only when
/// `M` already exceeds what the remaining budget can settle — when the search
/// has spent more labels failing to move the frontier than it has left to spend
/// at all. The doubling schedule makes that condition arrive on a stalled run
/// and never on a run that is about to finish.
/// Is another batch of separation on course to close this instance in time?
///
/// # The question the one-step test could not ask
///
/// The repayment test above asks whether the *last* batch paid for itself. That
/// is the right question for a linear return and the wrong one for this curve:
/// the measured investment on PACE instance083 is
///
/// ```text
///   0.25 s   4 solves   packing 3,100,514.3   search fails
///   0.5  s   6 solves   packing 3,100,516.8   search 2.72 s
///   1    s   8 solves   packing 3,100,518.1   search 1.79 s
///   2    s  14 solves   packing 3,100,519.3   search 0.75 s
///   4    s  26 solves   packing 3,100,526.7   search 0.12 s
/// ```
///
/// Every LP second roughly halves the search, so each *individual* step looks
/// marginal while the sequence closes the instance. What has to be projected is
/// the end of the sequence, and both halves of the projection are observable.
///
/// # The projection
///
/// Two quantities are measured on this instance in this pass, over the batches
/// this call has already funded:
///
/// - **the separation's rate**, `dp/ds`, the packing value gained per second of
///   separation, taken over all batches so far;
/// - **the search's response**, how its frontier rate answers a change in the
///   packing value.
///
/// The response is modelled as *log-linear*, `rate(p) = rate_0 e^{beta (p-p_0)}`,
/// because that is the shape the table above has — a constant factor per unit of
/// packing rather than a constant increment — and `beta` is estimated from the
/// observed pairs by the total change across the batches. With `beta` in hand,
/// the frontier rate needed to close the remaining gap `U - f` in the time left
/// after `s` further seconds of separation is `(U - f)/(T - s)`, and the packing
/// value that delivers it is
///
/// ```text
///   p_needed = p + ln( (U - f) / ((T - s) * rate) ) / beta,
/// ```
///
/// which costs `s = (p_needed - p) / (dp/ds)` seconds to reach. The two are
/// coupled, so the predicate simply *scans* the batches the doubling schedule
/// would actually buy — `s`, `2s`, `4s`, ... within `T` — and asks whether any
/// of them leaves enough time for the search the projection implies. That is a
/// handful of arithmetic operations over a sequence with at most `log2(T/s)`
/// terms.
///
/// # What it may do
///
/// Only refuse. It gates whether a further batch of separation is funded, and by
/// the proposition on [`potential_will_not_close`] the search's completed answer
/// does not depend on which packings it was given. A wrong projection costs time
/// and can never produce a wrong bound: every packing offered is verified against
/// (PACK) first, and every bound the loop reports is certified from its own
/// multipliers.
///
/// It returns `true` — keep funding — whenever it cannot see far enough to
/// refuse: fewer than two batches (nothing to fit), a degenerate estimate, or a
/// response that is flat but positive. Refusal is the exception and has to be
/// earned.
fn separation_route_is_worth_continuing(
    batches: &[(Cost, f64, f64, f64)],
    packing_value: Cost,
    frontier: Cost,
    upper_bound: Cost,
    rate_now: f64,
    horizon_secs: f64,
) -> bool {
    if batches.len() < 2 || horizon_secs <= 0.0 || !upper_bound.is_finite() {
        return true;
    }
    let gap = upper_bound - frontier;
    if gap <= 0.0 {
        return true;
    }
    // The separation's own rate, over everything this call has funded.
    let gained: Cost = batches.iter().map(|b| b.0).sum();
    let spent: f64 = batches.iter().map(|b| b.1).sum();
    if spent <= 0.0 || gained <= 0.0 {
        // No packing gain at any price: there is nothing for the projection to
        // extrapolate, and the repayment test above owns that case.
        return true;
    }
    let dp_ds = gained / spent;

    // The search's response to it. `beta` is the log-rate change per unit of
    // packing, taken across the whole sequence so that one noisy slice cannot
    // set it.
    let first_rate = batches.first().map_or(0.0, |b| b.2);
    if !(first_rate > 0.0) || !(rate_now > 0.0) {
        // Without two positive rates there is no ratio to fit.
        return true;
    }
    let beta = (rate_now / first_rate).ln() / gained;
    if !(beta > 0.0) || !beta.is_finite() {
        // A response that is flat or negative gives the projection nothing; the
        // repayment test is then the only judge, and it has already run.
        return true;
    }

    // Walk the batches the doubling schedule would buy and ask whether any of
    // them leaves a search that fits.
    let mut s = batches.last().map_or(0.0, |b| b.1) * 2.0;
    let mut total = 0.0;
    while total + s <= horizon_secs {
        total += s;
        let p = packing_value + dp_ds * total;
        let rate = rate_now * (beta * (p - packing_value)).exp();
        let search_secs = gap / rate;
        if total + search_secs <= horizon_secs {
            return true;
        }
        s *= 2.0;
    }
    false
}

fn potential_will_not_close(
    frontier_before: Cost,
    frontier_after: Cost,
    upper_bound: Cost,
    labels_in_slice: u64,
    labels_since_advance: u64,
    slice_secs: f64,
    seconds_left: f64,
) -> bool {
    if !upper_bound.is_finite() || labels_in_slice == 0 || seconds_left <= 0.0 {
        return false;
    }
    let gap = upper_bound - frontier_after;
    if gap <= 0.0 {
        // The frontier has already reached the incumbent; the search is about to
        // finish whatever anyone thinks.
        return false;
    }
    let speed = labels_in_slice as f64 / slice_secs.max(1e-9);
    let labels_available = speed * seconds_left;
    let advance = frontier_after - frontier_before;
    let labels_needed = if advance > 0.0 {
        gap * labels_in_slice as f64 / advance
    } else {
        labels_since_advance as f64
    };
    labels_needed > labels_available
}

/// Advance the goal-directed search, creating it or continuing it.
///
/// The search's whole state — settled labels, open queue, Lemma-15 witnesses —
/// lives in `cache` and survives across attempts *and* across solver passes.
/// That is the point: on PACE 024, 025, 086 and 087 the search settles a few
/// hundred thousand labels per slice and needs roughly their sum, and under the
/// old wiring it was handed four disjoint slices and started each of them from
/// nothing.
///
/// # Scheduling the potential
///
/// The old wiring was two phases: sweep under the ascent packing, and only if
/// that failed, build the LP potential and sweep again. That order was measured
/// in — SteinLib c18 and PACE instance024/025 are closed by the first phase and
/// were lost when the certificate was given the budget first — and it is
/// provably wasted on the opposite group. On PACE instance167 the first phase
/// settles 350,000 labels and moves the frontier by 7 units against a gap of 3,
/// while a quarter-second of separation produces a packing under which the same
/// instance closes in 29,000 labels.
///
/// Neither order is right, so neither is used. The search runs in doubling label
/// slices and, at each slice boundary, asks [`potential_will_not_close`] — a
/// statement about the instance, computed from the frontier's own rate of
/// advance — whether to spend the next of its budget on sweeping or on
/// separation. The separation loop is resumable, so "spend some on separation"
/// is a genuine increment and not a restart, and the answer can be revisited
/// every slice.
#[allow(clippy::too_many_arguments)]
fn run_search(
    work_graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    root_lower_bound: Cost,
    root_upper_bound: Cost,
    config: &SolverConfig,
    deadline: Instant,
    branch_and_cut_works: bool,
    cache: &mut Option<SteinerSearch>,
    sep_cache: &mut Option<RootSeparation>,
    search_lower_bound: &mut Cost,
    search_rate: &mut Cost,
) {
    // The search may be rooted at any terminal, and its potential is a packing
    // rooted at the same one. Which terminal is chosen was measured and does not
    // matter: over the terminals of the instances the search fails to close, the
    // ascent bound spans under 1 % (PACE 086: 3254 to 3286 against an optimum of
    // 3661) and is flat on 085 and 087. The strength that is missing is not
    // root-dependent.
    let directed = DirectedGraph::from_undirected(work_graph);

    // Continue the search from an earlier pass when it is literally the same
    // search: same graph, same terminals. Otherwise start one.
    let mut search = cache.take().filter(|s| s.applies_to(work_graph, terminals));
    let resumed = search.is_some();
    if search.is_none() {
        // The ascent's cut packing becomes the search's potential. This is the
        // whole point of running it here rather than only using its scalar bound:
        // the packing bounds every sub-requirement of the instance, not only the
        // instance, so it guides the search at every state instead of only
        // telling us how far off we are.
        let idx = ArcIndex::new(&directed);
        let active = vec![true; idx.num_arcs()];
        // Rooted at the search's own root: the potential is only valid for sets
        // missing the root, and `PackingPotential` drops the rest.
        let da = dual_ascent_packing(&idx, terminals[0], terminals, &active, DS_PACKING_NNZ);
        search = SteinerSearch::new(work_graph, terminals, root_upper_bound, &[&da.sets]);
    }
    // Out of the addressable range, or the terminals are split.
    let Some(mut search) = search else { return };
    // A pass that improved the incumbent hands the tighter cutoff to a search
    // that has already run under the looser one. That only ever prunes more.
    search.set_upper_bound(root_upper_bound);

    // The window this whole step gets.
    //
    // The exception is measured rather than guessed. A branch-and-cut that has
    // already run on this instance and solved *no* LP and opened *no* node is
    // not going to contribute: on PACE instance024 its model has 205,726 rows
    // and it cannot finish a single solve inside any share it could be given.
    // When that has been observed, the search keeps the whole budget instead of
    // handing half of it to a stage known to do nothing. SteinLib c18 is why
    // this is a measurement and not a rule: there the branch-and-cut closes the
    // instance in 0.38 s after the search fails, so it must keep its share until
    // it has been seen to fail.
    let window = {
        let budget = deadline.saturating_duration_since(Instant::now());
        if branch_and_cut_works {
            Instant::now() + budget.mul_f64(0.5)
        } else {
            deadline
        }
    };

    // The resumable separation loop, carried across attempts and passes exactly
    // as the search is. It applies when it is literally the same model: same
    // arcs, same costs, same root, same terminals.
    let mut separation =
        sep_cache.take().filter(|s| s.applies_to(&directed, terminals[0], terminals));

    // The strongest packing value the search has actually been given, which is
    // what the "did the potential get stronger" test has to be stated over. The
    // ascent's own bound is what it started under.
    let mut potential_value = root_lower_bound;
    let mut slice_labels = SEARCH_SLICE_LABELS;
    let mut first = true;
    // What this whole step cost and what it moved, in the units the
    // branch-and-cut is judged in: bound per second. The clock includes the
    // separation increments, because they come out of the same window and the
    // question being answered is what a second spent here is worth against a
    // second spent there.
    // The baseline is the bound the branch-and-cut would *also* be seeded with,
    // not the search's own zero. A search starting from nothing jumps its
    // frontier from 0 to the whole root bound in its first slice, and calling
    // that a rate would make every comparison against it degenerate.
    let step_started = Instant::now();
    let step_frontier_before = search.lower_bound().max(root_lower_bound);
    // Labels settled since the frontier last rose. See
    // [`potential_will_not_close`] for what a stall is and is not evidence of.
    let mut labels_since_advance = 0u64;
    // A separation increment that did not pay for itself stops the loop asking
    // for more of them *within this call*.
    //
    // Two things set it, and both are measurements rather than give-ups. It is
    // reset by the next call, which is where the resumption pays — the second
    // solver pass hands the loop a fresh window and it continues from the rows it
    // already has, so refusing a second increment here costs nothing later.
    let mut stalled = false;
    // The frontier's rate of advance in the slice *before* the last increment,
    // and what that increment cost, so the slice after it can be asked whether
    // the investment repaid. See the repayment test below.
    let mut pre_increment: Option<(f64, f64, Cost)> = None;
    // The separation batches this call has funded: `(packing gain, seconds,
    // frontier rate before, frontier rate after)`. The projection below is
    // calibrated on them and on nothing else.
    let mut batches: Vec<(Cost, f64, f64, f64)> = Vec::new();
    // The length of the next batch; see the doubling schedule below.
    let mut cert_batch: Option<std::time::Duration> = None;
    loop {
        if Instant::now() >= window || search.labels_settled() >= DS_LABEL_BUDGET {
            break;
        }
        let left = DS_LABEL_BUDGET.saturating_sub(search.labels_settled());
        let before_frontier = search.lower_bound();
        let before_labels = search.labels_settled();
        let t0 = Instant::now();
        let r = search.run(slice_labels.min(left), Some(window));
        let slice_secs = t0.elapsed().as_secs_f64();
        let slice_labels_done = r.labels_settled - before_labels;
        if r.lower_bound > before_frontier + 1e-9 {
            labels_since_advance = 0;
        } else {
            labels_since_advance += slice_labels_done;
        }
        if config.verbose && first {
            eprintln!(
                "[dsearch] start{}: {} labels, optimal {:?}, lower bound {:.1}",
                if resumed { " (resumed)" } else { "" },
                r.labels_settled,
                r.optimal,
                r.lower_bound
            );
        }
        first = false;
        *search_lower_bound = search_lower_bound.max(r.lower_bound);
        if r.optimal.is_some() || search.is_exhausted() {
            break;
        }
        // The next slice is twice this one whatever is decided below; see
        // [`SEARCH_SLICE_LABELS`].
        slice_labels = slice_labels.saturating_mul(2);

        // Did the last increment pay for itself?
        //
        // An increment costs `t` seconds during which the search advances
        // nothing, and buys a potential under which it advances at some new
        // rate. It was worth taking only if the improvement recovers the lost
        // time inside the window that is left:
        //
        // ```text
        //   (rate_after - rate_before) * seconds_left  >=  rate_before * t.
        // ```
        //
        // Every term is measured on this instance in this call. PACE Track 1's
        // instance086 is why the test exists: three increments raise the packing
        // from 3343.4 to 3345.5 — two units against a gap of sixty — while the
        // frontier is already at 3610 and advancing at 420 units a second, and
        // the search that closes the instance at 309,935 labels under the old
        // wiring is starved of exactly the time they took. The first increment
        // is never refused by this: there is no "before" until one has been
        // taken, which is the only way to find out what one buys.
        if let Some((rate_before, spent, packing_before)) = pre_increment.take() {
            let rate_after = if slice_secs > 1e-9 {
                (r.lower_bound - before_frontier).max(0.0) / slice_secs
            } else {
                0.0
            };
            // The horizon is the solver's own remaining budget, not what is left
            // of this window.
            //
            // The investment is a *packing*, and a packing outlives the window
            // that bought it: it stays installed for the rest of this call, for
            // the rest of this pass, and for every later pass, because both the
            // search and the separation loop are resumed rather than rebuilt.
            // Charging it against the window is charging a durable good at the
            // rental price, and it is what refused the increment that opens
            // instance083: three tenths of a second of separation doubled the
            // frontier's rate, from 24.3 to 45.3 units a second, and the test
            // declined it because 0.19 s remained *in the window* while 1.9 s
            // remained in the solve.
            let horizon = deadline.saturating_duration_since(Instant::now()).as_secs_f64();
            let gain = (potential_value - packing_before).max(0.0);
            batches.push((gain, spent, rate_before, rate_after));
            if (rate_after - rate_before) * horizon < rate_before * spent {
                if config.verbose {
                    eprintln!(
                        "[certify] the last batch cost {spent:.2}s and moved the frontier's \
                         rate {rate_before:.1}/s -> {rate_after:.1}/s: it does not repay inside \
                         {horizon:.2}s, so no more this pass"
                    );
                }
                stalled = true;
            } else if !separation_route_is_worth_continuing(
                &batches,
                potential_value,
                r.lower_bound,
                root_upper_bound,
                rate_after,
                horizon,
            ) {
                if config.verbose {
                    eprintln!(
                        "[certify] the projection over {} batches does not reach the incumbent \
                         {root_upper_bound:.1} inside {horizon:.2}s, so no more this pass",
                        batches.len()
                    );
                }
                stalled = true;
            }
        }

        // Is the potential in hand going to close this? The question is only
        // worth asking while there is something stronger available to build.
        let can_strengthen = !stalled
            && separation.as_ref().map_or(true, |s| !s.is_converged())
            && search.potential_layers() < MAX_PACKING_LAYERS;
        if !can_strengthen {
            continue;
        }
        let seconds_left = window.saturating_duration_since(Instant::now()).as_secs_f64();
        if !potential_will_not_close(
            before_frontier,
            r.lower_bound,
            root_upper_bound,
            slice_labels_done,
            labels_since_advance,
            slice_secs,
            seconds_left,
        ) {
            continue;
        }
        if config.verbose {
            eprintln!(
                "[dsearch] frontier {:.1} -> {:.1} over {} labels in {:.2}s: \
                 projected short of the incumbent {:.1}, asking for a stronger potential",
                before_frontier, r.lower_bound, slice_labels_done, slice_secs, root_upper_bound,
            );
        }

        // Spend the next increment on separation instead. Both of its outputs
        // are valid bounds on the reduced instance: the LP's own optimum, and
        // the packing's value.
        // How long this batch of separation gets.
        //
        // The old rule bought a quarter of what remained of the window, once,
        // and then asked whether it had paid for itself. The measured investment
        // curve says that question cannot be answered from one step, because the
        // curve is superlinear at its start: on instance083 a quarter-second of
        // separation buys four solves and a packing of 3,100,514.3 under which
        // the search does not finish, while four seconds buys twenty-six solves,
        // a packing of 3,100,526.7, and a search that finishes in 0.12 s. Each
        // LP second roughly halves the labels, so the first increment looks
        // worthless and the fifth closes the instance.
        //
        // So the batch **doubles**. The first is the measured cost of the search
        // slice that asked for help — spend on the alternative what the thing it
        // replaces just spent — and each further batch is twice its predecessor.
        // Two properties make that safe rather than a schedule to tune:
        //
        // - it reaches any budget in a logarithmic number of fundings, so the
        //   superlinear part of the curve is actually visited;
        // - the total spent when a batch is refused is at most twice the useful
        //   part, because the batches form a geometric series.
        //
        // Nothing here is a fraction of the clock: the first batch is a duration
        // measured on this instance in this pass, and the rest are doublings of
        // it. It is still bounded by the window, which only ever refuses.
        let budget = window.saturating_duration_since(Instant::now());
        if budget.is_zero() {
            break;
        }
        // The first batch is the control's: a quarter of what remains of the
        // window. It is left alone deliberately, so that what is being measured
        // here is the *sequence* and not a resizing of its first term — an
        // instance the control opens on its first increment still opens on it.
        let batch = cert_batch.get_or_insert_with(|| budget.mul_f64(0.25));
        let cert_deadline = Instant::now() + (*batch).min(budget);
        *batch = batch.saturating_mul(2);
        let packing_before = potential_value;
        let increment_started = Instant::now();
        let rate_before = if slice_secs > 1e-9 {
            (r.lower_bound - before_frontier).max(0.0) / slice_secs
        } else {
            0.0
        };
        let sep = separation.get_or_insert_with(|| {
            RootSeparation::new(&directed, terminals[0], terminals)
        });
        let solves_before = sep.lp_solves();
        let Some(cert) = sep.advance(
            root_upper_bound,
            cert_deadline,
            ROOT_CERT_ROUNDS,
            DS_PACKING_NNZ,
        ) else {
            // No LP solve has ever reached optimality on this model, so there is
            // no dual to read and there never will be.
            break;
        };
        *search_lower_bound = search_lower_bound.max(cert.lp_bound).max(cert.packing.value);

        // An edge survives unless *both* of its arcs are eliminated: an
        // undirected edge is available to a tree as long as one orientation is.
        // `DirectedGraph::from_undirected` emits the two arcs of edge `i` at
        // positions `2i` and `2i+1`, which is the whole of the map.
        let mut dead = vec![false; directed.num_arcs() as usize];
        for &a in &cert.eliminated_arcs {
            dead[a as usize] = true;
        }
        // The *strengthened* fixing, from the same certified dual.
        //
        // `cert.eliminated_arcs` is the plain rule `z + rc_a > UB`. The stronger
        // one charges the whole of what an arborescence through `a` must pay:
        // it also contains a root-to-tail path and, below the head, a path down
        // to a terminal, and those three parts are pairwise arc-disjoint — the
        // head's only in-arc is `a`. So
        //
        // ```text
        //   c(A) >= L + d_r(root, u) + d_a + d_r(w, T)      for a = (u,w) in A,
        // ```
        //
        // exactly the argument [`reduced_cost_fixings`] makes for a dual ascent,
        // and it transfers verbatim because the only properties it uses are the
        // ones [`crate::model::ArcDual`] proves: a valid bound `L`, non-negative
        // arc prices, and `c(A) >= L + sum_{a in A} d_a` for every minimal
        // arborescence rooted here. The LP's dual is far stronger than an
        // ascent's — an ascent's packing is maximal and cannot trade one
        // multiplier for another — so the same argument prices more.
        //
        // Both conclusions come from the *same* root, so unioning them at the
        // arc level is sound; see `root_reduce`'s module header for why the
        // union across *different* roots is not, and note that an edge here dies
        // only when both orientations do.
        if let Some(d) = &cert.arc_dual {
            if root_upper_bound.is_finite() && d.reduced.len() == directed.num_arcs() as usize {
                let priced = crate::graph::algorithms::DualAscentResult {
                    lower_bound: d.value,
                    reduced_costs: d.reduced.clone(),
                    root: d.root,
                    steps: Vec::new(),
                    cuts: Vec::new(),
                    sets: Vec::new(),
                };
                let idx = ArcIndex::new(&directed);
                let active = vec![true; idx.num_arcs()];
                let dists = crate::graph::algorithms::reduced_cost_distances(
                    &idx,
                    d.root,
                    terminals,
                    &priced.reduced_costs,
                    &active,
                );
                let fix = crate::graph::algorithms::reduced_cost_fixings(
                    &idx,
                    d.root,
                    terminals,
                    &priced,
                    &dists,
                    &active,
                    root_upper_bound,
                );
                for &a in &fix.arcs {
                    dead[a as usize] = true;
                }
            }
        }
        let before = work_graph.edges.len();
        let mut smaller = work_graph.clone();
        smaller.edges = work_graph
            .edges
            .iter()
            .enumerate()
            .filter(|&(i, _)| !(dead[2 * i] && dead[2 * i + 1]))
            .map(|(_, e)| e.clone())
            .collect();
        if config.verbose {
            eprintln!(
                "[certify] lp bound {:.1}, packing {:.1} over {} sets, {} solves (+{}) [{:?}], \
                 {} rows{} (ascent {:.1}), edges {} -> {}",
                cert.lp_bound,
                cert.packing.value,
                cert.packing.sets.len(),
                cert.lp_solves,
                cert.lp_solves - solves_before,
                sep.method(),
                sep.num_rows(),
                if sep.is_converged() { ", converged" } else { "" },
                root_lower_bound,
                before,
                smaller.edges.len(),
            );
        }
        // The elimination is applied whatever happens next - it is free and it
        // only shrinks the state space.
        if smaller.edges.len() < before && std::env::var("SJ_NO_RESTRICT").is_err() {
            search.restrict_to(&smaller);
        }
        // Offer the layer only when the object the search actually consumes got
        // stronger. The potential is the packing, so the test is on the packing's
        // own value: a packing no stronger at the root than the one already
        // installed re-keys the whole open queue for nothing. This is a measured
        // fact about the two objects, not an estimate of how long a continuation
        // would take.
        if cert.packing.value <= potential_value + 1e-9 {
            stalled = true;
            continue;
        }
        pre_increment =
            Some((rate_before, increment_started.elapsed().as_secs_f64(), packing_before));
        match search.add_packing(&cert.packing.sets) {
            PackingAdmission::Added => potential_value = cert.packing.value,
            // Loud, because a silent one invalidated an experiment once. See
            // [`MAX_PACKING_LAYERS`].
            other => {
                if config.verbose {
                    eprintln!("[certify] packing refused: {other:?}");
                }
            }
        }
    }
    let step_secs = step_started.elapsed().as_secs_f64();
    *search_rate = if step_secs > 1e-9 {
        ((search.lower_bound() - step_frontier_before).max(0.0)) / step_secs
    } else {
        0.0
    };
    *cache = Some(search);
    *sep_cache = separation;
}


/// States the width-parameterised dynamic programme may hold at once.
///
/// A memory bound: each state is a cost and a packed signature, so a few
/// million of them is where the table stops being cheaper than the
/// branch-and-cut it would hand back to. Time is bounded by the deadline
/// instead — see [`crate::graph::algorithms::steiner_td`] for why the analytic
/// work estimate is far too loose to serve as the admission test.
const TD_STATE_BUDGET: usize = 40_000_000;

/// Solve exactly by dynamic programming over a tree decomposition, when the
/// graph is narrow enough for one.
///
/// Returns the optimum and what it cost, or `None` when the graph is too wide,
/// the state budget is hit, or the deadline passes — all of which leave the
/// caller exactly where it was.
/// Returns the exact value when the dynamic programme finished, and whether the
/// attempt was cut off by the **clock or the state budget** rather than refused
/// on width.
///
/// The two are not the same event and conflating them is §47's error. A refusal
/// on width is a property of the graph: the cheap min-degree ordering abandons at
/// the first oversized bag, it costs microseconds, and repeating it is free. A
/// truncation is a property of the budget, repeats *expensively*, and is the only
/// one worth remembering.
fn try_decomposition(
    graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    deadline: Instant,
) -> (Option<(Cost, f64)>, bool) {
    use crate::graph::algorithms::steiner_td::{steiner_tree_over_decomposition, MAX_BAG};
    use crate::graph::algorithms::tree_decomposition::{
        decompose_portfolio, decompose_with, Ordering, ORDERINGS,
    };

    if terminals.len() < 2 || Instant::now() >= deadline {
        return (None, false);
    }
    // One vertex of every bag is spent on the root terminal the DP pins there.
    let cap = MAX_BAG - 2;
    let started = Instant::now();
    // The cheap ordering is the gate: it abandons an ordering at the first bag
    // that exceeds the cap, so a wide graph costs microseconds to reject. Only
    // once it has shown the graph is narrow is the rest of the portfolio worth
    // running, and the portfolio then chooses by the work each decomposition
    // implies rather than by width alone.
    let Some(cheap) = decompose_with(graph, Ordering::MinDegree, cap, Some(deadline)) else {
        return (None, false);
    };
    let td = decompose_portfolio(graph, cap, Some(deadline), &ORDERINGS[1..])
        .map(|(t, _)| t)
        .filter(|t| {
            use crate::graph::algorithms::steiner_td::work_estimate;
            work_estimate(t, graph.edges.len(), 1) <= work_estimate(&cheap, graph.edges.len(), 1)
        })
        .unwrap_or(cheap);
    if !td.verify(graph) {
        return (None, false);
    }

    // One attempt, bounded by the clock rather than by an estimate.
    //
    // Two ways of bounding the bet were tried before this one.
    //
    // The analytic [`work_estimate`] is a sound upper bound and useless as an
    // admission test: it predicts `1.6e10` units for a run that takes 0.14 s,
    // because the reachable signatures at a bag are a minute fraction of the
    // partitions of that bag.
    //
    // Iterative deepening on the state budget — run under a small cap, quadruple
    // only while the next attempt still fits — is wrong for a subtler reason,
    // and the trace says so plainly. On PACE Track 2's instance040 the attempts
    // cost 0.03 s at 100k states, 0.16 s at 400k and **1.31 s** at 1.6M, and the
    // extrapolation from those refused to go on. The full run takes 2.37 s. The
    // DP's cost is not proportional to the states it holds: the wide bags come
    // early and the tail is nearly free, so any extrapolation from a truncated
    // run over-predicts what remains, and the deepening refused instances it
    // would have solved in a third of the time it had already spent.
    //
    // What bounds the loss exactly is the deadline, which the DP checks at every
    // node. So the attempt is single, the state budget is a memory guard, and an
    // instance too big for the clock costs the clock — the same bargain the
    // branch-and-cut it defers to makes.
    let Some((cost, _)) = steiner_tree_over_decomposition(
        graph,
        terminals,
        &td,
        TD_STATE_BUDGET,
        // The exact finish reports a value; nothing downstream wants the edge
        // set, so the tables can be freed as they die.
        false,
        Some(deadline),
    ) else {
        // The decomposition was built, so the graph is narrow enough for the
        // encoding: what stopped the run was the clock or the state budget, and
        // both repeat on the same graph with less of the first.
        return (None, true);
    };
    (Some((cost, started.elapsed().as_secs_f64())), false)
}

fn try_dreyfus_wagner(
    graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    start: Instant,
) -> Option<SolveResult> {
    if !dw_is_affordable(terminals.len(), graph.num_nodes, graph.edges.len()) {
        return None;
    }
    let dw = dreyfus_wagner(graph, terminals)?;
    Some(SolveResult {
        status: SolveStatus::Optimal,
        primal_bound: dw.optimal_cost,
        dual_bound: dw.optimal_cost,
        gap_pct: 0.0,
        nodes_processed: 0,
        cuts_added: 0,
        lp_solves: 0,
        time_secs: start.elapsed().as_secs_f64(),
        verified: true,
        method: SolveMethod::DreyfusWagner,
    })
}

fn trivial_result(start: Instant, value: Cost, method: SolveMethod) -> SolveResult {
    SolveResult {
        status: SolveStatus::Optimal,
        primal_bound: value,
        dual_bound: value,
        gap_pct: 0.0,
        nodes_processed: 0,
        cuts_added: 0,
        lp_solves: 0,
        time_secs: start.elapsed().as_secs_f64(),
        verified: true,
        method,
    }
}

/// Solve a Steiner tree instance from a SteinLib `.stp` file.
pub fn solve_file(path: &str, config: SolverConfig) -> SolveResult {
    let instance = io::read_instance(path).expect("Failed to read instance");
    solve(&instance, config)
}

#[cfg(test)]
mod feedback_tests {
    use super::*;
    use crate::graph::{NodeId, NodeType};
    use std::sync::atomic::Ordering;

    fn xorshift(seed: u64) -> impl FnMut() -> u64 {
        let mut s = seed;
        move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        }
    }

    /// A connected graph with `k` terminals, and a spanning tree of it.
    fn graph_and_spanning_tree(
        rng: &mut dyn FnMut() -> u64,
    ) -> (UndirectedGraph, Vec<NodeId>, Vec<u32>, Cost) {
        let n = 6 + (rng() % 8) as u32;
        let mut g = UndirectedGraph::new(n);
        let k = 2 + (rng() % (n as u64 - 2).max(1)) as usize;
        let mut terminals = Vec::new();
        for v in 1..=n {
            let t = (v as usize) <= k;
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            if t {
                terminals.push(v);
            }
        }
        // A path guarantees connectivity; the rest are extra chords.
        for v in 1..n {
            g.add_edge(v, v + 1, 1.0 + (rng() % 9) as f64);
        }
        for _ in 0..(n as usize) {
            let u = 1 + (rng() % n as u64) as u32;
            let v = 1 + (rng() % n as u64) as u32;
            if u != v {
                g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
            }
        }
        // A spanning tree by union-find over the edge list, in index order.
        let mut parent: Vec<u32> = (0..=n).collect();
        fn find(p: &mut Vec<u32>, x: u32) -> u32 {
            let mut r = x;
            while p[r as usize] != r {
                r = p[r as usize];
            }
            p[x as usize] = r;
            r
        }
        let mut edges = Vec::new();
        let mut cost = 0.0;
        for (i, e) in g.edges.iter().enumerate() {
            let (a, b) = (find(&mut parent, e.src), find(&mut parent, e.dst));
            if a != b {
                parent[a as usize] = b;
                edges.push(i as u32);
                cost += e.cost;
            }
        }
        (g, terminals, edges, cost)
    }

    /// A tree of the graph, handed in as arcs, comes back as a witness of that
    /// graph at exactly its own cost — and a claim that is not the tree's cost,
    /// or an arc set that does not span the terminals, comes back as nothing.
    ///
    /// The arc-to-edge map is the only thing being trusted here, and it is the
    /// thing §61 says must never be trusted, so it is re-derived: the witness is
    /// verified against the graph's own edge list and its own terminals.
    #[test]
    fn a_tree_becomes_a_witness_of_the_graph_it_is_a_tree_of() {
        let mut rng = xorshift(0x9E37_79B9_7F4A_7C15);
        let (mut ok, mut rejected_value, mut rejected_shape) = (0, 0, 0);
        for _ in 0..400 {
            let (g, terminals, edges, cost) = graph_and_spanning_tree(&mut rng);
            let arcs: Vec<u32> = edges.iter().map(|&e| 2 * e).collect();
            let w = witness_from_arcs(&g, &terminals, &arcs, cost)
                .expect("a spanning tree of the graph must verify");
            assert!((w.verify().unwrap() - cost).abs() < 1e-6);
            assert_eq!(w.graph.edges.len(), g.edges.len());
            ok += 1;

            // A value that is not the tree's cost is refused outright.
            assert!(witness_from_arcs(&g, &terminals, &arcs, cost - 1.0).is_none());
            rejected_value += 1;

            // Dropping an edge can disconnect a terminal; when it does, the
            // witness must be refused. When it does not, the recomputed cost is
            // lower than the claim and it is refused anyway. Either way: `None`.
            if !edges.is_empty() {
                let short: Vec<u32> = arcs[1..].to_vec();
                assert!(witness_from_arcs(&g, &terminals, &short, cost).is_none());
                rejected_shape += 1;
            }

            // The reverse orientation of every arc names the same edge, so the
            // witness is identical: an undirected tree does not know which way
            // the arborescence ran it.
            let flipped: Vec<u32> = edges.iter().map(|&e| 2 * e + 1).collect();
            let w2 = witness_from_arcs(&g, &terminals, &flipped, cost)
                .expect("the reverse orientation names the same edges");
            assert_eq!(w2.edges, w.edges);
        }
        assert!(ok > 300 && rejected_value > 300 && rejected_shape > 300);
    }

    /// A grid too large for the reduction to close, and its exact optimum.
    ///
    /// [`crate::root_reduce::tests::grid_instance`] is sized so that its own
    /// oracle is cheap, and the consequence is that `tighten` proves it outright:
    /// `finish` is never entered and no writeback ever executes. Forty-odd
    /// terminals on a hundred-odd vertices keeps the width — and therefore the
    /// oracle — cheap while putting the instance out of the reduction's reach, so
    /// the pipeline runs to the goal-directed search and past it.
    fn hard_grid_instance(
        rng: &mut dyn FnMut() -> u64,
    ) -> Option<(crate::graph::SteinerInstance, Cost)> {
        use crate::graph::algorithms::steiner_td::reference::{raw_dp, RawCensus};
        use crate::graph::algorithms::tree_decomposition::decompose;
        let rows = 6;
        let cols = 18 + (rng() % 5) as u32;
        let n = rows * cols;
        let id = |r: u32, c: u32| r * cols + c + 1;
        let mut g = UndirectedGraph::new(n);
        let mut terminals = Vec::new();
        for v in 1..=n {
            // Roughly a third of the vertices, which lands between 24 (where
            // Dreyfus-Wagner stops) and 64 (where the search stops).
            let t = rng() % 3 == 0;
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            if t {
                terminals.push(v);
            }
        }
        if terminals.len() < 25 || terminals.len() > 60 {
            return None;
        }
        // **Unit costs.** This is the property that keeps the reduction from
        // closing the instance before `finish` is entered: the dual ascent
        // saturates almost everything on near-uniform costs and is degenerate, so
        // a real gap survives the reduction. With costs drawn from 1..9 the same
        // grids are proved outright at the root and `run_search` is never
        // reached — which is what the coverage counter caught, twice.
        for r in 0..rows {
            for c in 0..cols {
                if c + 1 < cols {
                    g.add_edge(id(r, c), id(r, c + 1), 1.0);
                }
                if r + 1 < rows {
                    g.add_edge(id(r, c), id(r + 1, c), 1.0);
                }
            }
        }
        // A cap of ten against a treewidth of six. The elimination ordering is
        // heuristic, so a cap barely above the true width is often missed
        // outright — and a *generous* cap is worse, because it is then often
        // taken: `B(13) = 27,644,437` signatures a bag made the oracle cost 620
        // CPU-seconds before this was understood. Slack of four on a width of six
        // is the band where the ordering succeeds and the table stays small.
        let td = decompose(&g, 10, None)?;
        let mut census = RawCensus::default();
        let opt = raw_dp(&g, &terminals, &td, 4_000_000, None, &mut census)?;
        Some((crate::root_reduce::as_instance(&g, &terminals), opt))
    }

    /// End to end: the solver never reports a dual bound above the optimum, and
    /// never claims `Optimal` at a wrong value, across several budgets.
    ///
    /// # What this covers, and what it does not
    ///
    /// It does **not** reach the feedback writebacks, and the counters say so
    /// rather than the comment claiming otherwise. Five generators were tried and
    /// every one of them is closed before `finish` is entered at all:
    ///
    /// - small dense graphs — Dreyfus-Wagner solves them in `solve`;
    /// - `5x9` grids with random costs — the reduction proves them at the root;
    /// - `6x20` grids, unit costs — the classical reduction takes 120 vertices
    ///   and 43 terminals to 20 and 9, and Dreyfus-Wagner finishes them;
    /// - `6x12` grids at 70 % terminal density — the classical reduction
    ///   contracts them to *one* vertex;
    /// - dense all-terminal graphs, whose optimum is the MST in closed form — the
    ///   relaxation is the spanning-tree polytope, so the ascent closes them.
    ///
    /// That is not an accident of these five. The branch-and-cut is reached only
    /// when Dreyfus-Wagner (24 terminals), the goal-directed search (64) and the
    /// width DP (a bag of `MAX_BAG - 2`) have all refused, and every oracle this
    /// crate has is bounded by one of those same three quantities. An instance
    /// with an independently computable optimum is, more or less by definition,
    /// an instance the pipeline closes early.
    ///
    /// So the writeback is gated directly instead, in
    /// [`the_branch_and_cut_carries_a_bound_no_larger_than_the_optimum`], which
    /// runs the reduction and then the branch-and-cut itself and asserts its own
    /// coverage. What *this* gate is, is a regression on the reporting path at
    /// several budgets — and it is kept because that is a real thing to regress.
    #[test]
    fn a_carried_bound_never_exceeds_the_optimum() {
        use crate::branch_and_bound::{SolveStatus, SolverConfig};
        let mut rng = xorshift(0x2545_F491_4F6C_DD1D);
        let mut checked = 0;
        for _ in 0..12 {
            let Some((instance, opt)) = hard_grid_instance(&mut rng) else { continue };
            for limit in [0.5, 1.5] {
                let cfg = SolverConfig {
                    time_limit_secs: limit,
                    verbose: false,
                    preprocess: true,
                    ..SolverConfig::default()
                };
                let r = crate::solver::solve(&instance, cfg);
                assert!(
                    r.dual_bound <= opt + 1e-6,
                    "dual bound {} above the optimum {opt} at a {limit}s limit",
                    r.dual_bound
                );
                if r.primal_bound.is_finite() {
                    assert!(
                        r.primal_bound >= opt - 1e-6,
                        "primal {} below the optimum {opt}",
                        r.primal_bound
                    );
                }
                if r.status == SolveStatus::Optimal {
                    assert!(
                        (r.primal_bound - opt).abs() < 1e-6,
                        "claimed Optimal {} against a true optimum of {opt}",
                        r.primal_bound
                    );
                }
                checked += 1;
            }
        }
        assert!(checked > 10, "only {checked} cases were exercised");
    }

    /// The proposition the branch-and-cut's writeback rests on, gated where it
    /// is actually stated: **after** the classical fixpoint, on the graph the
    /// reduction leaves behind, against Dreyfus-Wagner.
    ///
    /// # Why this is not run through `solve`
    ///
    /// `solve` reaches the branch-and-cut only when Dreyfus-Wagner, the
    /// goal-directed search and the width DP have all refused — above 24
    /// terminals, above 64 terminals, and above a bag of `MAX_BAG - 2 = 13`
    /// respectively. Every generator whose optimum this crate can compute
    /// independently fails at least one of those by construction: the grid is
    /// narrow *because* its oracle needs to be, and Dreyfus-Wagner's own range is
    /// the one that refuses the branch-and-cut. Two generators were written for
    /// this gate before that was understood, and the counters caught both — 24
    /// solves and 42 solves that never executed the writeback and asserted
    /// nothing.
    ///
    /// So the proposition is gated directly, in the composition `finish` uses:
    /// tighten under a cutoff, run the branch-and-cut on what it leaves, compose
    /// the dual exactly as `finish` does, and check it against the true optimum.
    /// The reduction runs first, which is what SS70 says a rule of this kind needs:
    /// the graph the branch-and-cut sees has retired ids, contractions and a
    /// non-zero offset, and that difference is where both of `extended.rs`'s
    /// faults hid.
    #[test]
    fn the_branch_and_cut_carries_a_bound_no_larger_than_the_optimum() {
        use crate::branch_and_bound::BranchAndCutSolver;
        use crate::graph::{costs_are_integral, tighten_dual};
        use crate::root_reduce::{tighten, ReduceConfig};
        let mut rng = xorshift(0x7F4A_7C15_9E37_79B9);
        let (mut checked, mut ran_bnc, mut witnessed) = (0, 0, 0);
        for _ in 0..220 {
            let n = 8 + (rng() % 9) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 3 + (rng() % 4) as usize;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = (v as usize) <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for v in 1..n {
                g.add_edge(v, v + 1, 1.0 + (rng() % 9) as f64);
            }
            for _ in 0..(2 * n as usize) {
                let (u, v) = (1 + (rng() % n as u64) as u32, 1 + (rng() % n as u64) as u32);
                if u != v {
                    g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
                }
            }
            let Some(dw) = crate::graph::algorithms::dreyfus_wagner(&g, &terminals) else {
                continue;
            };
            let opt = dw.optimal_cost;

            // A loose cutoff as well as a tight one: the tight one cannot catch a
            // bound-based rule being wrong, because under it every bound is right.
            for slack in [0.0, 2.0, 9.0] {
                let cfg = ReduceConfig {
                    initial_upper_bound: opt + slack,
                    deadline: Some(Instant::now() + std::time::Duration::from_secs_f64(0.3)),
                    ..ReduceConfig::default()
                };
                let reduced = tighten(g.clone(), terminals.clone(), &cfg);
                let ub_witnessed = reduced.upper_bound_is_witnessed();
                if ub_witnessed {
                    witnessed += 1;
                }
                let offset = reduced.offset;
                if reduced.terminals.len() < 2 {
                    continue;
                }
                let directed = DirectedGraph::from_undirected(&reduced.graph);
                let mut solver = BranchAndCutSolver::new(
                    directed.clone(),
                    reduced.root,
                    reduced.terminals.clone(),
                );
                solver.config =
                    SolverConfig { time_limit_secs: 1.0, ..SolverConfig::default() };
                solver.seed_bounds(reduced.lower_bound, reduced.upper_bound);
                let (solution, stats) = solver.solve();
                if stats.lp_solves > 0 || stats.nodes_processed > 0 {
                    ran_bnc += 1;
                }

                // Exactly `finish`'s composition, so the number under test is the
                // number the pipeline would carry.
                let mut primal =
                    if ub_witnessed { reduced.upper_bound } else { Cost::INFINITY };
                if let Some(ref sol) = solution {
                    if verify_solution(&directed, reduced.root, &reduced.terminals, sol).is_valid
                        && sol.objective_value < primal
                    {
                        primal = sol.objective_value;
                    }
                }
                let integral = costs_are_integral(directed.arcs.iter().map(|a| a.cost));
                let dual =
                    tighten_dual(stats.dual_bound.max(reduced.lower_bound), integral).min(primal);

                // The claim, on the scale of the graph `tighten` was handed.
                if ub_witnessed && dual.is_finite() {
                    assert!(
                        dual + offset <= opt + 1e-6,
                        "carried dual {} + offset {offset} above the optimum {opt} \
                         at a cutoff of {} on {n} nodes / {k} terminals",
                        dual,
                        opt + slack
                    );
                }
                // And the rebase the caller then applies must stay valid too.
                assert!(
                    (dual - offset).max(0.0) <= opt + 1e-6,
                    "rebased dual above the optimum {opt}"
                );
                checked += 1;
            }
        }
        assert!(
            checked > 300 && ran_bnc > 100 && witnessed > 100,
            "only {checked} compositions, {ran_bnc} of which ran the branch-and-cut and \
             {witnessed} of which had a witnessed cutoff — the gate proved nothing"
        );
    }

    /// The same instances, with the reduction's own deliberately *loose* cutoff:
    /// a bound-based rule being wrong cannot be caught by a tight one.
    ///
    /// Supplying an incumbent above the optimum is the loose case, and it is the
    /// one that exercises the carried bound against a reduction that has deleted
    /// nothing on its strength.
    #[test]
    fn a_carried_bound_is_valid_under_a_loose_cutoff() {
        use crate::branch_and_bound::{SolveStatus, SolverConfig};
        let mut rng = xorshift(0xD1B5_4A32_D192_ED03);
        let mut checked = 0;
        for _ in 0..10 {
            let Some((instance, opt)) = crate::root_reduce::tests::grid_instance(&mut rng) else {
                continue;
            };
            for slack in [1.0, 10.0, 100.0] {
                let cfg = SolverConfig {
                    time_limit_secs: 1.0,
                    verbose: false,
                    preprocess: true,
                    initial_upper_bound: opt + slack,
                    ..SolverConfig::default()
                };
                let r = crate::solver::solve(&instance, cfg);
                assert!(
                    r.dual_bound <= opt + 1e-6,
                    "dual bound {} above the optimum {opt} under a cutoff of {}",
                    r.dual_bound,
                    opt + slack
                );
                if r.status == SolveStatus::Optimal {
                    assert!((r.primal_bound - opt).abs() < 1e-6);
                }
                checked += 1;
            }
        }
        assert!(checked > 20, "only {checked} cases were exercised");
    }
}

#[cfg(test)]
mod scheduling_tests {
    use super::*;

    /// The units-short shape: a frontier that barely moves.
    ///
    /// PACE instance167's measured trace (§38, ninth round): 350,000 labels
    /// under the ascent packing take the frontier from 2,600,420 to 2,600,427
    /// against an incumbent of 2,600,443, in about two seconds, with about one
    /// second left. The projection is `16 / (7/350000) = 800,000` labels needed
    /// against `175,000/s * 1 s = 175,000` available, so the potential is asked
    /// to get stronger — which is what the LP packing then does, closing the
    /// instance in 29,000 labels.
    #[test]
    fn a_crawling_frontier_asks_for_a_stronger_potential() {
        assert!(potential_will_not_close(
            2_600_420.0,
            2_600_427.0,
            2_600_443.0,
            350_000,
            0,
            2.0,
            1.0
        ));
    }

    /// The same rate with a gap small enough to reach does *not* ask. The
    /// predicate is a projection, not a verdict on the packing's quality.
    #[test]
    fn a_crawling_frontier_with_a_reachable_gap_keeps_the_budget() {
        assert!(!potential_will_not_close(
            2_600_420.0,
            2_600_427.0,
            2_600_430.0,
            350_000,
            0,
            2.0,
            1.0
        ));
    }

    /// A stall diverts the budget only once it is bigger than the budget.
    ///
    /// 100,000 labels in 0.5 s is 200,000/s, so four seconds can settle 800,000.
    /// A stall of 100,000 is not evidence against that; a stall of 900,000 is.
    #[test]
    fn a_stall_asks_only_when_it_outweighs_the_remaining_budget() {
        assert!(!potential_will_not_close(100.0, 100.0, 110.0, 100_000, 100_000, 0.5, 4.0));
        assert!(potential_will_not_close(100.0, 100.0, 110.0, 100_000, 900_000, 0.5, 4.0));
    }

    /// PACE Track 1's instance026: a one-unit gap, a frontier that stands still
    /// at 1750 against an incumbent of 1751, and a goal state popped at 23,640
    /// labels. The first version of this predicate diverted at 8,192 and lost
    /// the proof. At that boundary the stall is 12,288 labels against 46,000 the
    /// remaining 0.79 s can settle, so it must not divert.
    #[test]
    fn a_one_unit_gap_is_not_abandoned_for_standing_still() {
        assert!(!potential_will_not_close(1750.0, 1750.0, 1751.0, 8_192, 12_288, 0.14, 0.79));
    }

    /// The case the old phase order was measured into protecting: a frontier
    /// advancing fast enough to arrive inside the budget must not divert it.
    #[test]
    fn a_marching_frontier_keeps_the_budget() {
        // Half the gap closed in a fifth of the time.
        assert!(!potential_will_not_close(0.0, 500.0, 1000.0, 100_000, 0, 0.2, 1.0));
    }

    /// Degenerate inputs never divert the budget: no incumbent to aim at, no
    /// labels to measure a rate from, no time left to spend, or a frontier that
    /// has already arrived.
    #[test]
    fn degenerate_inputs_refuse_to_ask() {
        assert!(!potential_will_not_close(0.0, 10.0, Cost::INFINITY, 1000, 0, 1.0, 1.0));
        assert!(!potential_will_not_close(0.0, 10.0, 100.0, 0, 0, 1.0, 1.0));
        assert!(!potential_will_not_close(0.0, 10.0, 100.0, 1000, 0, 1.0, 0.0));
        assert!(!potential_will_not_close(0.0, 100.0, 100.0, 1000, 0, 1.0, 5.0));
        assert!(!potential_will_not_close(0.0, 101.0, 100.0, 1000, 0, 1.0, 5.0));
    }
}
