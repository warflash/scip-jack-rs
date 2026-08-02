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
    dreyfus_wagner, dual_ascent_packing, ArcIndex, SteinerSearch,
};
use crate::graph::{costs_are_integral, tighten_dual, Cost, DirectedGraph, SteinerInstance, UndirectedGraph};
use crate::io;
use crate::model::{
    hyp_certificate, hyp_work, root_certificate, verify_solution, HYP_UNITS_PER_SECOND,
    HYP_WORK_CEILING,
};
use crate::preprocessing::preprocess_until;
use crate::root_reduce::{tighten, ReduceConfig};

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
    let mut incoming_ub = Cost::INFINITY;
    let mut best: Option<SolveResult> = None;
    // The goal-directed search, carried across passes. When the second pass's
    // tightening lands on the same reduced instance — which is the usual case
    // once the first pass has already run the reductions to a fixpoint — the
    // search continues instead of starting over. See [`SteinerSearch`].
    let mut search_cache: Option<SteinerSearch> = None;
    // Root bounds an earlier pass proved, restated for the current pass's graph
    // exactly as `incoming_ub` is, and a note on whether the branch-and-cut has
    // been observed to do anything on this instance. The first pass assumes it
    // does; only a pass that watched it solve nothing says otherwise.
    let mut carried_lower_bound: Cost = 0.0;
    let mut branch_and_cut_works = true;

    // A converged tightening carried into the next pass; see below.
    let mut reuse: Option<crate::root_reduce::Reduced> = None;
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
        let reusable = reduced.converged.then(|| (reduced.clone(), reduced.upper_bound));
        // What the next pass will start from, before `finish` consumes `reduced`.
        let next_graph = reduced.graph.clone();
        let next_terminals = reduced.terminals.clone();
        let next_offset = reduced.offset;
        // Cap the first search so an unproved-but-improved incumbent still
        // leaves time for the second tightening pass to exploit it.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let pass_deadline = if pass == 0 {
            Instant::now() + remaining.mul_f64(0.5)
        } else {
            deadline
        };
        if config.verbose {
            eprintln!(
                "[time] pass {pass}: tighten {}took {:.2}s, search gets {:.2}s, elapsed {:.2}s",
                if reused_here { "(reused fixpoint) " } else { "" },
                tighten_secs,
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
            &mut carried_lower_bound,
            &mut branch_and_cut_works,
        );
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
        // The fixpoint survives into the next pass exactly when that pass would
        // start it from the same graph with an upper bound no better than the
        // one it converged under. A strictly better incumbent is new
        // information: the bound-based reductions can kill more with it, so the
        // fixpoint has to be recomputed.
        reuse = reusable.filter(|(_, ub)| incoming_ub >= ub - 1e-9).map(|(r, _)| r);
        carried_lower_bound = (carried_lower_bound - next_offset).max(0.0);
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
fn finish(
    reduced: crate::root_reduce::Reduced,
    config: &SolverConfig,
    start: Instant,
    deadline: Instant,
    search_cache: &mut Option<SteinerSearch>,
    carried_lower_bound: &mut Cost,
    branch_and_cut_works: &mut bool,
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

    if reduced.proved_optimal(config.gap_tolerance.max(1e-6)) {
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
            &mut search_lower_bound,
        );
        if let Some(value) = search_cache.as_ref().and_then(|s| s.optimum()) {
            // The search runs on a graph that keeps only trees at or below the
            // incumbent, so the incumbent still wins ties.
            let best = value.min(root_upper_bound);
            return SolveResult {
                status: SolveStatus::Optimal,
                primal_bound: best + offset,
                dual_bound: best + offset,
                gap_pct: 0.0,
                nodes_processed: 0,
                cuts_added: 0,
                lp_solves: 0,
                time_secs: start.elapsed().as_secs_f64(),
                verified: true,
                method: SolveMethod::DreyfusWagner,
            };
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
    if let Some((value, secs)) = try_decomposition(&work_graph, &terminals, deadline) {
        if config.verbose {
            eprintln!("[td] exact by tree decomposition: {value:.1} in {secs:.2}s");
        }
        let best = value.min(root_upper_bound);
        return SolveResult {
            status: SolveStatus::Optimal,
            primal_bound: best + offset,
            dual_bound: best + offset,
            gap_pct: 0.0,
            nodes_processed: 0,
            cuts_added: 0,
            lp_solves: 0,
            time_secs: start.elapsed().as_secs_f64(),
            verified: true,
            method: SolveMethod::TreeDecomposition,
        };
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

    let (solution, stats) = solver.solve();
    // Whether it did anything at all, for the next pass to act on.
    *branch_and_cut_works = stats.lp_solves > 0 || stats.nodes_processed > 0;

    let mut verified = false;
    let mut primal = root_upper_bound;
    if let Some(ref sol) = solution {
        let vr = verify_solution(&directed, root, &terminals, sol);
        verified = vr.is_valid;
        if verified && sol.objective_value < primal {
            primal = sol.objective_value;
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
    let dual = if stats.status == SolveStatus::Infeasible && primal.is_finite() {
        primal
    } else {
        tighten_dual(stats.dual_bound.max(root_lower_bound), integral).min(primal)
    };
    let gap_pct = if primal.is_finite() && dual > f64::NEG_INFINITY {
        ((primal - dual) / primal.abs().max(1e-10)) * 100.0
    } else {
        100.0
    };

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

/// Advance the goal-directed search, creating it or continuing it.
///
/// The search's whole state — settled labels, open queue, Lemma-15 witnesses —
/// lives in `cache` and survives across attempts *and* across solver passes.
/// That is the point: on PACE 024, 025, 086 and 087 the search settles a few
/// hundred thousand labels per slice and needs roughly their sum, and under the
/// old wiring it was handed four disjoint slices and started each of them from
/// nothing.
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
    search_lower_bound: &mut Cost,
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

    // Two phases, and the second is only paid for when the first fails. The
    // ascent's packing is *maximal* - no set missing the root admits any increase
    // - so when it is not strong enough there is no combinatorial way to
    // strengthen it. The LP on the same relaxation reaches materially further,
    // and `root_certificate` turns its dual back into a packing. That LP is not
    // free, so it is run only after the cheap potential has been shown, by
    // running it, not to suffice.
    //
    // Unlike the old wiring, the second phase *continues* the first: the labels
    // it settled, the queue it built and the witnesses it found are all still
    // there, and only the potential and the graph get stronger.
    for phase in 0..2 {
        let budget = deadline.saturating_duration_since(Instant::now());
        if budget.is_zero() {
            break;
        }
        // The first phase keeps the share it always had, so an instance the cheap
        // potential already closes is untouched by any of this. Everything the
        // certificate costs comes out of what is left after that phase failed.
        //
        // The exception is measured rather than guessed. A branch-and-cut that
        // has already run on this instance and solved *no* LP and opened *no*
        // node is not going to contribute: on PACE instance024 its model has
        // 205,726 rows and it cannot finish a single solve inside any share it
        // could be given. When that has been observed, the search keeps the whole
        // budget instead of handing half of it to a phase known to do nothing.
        // SteinLib c18 is why this is a measurement and not a rule: there the
        // branch-and-cut closes the instance in 0.38 s after the search fails, so
        // it must keep its share until it has been seen to fail.
        let slice = if branch_and_cut_works {
            Instant::now() + budget.mul_f64(0.5)
        } else {
            deadline
        };
        let left = DS_LABEL_BUDGET.saturating_sub(search.labels_settled());
        let r = search.run(left, Some(slice));
        if config.verbose {
            eprintln!(
                "[dsearch] phase {phase}{}: {} labels total, optimal {:?}, lower bound {:.1}",
                if resumed && phase == 0 { " (resumed)" } else { "" },
                r.labels_settled,
                r.optimal,
                r.lower_bound
            );
        }
        *search_lower_bound = search_lower_bound.max(r.lower_bound);
        if r.optimal.is_some() {
            break;
        }
        // Nothing left in the queue, or nothing left in the label budget: another
        // phase would settle nothing.
        if phase == 1 || search.is_exhausted() || search.labels_settled() >= DS_LABEL_BUDGET {
            break;
        }

        // Build the stronger potential. Both its outputs are valid bounds on the
        // reduced instance: the LP's own optimum, and the packing's value.
        let budget = deadline.saturating_duration_since(Instant::now());
        if budget.is_zero() {
            break;
        }
        let cert_deadline = Instant::now() + budget.mul_f64(0.25);
        let Some(cert) = root_certificate(
            &directed,
            terminals[0],
            terminals,
            root_upper_bound,
            cert_deadline,
            ROOT_CERT_ROUNDS,
            DS_PACKING_NNZ,
        ) else {
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
                "[certify] lp bound {:.1}, packing {:.1} over {} sets, {} solves \
                 (ascent {:.1}), edges {} -> {}",
                cert.lp_bound,
                cert.packing.value,
                cert.packing.sets.len(),
                cert.lp_solves,
                root_lower_bound,
                before,
                smaller.edges.len(),
            );
        }
        // The elimination is applied whatever happens next - it is free and it
        // only shrinks the state space.
        if smaller.edges.len() < before {
            search.restrict_to(&smaller);
        }
        // Continue only when the object the search actually consumes got
        // stronger. The potential is the packing, so the test is on the packing's
        // own value: if it did not rise above the bound the search already ran
        // under, continuing would sweep against a potential no stronger at the
        // root, and the budget belongs to the branch-and-cut instead. This is a
        // measured fact about the two objects, not an estimate of how long a
        // continuation would take.
        if cert.packing.value <= root_lower_bound + 1e-9 {
            break;
        }
        search.add_packing(&cert.packing.sets);
    }
    *cache = Some(search);
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
fn try_decomposition(
    graph: &UndirectedGraph,
    terminals: &[crate::graph::NodeId],
    deadline: Instant,
) -> Option<(Cost, f64)> {
    use crate::graph::algorithms::steiner_td::{steiner_tree_over_decomposition, MAX_BAG};
    use crate::graph::algorithms::tree_decomposition::{
        decompose_portfolio, decompose_with, Ordering, ORDERINGS,
    };

    if terminals.len() < 2 || Instant::now() >= deadline {
        return None;
    }
    // One vertex of every bag is spent on the root terminal the DP pins there.
    let cap = MAX_BAG - 2;
    let started = Instant::now();
    // The cheap ordering is the gate: it abandons an ordering at the first bag
    // that exceeds the cap, so a wide graph costs microseconds to reject. Only
    // once it has shown the graph is narrow is the rest of the portfolio worth
    // running, and the portfolio then chooses by the work each decomposition
    // implies rather than by width alone.
    let cheap = decompose_with(graph, Ordering::MinDegree, cap, Some(deadline))?;
    let td = decompose_portfolio(graph, cap, Some(deadline), &ORDERINGS[1..])
        .map(|(t, _)| t)
        .filter(|t| {
            use crate::graph::algorithms::steiner_td::work_estimate;
            work_estimate(t, graph.edges.len(), 1) <= work_estimate(&cheap, graph.edges.len(), 1)
        })
        .unwrap_or(cheap);
    if !td.verify(graph) {
        return None;
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
    let (cost, _) = steiner_tree_over_decomposition(
        graph,
        terminals,
        &td,
        TD_STATE_BUDGET,
        // The exact finish reports a value; nothing downstream wants the edge
        // set, so the tables can be freed as they die.
        false,
        Some(deadline),
    )?;
    Some((cost, started.elapsed().as_secs_f64()))
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
