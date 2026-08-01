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
    dijkstra_steiner_guided, dreyfus_wagner, dual_ascent_packing, ArcIndex,
};
use crate::graph::{costs_are_integral, tighten_dual, Cost, DirectedGraph, SteinerInstance, UndirectedGraph};
use crate::io;
use crate::model::{root_certificate, verify_solution};
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
    let mut incoming_ub = Cost::INFINITY;
    let mut best: Option<SolveResult> = None;

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
        let reduced = tighten(work_graph.clone(), terminals.clone(), &reduce_config);
        let tighten_secs = tighten_start.elapsed().as_secs_f64();
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
                "[time] pass {pass}: tighten took {:.2}s, search gets {:.2}s, elapsed {:.2}s",
                tighten_secs,
                pass_deadline.saturating_duration_since(Instant::now()).as_secs_f64(),
                start.elapsed().as_secs_f64(),
            );
        }
        let outcome = finish(reduced, &config, start, pass_deadline);
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
        if !b.primal_bound.is_finite() || b.primal_bound >= incoming_ub {
            break;
        }
        incoming_ub = b.primal_bound;
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
    let mut search_lower_bound = root_lower_bound;
    if terminals.len() >= 2 {
        // The search may be rooted at any terminal, and its potential is a
        // packing rooted at the same one. Which terminal is chosen was measured
        // and does not matter: over the terminals of the instances the search
        // fails to close, the ascent bound spans under 1 % (PACE 086: 3254 to
        // 3286 against an optimum of 3661) and is flat on 085 and 087. The
        // strength that is missing is not root-dependent.
        let search_terminals = terminals.clone();
        let directed = DirectedGraph::from_undirected(&work_graph);
        // The ascent's cut packing becomes the search's potential. This is the
        // whole point of running it here rather than only using its scalar
        // bound: the packing bounds every sub-requirement of the instance, not
        // only the instance, so it guides the search at every state instead of
        // only telling us how far off we are.
        let ascent_guide = {
            let idx = ArcIndex::new(&directed);
            let active = vec![true; idx.num_arcs()];
            // Rooted at the search's own root: the potential is only valid for
            // sets missing the root, and `PackingPotential` drops the rest.
            let da = dual_ascent_packing(
                &idx,
                search_terminals[0],
                &search_terminals,
                &active,
                DS_PACKING_NNZ,
            );
            da.sets
        };

        // Two attempts, and the second one is only paid for when the first
        // fails. The ascent's packing is *maximal* — no set missing the root
        // admits any increase — so when it is not strong enough there is no
        // combinatorial way to strengthen it. The LP on the same relaxation
        // reaches materially further, and `root_certificate` turns its dual back
        // into a packing. That LP is not free, so it is run only after the
        // cheap potential has been shown, by running it, not to suffice.
        let mut lp_guide: Vec<(Cost, Vec<crate::graph::NodeId>)> = Vec::new();
        // The graph the search runs on. The certificate's reduced-cost
        // elimination deletes edges no solution of cost at most the incumbent
        // can use, which shrinks the search's `n * 2^(k-1)` state space as well
        // as every Dijkstra inside it. `work_graph` itself is left alone: the
        // branch-and-cut below inherits an incumbent whose arc numbering belongs
        // to it.
        let mut search_graph = work_graph.clone();
        for attempt in 0..2 {
            let budget = deadline.saturating_duration_since(Instant::now());
            if budget.is_zero() {
                break;
            }
            // The first attempt keeps the share it always had, so an instance
            // the cheap potential already closes is untouched by any of this.
            // Everything the certificate costs comes out of what is left after
            // that attempt has failed.
            let search_deadline = Instant::now() + budget.mul_f64(0.5);
            let mut guides: Vec<&[(Cost, Vec<crate::graph::NodeId>)]> = vec![&ascent_guide];
            if !lp_guide.is_empty() {
                guides.push(&lp_guide);
            }
            if let Some(r) = dijkstra_steiner_guided(
                &search_graph,
                &search_terminals,
                root_upper_bound,
                DS_LABEL_BUDGET,
                Some(search_deadline),
                &guides,
            ) {
                if config.verbose {
                    eprintln!(
                        "[dsearch] attempt {attempt}: {} labels, optimal {:?}, lower bound {:.1}",
                        r.labels_settled, r.optimal, r.lower_bound
                    );
                }
                search_lower_bound = search_lower_bound.max(r.lower_bound);
                if let Some(value) = r.optimal {
                    // The search runs on the *reduced* graph, which keeps only
                    // trees at or below the incumbent, so the incumbent still
                    // wins ties.
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
            } else {
                // Out of the addressable range; a second attempt would fail the
                // same way.
                break;
            }
            if attempt == 1 {
                break;
            }
            // Build the stronger potential. Both its outputs are valid bounds on
            // the reduced instance: the LP's own optimum, and the packing's
            // value.
            let budget = deadline.saturating_duration_since(Instant::now());
            if budget.is_zero() {
                break;
            }
            let cert_deadline = Instant::now() + budget.mul_f64(0.25);
            let Some(cert) = root_certificate(
                &directed,
                search_terminals[0],
                &search_terminals,
                root_upper_bound,
                cert_deadline,
                ROOT_CERT_ROUNDS,
                DS_PACKING_NNZ,
            ) else {
                break;
            };
            search_lower_bound = search_lower_bound.max(cert.lp_bound).max(cert.packing.value);

            // An edge survives unless *both* of its arcs are eliminated: an
            // undirected edge is available to a tree as long as one orientation
            // is. `DirectedGraph::from_undirected` emits the two arcs of edge
            // `i` at positions `2i` and `2i+1`, which is the whole of the map.
            let mut dead = vec![false; directed.num_arcs() as usize];
            for &a in &cert.eliminated_arcs {
                dead[a as usize] = true;
            }
            // Read from `work_graph`, which is what `directed` — and therefore
            // the arc numbering in `dead` — was built from.
            let before = work_graph.edges.len();
            search_graph.edges = work_graph
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
                    search_graph.edges.len(),
                );
            }
            // Retry only when the object the search actually consumes got
            // stronger. The potential is the packing, so the test is on the
            // packing's own value: if it did not rise above the bound the first
            // attempt already ran under, the second attempt would sweep the same
            // state space against a potential no stronger at the root, and the
            // budget belongs to the branch-and-cut instead. This is a measured
            // fact about the two objects, not an estimate of how long a rerun
            // would take.
            if cert.packing.value <= root_lower_bound + 1e-9 {
                break;
            }
            lp_guide = cert.packing.sets;
        }
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
    // alongside a dual bound several percent below the primal — PACE instance200
    // was announced as a proved 6491 against a true optimum of 6393. This is the
    // last line of defence, and it is a cheap one.
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
