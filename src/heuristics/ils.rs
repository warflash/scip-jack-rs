//! Iterated local search: what turns a construction heuristic into a primal
//! bound worth eliminating against.
//!
//! # Why more restarts are not the answer
//!
//! The shortest-path heuristic run from `k` different starts explores a very
//! narrow set of trees: every run is greedy against the same arc costs, so the
//! runs differ only in which terminal happened to go first. On the larger PACE
//! instances sixty-four such starts land two to three percent above the optimum
//! and the sixty-fourth is no better than the fourth — while costing sixty-four
//! multi-source Dijkstras each.
//!
//! That matters far beyond the reported primal value. Every reduced-cost
//! elimination is measured against `UB - LB`; an incumbent two percent high
//! deletes nothing, and the branch-and-cut then starts on the full graph.
//!
//! # The loop
//!
//! One iteration is
//!
//! ```text
//! perturb the arc costs
//! -> shortest-path heuristic on the perturbed costs
//! -> key-path exchange against the true costs
//! -> merge with the incumbent
//! -> key-path exchange again
//! ```
//!
//! Perturbation is what escapes the local optimum; the merge is what keeps the
//! escape from losing the ground already gained.
//!
//! Two perturbations alternate, and the pair is the point:
//!
//! - *intensifying*: arcs of the incumbent keep their true cost, every other arc
//!   is scaled up by a random factor in `[1, 1+lambda]`. The construction is
//!   pushed to reuse the incumbent's corridors and differs from it only where the
//!   random draw made an alternative genuinely competitive.
//! - *diversifying*: arcs of the incumbent are scaled up instead. The
//!   construction is pushed away from the incumbent entirely, which is the only
//!   way out of a basin that intensification keeps falling back into.
//!
//! # Why the merge is free of risk
//!
//! [`mst_prune`] returns the cheapest tree inside the subgraph induced on the
//! vertex set it is given, so feeding it `V(A) ∪ V(B)` returns something no worse
//! than either `A` or `B` — both are trees inside that subgraph. The merge can
//! therefore only improve the incumbent, and it frequently does strictly better
//! than both parents by taking a cheap corridor from each.
//!
//! Every tree is scored with the true arc costs; the perturbed costs only ever
//! steer which tree gets built.

use std::time::Instant;

use crate::graph::algorithms::ArcIndex;
use crate::graph::{ArcId, Cost, NodeId};

use super::key_path::{key_path_exchange, KeyPathWorkspace};
use super::sph::{mst_prune, shortest_path_heuristic, SphResult, SphWorkspace};

/// Relative size of the random cost perturbation.
const LAMBDA: Cost = 0.6;

/// Key-path passes applied to each candidate.
const POLISH_PASSES: u32 = 6;

/// Consecutive iterations without an improvement before the loop concludes it
/// has converged.
///
/// A stopping rule of this shape is what makes the search self-scaling: it keeps
/// going exactly as long as perturbation is still finding something, and returns
/// immediately on an instance the construction already solved. Running to a clock
/// instead would spend the same time on every instance regardless of whether
/// there was anything left to find.
const STALL_LIMIT: u32 = 50;

/// Deterministic xorshift, so a run is reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// Uniform in `[0, 1)`.
    fn unit(&mut self) -> Cost {
        (self.next() >> 11) as Cost / (1u64 << 53) as Cost
    }
}

/// Scratch buffers, so an iteration allocates nothing.
pub struct IlsWorkspace {
    weights: Vec<Cost>,
    in_best: Vec<bool>,
    nodes: Vec<NodeId>,
    rng: Rng,
}

impl IlsWorkspace {
    pub fn new(num_arcs: usize) -> Self {
        Self {
            weights: vec![0.0; num_arcs],
            in_best: vec![false; num_arcs],
            nodes: Vec::new(),
            rng: Rng(0x2545_F491_4F6C_DD1D),
        }
    }
}

/// Improve on `seed` until it converges.
///
/// The loop stops at whichever comes first: a tree meeting `lower_bound`, which
/// is a proof of optimality and leaves nothing to find; [`STALL_LIMIT`]
/// consecutive iterations without an improvement; `max_iters`; or `deadline`.
///
/// Returns the best tree found, which is never worse than `seed`.
#[allow(clippy::too_many_arguments)]
pub fn iterated_local_search(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    terminals: &[NodeId],
    is_terminal: &[bool],
    seed: SphResult,
    lower_bound: Cost,
    max_iters: u32,
    deadline: Option<Instant>,
    ws: &mut IlsWorkspace,
    sws: &mut SphWorkspace,
    kws: &mut KeyPathWorkspace,
) -> SphResult {
    let num_arcs = idx.num_arcs();
    if ws.weights.len() < num_arcs {
        ws.weights.resize(num_arcs, 0.0);
        ws.in_best.resize(num_arcs, false);
    }

    let mut best = polish(idx, active, root, seed, is_terminal, sws, kws);
    if terminals.len() < 2 {
        return best;
    }

    let expired = || deadline.is_some_and(|d| Instant::now() >= d);
    let mut stalled = 0u32;

    for iter in 0..max_iters {
        if expired() || stalled >= STALL_LIMIT || best.cost <= lower_bound + 1e-9 {
            break;
        }

        mark(idx, &best.arcs, &mut ws.in_best);
        let diversify = iter % 2 == 1;
        for a in 0..num_arcs {
            let c = idx.cost(a as ArcId);
            let penalised = ws.in_best[a] == diversify;
            ws.weights[a] = if penalised {
                c * (1.0 + LAMBDA * ws.rng.unit())
            } else {
                c
            };
        }

        let start = terminals[(ws.rng.next() % terminals.len() as u64) as usize];
        let Some(candidate) = shortest_path_heuristic(
            idx, active, &ws.weights, root, start, terminals, is_terminal, sws,
        ) else {
            unmark(idx, &best.arcs, &mut ws.in_best);
            continue;
        };
        unmark(idx, &best.arcs, &mut ws.in_best);

        let candidate = polish(idx, active, root, candidate, is_terminal, sws, kws);

        // Merge: the cheapest tree inside `V(candidate) union V(best)` is no
        // worse than either.
        ws.nodes.clear();
        ws.nodes.push(root);
        for r in [&candidate, &best] {
            for &a in &r.arcs {
                ws.nodes.push(idx.tail(a));
                ws.nodes.push(idx.head(a));
            }
        }
        ws.nodes.sort_unstable();
        ws.nodes.dedup();
        let merged = mst_prune(idx, active, root, &ws.nodes, is_terminal, sws)
            .map(|m| polish(idx, active, root, m, is_terminal, sws, kws));

        stalled += 1;
        for r in [Some(candidate), merged].into_iter().flatten() {
            if r.cost < best.cost - 1e-9 {
                best = r;
                stalled = 0;
            }
        }
    }

    best
}

fn polish(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    r: SphResult,
    is_terminal: &[bool],
    sws: &mut SphWorkspace,
    kws: &mut KeyPathWorkspace,
) -> SphResult {
    match key_path_exchange(idx, active, root, &r, is_terminal, POLISH_PASSES, kws, sws) {
        Some(better) if better.cost < r.cost => better,
        _ => r,
    }
}

/// Mark both orientations of every edge the tree uses.
fn mark(idx: &ArcIndex, arcs: &[ArcId], flags: &mut [bool]) {
    let n = idx.num_arcs();
    for &a in arcs {
        flags[a as usize] = true;
        let twin = (a ^ 1) as usize;
        if twin < n {
            flags[twin] = true;
        }
    }
}

fn unmark(idx: &ArcIndex, arcs: &[ArcId], flags: &mut [bool]) {
    let n = idx.num_arcs();
    for &a in arcs {
        flags[a as usize] = false;
        let twin = (a ^ 1) as usize;
        if twin < n {
            flags[twin] = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType, UndirectedGraph};

    fn setup(g: &UndirectedGraph, terminals: &[NodeId]) -> (DirectedGraph, Vec<bool>) {
        let d = DirectedGraph::from_undirected(g);
        let mut is_t = vec![false; d.num_nodes as usize + 1];
        for &t in terminals {
            is_t[t as usize] = true;
        }
        (d, is_t)
    }

    /// A ladder whose greedy solution is not optimal: the construction commits to
    /// an expensive rung that the perturbed restarts have to walk away from.
    #[test]
    fn escapes_a_greedy_local_optimum() {
        //   1 --1-- 2 --1-- 3 --1-- 4      (terminals 1 and 4)
        //   |                       |
        //   +---------- 9 ----------+      the direct chord
        // plus a decoy: 1 --2-- 5 --2-- 4
        let mut g = UndirectedGraph::new(5);
        for v in 1..=5u32 {
            let t = v == 1 || v == 4;
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(1, 4, 9.0);
        g.add_edge(1, 5, 2.0);
        g.add_edge(5, 4, 2.0);

        let terminals = vec![1, 4];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let mut sws = SphWorkspace::new(idx.num_nodes());
        let mut kws = KeyPathWorkspace::new(idx.num_nodes());
        let mut ws = IlsWorkspace::new(idx.num_arcs());

        let seed = shortest_path_heuristic(
            &idx, &active, &(0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect::<Vec<_>>(),
            1, 1, &terminals, &is_t, &mut sws,
        )
        .expect("feasible");

        let best = iterated_local_search(
            &idx, &active, 1, &terminals, &is_t, seed, 0.0, 400, None, &mut ws, &mut sws, &mut kws,
        );
        assert!((best.cost - 3.0).abs() < 1e-9, "expected 3, got {}", best.cost);
    }

    /// The loop never returns something worse than what it was handed.
    #[test]
    fn never_degrades_the_seed() {
        let mut seed_state = 0xA5A5_1234_9876_FEEDu64;
        let mut rng = move || {
            seed_state ^= seed_state << 13;
            seed_state ^= seed_state >> 7;
            seed_state ^= seed_state << 17;
            seed_state
        };

        for _ in 0..60 {
            let n = 8 + (rng() % 8) as u32;
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
                        g.add_edge(u, v, 1.0 + (rng() % 20) as f64);
                    }
                }
            }

            let (d, is_t) = setup(&g, &terminals);
            let idx = ArcIndex::new(&d);
            let active = vec![true; idx.num_arcs()];
            let costs: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
            let mut sws = SphWorkspace::new(idx.num_nodes());
            let mut kws = KeyPathWorkspace::new(idx.num_nodes());
            let mut ws = IlsWorkspace::new(idx.num_arcs());

            let Some(seed) = shortest_path_heuristic(
                &idx, &active, &costs, terminals[0], terminals[0], &terminals, &is_t, &mut sws,
            ) else {
                continue;
            };
            let before = seed.cost;
            let best = iterated_local_search(
                &idx, &active, terminals[0], &terminals, &is_t, seed, 0.0, 200, None, &mut ws,
                &mut sws, &mut kws,
            );
            assert!(best.cost <= before + 1e-9, "{} > {before}", best.cost);

            // And it is a real tree: every terminal reachable from the root.
            let mut reached = vec![false; idx.num_nodes()];
            reached[terminals[0] as usize] = true;
            let mut changed = true;
            while changed {
                changed = false;
                for &a in &best.arcs {
                    if reached[idx.tail(a) as usize] && !reached[idx.head(a) as usize] {
                        reached[idx.head(a) as usize] = true;
                        changed = true;
                    }
                }
            }
            assert!(terminals.iter().all(|&t| reached[t as usize]));
        }
    }
}
