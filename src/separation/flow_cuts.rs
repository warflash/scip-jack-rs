use super::Separator;
use crate::graph::{cmp_cost, DirectedGraph, NodeId, ArcId};
use crate::graph::algorithms::MaxFlowWorkspace;

/// Separates violated directed cut constraints (Steiner cuts).
///
/// For each terminal `t` other than the root, compute the maximum flow from the
/// root to `t` with arc capacities taken from the LP solution. If the flow is
/// below one, the corresponding minimum cut is a violated Steiner cut
/// `y(delta+(W)) >= 1`.
///
/// # Getting more than one cut per flow
///
/// The naive routine emits one inequality per terminal per round, which makes
/// the cut loop converge very slowly: on PACE instance141 thirty rounds moved
/// the bound by a tenth of the remaining gap while each round's LP re-solve cost
/// tens of milliseconds. Two standard devices (Koch and Martin, *Solving Steiner
/// tree problems in graphs to optimality*, Networks 32, 1998) multiply the yield:
///
/// - **Back cuts.** When the minimum cut is not unique, the one nearest the root
///   and the one nearest the terminal are different inequalities. Both come out
///   of the same residual graph, so the second is free.
/// - **Nested cuts.** After emitting a cut, raise the capacity of its arcs to one
///   and recompute the flow. The next minimum cut is a *different* violated
///   inequality, and because raising capacities can only raise the flow, a cut
///   found this way has capacity below one under the original solution too - so
///   it is genuinely violated by the point being separated.
///
/// Every inequality emitted is checked against the true LP values before being
/// returned, so the modified capacities can never smuggle in a satisfied row.
///
/// # Creep flow
///
/// Capacities carry a tiny additive epsilon. Among the many minimum cuts of a
/// degenerate solution this biases the search towards the one with fewest arcs,
/// which is both a sparser row for the LP and a stronger inequality.
pub struct FlowCutSeparator<'a> {
    pub graph: &'a DirectedGraph,
    pub root: NodeId,
    pub terminals: &'a [NodeId],
    pub cuts_found: u32,
    pub total_cuts_generated: u32,
    pub violation_tolerance: f64,
    workspace: Option<MaxFlowWorkspace>,
    capacities: Vec<f64>,
    /// Terminals whose Steiner cut was violated the last time this separator
    /// looked at them. See [`FlowCutSeparator::find_violated_cuts`].
    active: Vec<NodeId>,
    /// What this separator's last *complete* sweep over the terminals cost, in
    /// seconds, on this instance. Measured, not configured.
    last_full_secs: f64,
    /// What the LP solve that produced the point being separated cost, as the
    /// caller measured it. Infinite — the default — makes the complete sweep
    /// unconditionally the cheaper of the two and so reproduces the sweep this
    /// separator has always done, exactly. A caller that does not measure its own
    /// LP is therefore unchanged, which is what keeps the branch-and-cut (§135)
    /// out of a trade nobody measured for it.
    pub lp_secs: f64,
    /// The last pass ran out of clock before it had looked at every terminal it
    /// meant to. See [`FlowCutSeparator::was_truncated`].
    truncated: bool,
    /// Canonical cut signatures reused across sweeps. The rows themselves are
    /// returned to the caller, but retaining the hash table avoids rebuilding
    /// its buckets for every LP round.
    seen: std::collections::HashSet<Vec<ArcId>>,
}

/// Cuts emitted per terminal before moving on. Nested cuts are disjoint by
/// construction, so a handful per terminal is already a large family.
const MAX_NESTED: usize = 4;
/// Additive capacity bias that steers the minimum cut towards fewer arcs.
const CREEP: f64 = 1e-6;

/// A separated Steiner cut constraint.
#[derive(Debug, Clone)]
pub struct SteinerCut {
    /// The set W (source side of the min-cut, containing root)
    pub cut_set: Vec<NodeId>,
    /// Arcs crossing the cut δ+(W)
    pub cut_arcs: Vec<ArcId>,
    /// The terminal that caused this cut to be found
    pub separated_terminal: NodeId,
    /// Amount of violation: 1 - y(δ+(W))
    pub violation: f64,
}

impl<'a> FlowCutSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph, root: NodeId, terminals: &'a [NodeId]) -> Self {
        Self {
            graph,
            root,
            terminals,
            cuts_found: 0,
            total_cuts_generated: 0,
            violation_tolerance: 1e-6,
            workspace: None,
            capacities: Vec::new(),
            active: Vec::new(),
            last_full_secs: 0.0,
            lp_secs: f64::INFINITY,
            truncated: false,
            seen: std::collections::HashSet::new(),
        }
    }

    /// Find all violated Steiner cuts given the current LP solution.
    /// Returns the list of violated cuts sorted by violation (most violated first).
    ///
    /// Checks both standard terminal cuts AND nested Steiner-node cuts:
    /// - Standard: max-flow(root, t) < 1 for each terminal t
    /// - Nested: when a terminal cut is found, also check sub-cuts within
    ///   the sink side for additional violated constraints
    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<SteinerCut> {
        // ## Why a round does not sweep every terminal
        //
        // A complete sweep is `|R|` max flows and it is what the loop spends its
        // seconds on. PACE Track 2 instance096, root cut loop run to convergence
        // with the dual simplex, per round from `lpstar_probe`:
        //
        // ```text
        // round 15  cuts  4   lp 0.028  flow 0.197
        // round 17  cuts  2   lp 0.026  flow 0.170
        // round 19  cuts  4   lp 0.024  flow 0.179
        // ```
        //
        // Every late round pays 305 max flows to find two to four violated cuts,
        // and the flow separation is 3.88 s of the 5.56 s the loop takes to
        // converge -- four times the LP it is feeding.
        //
        // > **Proposition (the short list cannot change what the loop proves).**
        // > Let `A` be any set of terminals. A pass over `A` emits only rows it
        // > has checked against the true LP values, so every row it emits is a
        // > valid inequality violated by the point, whatever `A` is. And the only
        // > conclusion the loop draws from an *empty* separation is that the point
        // > is feasible for this family: that conclusion is reached here only
        // > after a pass over **all** the terminals, because an empty short pass
        // > is followed by the complete one before anything is returned. So the
        // > short list changes which violated rows are found first, and never
        // > which points are separable. QED
        //
        // The list is self-regulating rather than tuned: the first rounds violate
        // hundreds of terminals and the pass is nearly complete; it thins as the
        // point approaches feasibility, which is exactly where the seconds were.
        //
        // ## When the short list is *not* worth taking
        //
        // A short pass finds fewer rows than a complete one, so the loop needs
        // more rounds, and a round costs an LP solve. That is a straight trade
        // between two costs this loop measures on this instance: what a complete
        // sweep costs it, and what the solve that produced this point cost it.
        // Both are seconds already spent, neither is a share of any budget, and
        // the comparison reads the same at a one-second limit and at a
        // thousand-second one.
        //
        // Measured, converging the root cut loop to `BCR*` with the dual simplex,
        // seconds in the LP against seconds in the separation:
        //
        // | instance | complete sweep | LP per solve | which dominates |
        // |---|---|---|---|
        // | instance130 |  0.01 s | 0.11 s | the LP -- sweep completely |
        // | instance064 |  0.09 s | 0.03 s | the flow -- use the short list |
        // | instance096 |  0.18 s | 0.04 s | the flow -- use the short list |
        //
        // and the short list unconditional costs instance130 111 extra solves
        // while saving 0.2 s of flow, and saves instance096 2.5 s of 5.6 s.
        if self.workspace.is_none() {
            self.workspace = Some(MaxFlowWorkspace::new(self.graph));
        }

        self.truncated = false;
        let mut violated_cuts = Vec::new();
        let mut short = Vec::new();
        if !self.active.is_empty() && self.last_full_secs > self.lp_secs {
            short = std::mem::take(&mut self.active);
            violated_cuts = self.sweep(lp_solution, &short);
        }
        let mut complete = violated_cuts.is_empty();
        if complete {
            let all: &[NodeId] = self.terminals;
            let t0 = std::time::Instant::now();
            violated_cuts = self.sweep(lp_solution, all);
            self.last_full_secs = t0.elapsed().as_secs_f64();
        }
        // A sweep the clock cut short has not looked at every terminal, so its
        // emptiness proves nothing and the proposition above does not apply to
        // it. `was_truncated` is what the caller must consult before reading an
        // empty separation as convergence.
        if self.truncated {
            complete = false;
        }

        // The terminals this pass found something for are the ones worth asking
        // again; the rest drop out, and a complete sweep is what puts any of them
        // back. A truncated pass names nobody, because it did not look: the list
        // it started from is kept intact instead.
        if self.truncated {
            for t in short {
                if !self.active.contains(&t) {
                    self.active.push(t);
                }
            }
        } else {
            self.active.clear();
        }
        for c in &violated_cuts {
            if !self.active.contains(&c.separated_terminal) {
                self.active.push(c.separated_terminal);
            }
        }

        // "Back-cut" separation: for Steiner nodes with fractional incoming flow,
        // check if the minimum cut separating them from the root is violated.
        // This finds nested cuts that terminal separation alone would miss. It is
        // asked only when a *complete* sweep over the terminals found nothing,
        // which is the state it was written for.
        if complete && violated_cuts.is_empty() {
            let mut steiner_candidates: Vec<(NodeId, f64)> = Vec::new();
            for node in &self.graph.nodes {
                if self.terminals.contains(&node.id) || node.id == self.root {
                    continue;
                }
                // Compute total incoming flow to this Steiner node
                let in_flow: f64 = self.graph.delta_minus(node.id).iter()
                    .map(|&(_, aid)| lp_solution[aid as usize])
                    .sum();
                if in_flow > 0.01 && in_flow < 0.999 {
                    steiner_candidates.push((node.id, in_flow));
                }
            }

            // Sort by fractionality (most fractional first)
            steiner_candidates.sort_by(|a, b| {
                let frac_a = (a.1 - 0.5).abs();
                let frac_b = (b.1 - 0.5).abs();
                cmp_cost(frac_a, frac_b)
            });

            let ws = self.workspace.as_mut().unwrap();
            for &(node, in_flow) in steiner_candidates.iter().take(10) {
                let result = ws.compute_view_without_sink(self.root, node, lp_solution, &self.graph.arcs);
                if result.flow_value < in_flow - self.violation_tolerance
                    && in_flow - result.flow_value > self.violation_tolerance
                {
                    violated_cuts.push(SteinerCut {
                        cut_set: result.source_side.to_vec(),
                        cut_arcs: result.cut_arcs.to_vec(),
                        separated_terminal: node,
                        violation: in_flow - result.flow_value,
                    });
                }
            }
        }

        violated_cuts.sort_by(|a, b| cmp_cost(b.violation, a.violation));

        self.cuts_found = violated_cuts.len() as u32;
        self.total_cuts_generated += self.cuts_found;

        violated_cuts
    }

    /// One pass of nested-and-back cut separation over `order`.
    ///
    /// Capacities are rebuilt from the LP point at entry, so a pass never
    /// inherits the saturations an earlier pass made in order to force nested
    /// cuts out of the same flow.
    fn sweep(&mut self, lp_solution: &[f64], order: &[NodeId]) -> Vec<SteinerCut> {
        let mut violated_cuts = Vec::new();
        let num_arcs = self.graph.arcs.len();
        self.capacities.clear();
        self.capacities
            .extend(lp_solution.iter().take(num_arcs).map(|&y| y + CREEP));
        self.capacities.resize(num_arcs, CREEP);

        // Stop once the round has enough material: the solver installs a bounded
        // number per round, and further max-flows are wasted work.
        let max_violated = 200;
        self.seen.clear();

        'terminals: for &terminal in order {
            if terminal == self.root {
                continue;
            }
            // One max flow per terminal, and on the wide instances there are
            // thousands of them: PACE Track 2's instance079 has 16,808 after a
            // classical reduction that deletes nothing. Stopping returns the rows
            // found so far, every one of them checked against the point, which is
            // a refusal the caller already tolerates -- but it also means this
            // pass is *not* the complete sweep the convergence test needs, and
            // `truncated` is what says so. See [`crate::deadline`].
            if crate::deadline::expired() {
                self.truncated = true;
                break 'terminals;
            }

            for _ in 0..MAX_NESTED {
                let ws = self.workspace.as_mut().unwrap();
                // First compute only the source-side cut. The backward residual
                // sweep for the sink-nearest variant is needed only when this
                // flow is actually violated.
                let flow_value = {
                    let result = ws.compute_view_until(
                        self.root, terminal, &self.capacities, &self.graph.arcs,
                        1.0 - self.violation_tolerance,
                    );
                    result.flow_value
                };
                if flow_value >= 1.0 - self.violation_tolerance {
                    break;
                }

                let result = ws.finish_sink_cut(terminal, &self.graph.arcs, flow_value);
                let source_side = result.source_side.to_vec();
                let cut_arcs = result.cut_arcs.to_vec();
                let sink_cut_arcs = result.sink_cut_arcs.to_vec();
                drop(result);
                let mut emitted = false;
                for arcs in [cut_arcs, sink_cut_arcs] {
                    if arcs.is_empty() {
                        continue;
                    }
                    // Score against the true LP values, never the creeping ones.
                    let load: f64 = arcs
                        .iter()
                        .map(|&a| lp_solution[a as usize])
                        .sum();
                    if load >= 1.0 - self.violation_tolerance {
                        continue;
                    }
                    // MaxFlowWorkspace scans the graph's arc array in id order,
                    // so both cut variants are already canonical. Sorting the
                    // same row again was pure separator overhead on every
                    // nested flow.
                    if !self.seen.insert(arcs.clone()) {
                        continue;
                    }
                    // Saturating the emitted arcs is what makes the next flow
                    // find a different cut.
                    for &a in &arcs {
                        self.capacities[a as usize] = 1.0;
                    }
                    violated_cuts.push(SteinerCut {
                        cut_set: source_side.clone(),
                        cut_arcs: arcs,
                        separated_terminal: terminal,
                        violation: 1.0 - load,
                    });
                    emitted = true;
                }

                if !emitted || violated_cuts.len() >= max_violated {
                    break;
                }
            }
            if violated_cuts.len() >= max_violated {
                break 'terminals;
            }
        }

        violated_cuts
    }

    /// Whether the last separation ran out of clock before looking at every
    /// terminal.
    ///
    /// An empty answer from a truncated pass says nothing about the point; a
    /// caller that reads emptiness as "this family is satisfied" -- which is what
    /// declaring a cut loop converged means -- must check this first.
    pub fn was_truncated(&self) -> bool {
        self.truncated
    }

    /// Separate cuts and return the number found.
    /// This is the main interface called during the branch-and-cut loop.
    pub fn separate_cuts(&mut self, lp_solution: &[f64]) -> Vec<SteinerCut> {
        self.find_violated_cuts(lp_solution)
    }
}

impl<'a> Separator for FlowCutSeparator<'a> {
    fn separate(&mut self, lp_solution: &[f64]) -> u32 {
        let cuts = self.find_violated_cuts(lp_solution);
        cuts.len() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    /// A cheap deterministic generator: `seed` picks the graph and the point.
    fn scramble(x: &mut u64) -> u64 {
        *x ^= *x << 13;
        *x ^= *x >> 7;
        *x ^= *x << 17;
        *x
    }

    /// The proposition the short list rests on, exercised rather than asserted.
    ///
    /// `find_violated_cuts` may look at a subset of the terminals, so the only
    /// thing that must be protected is the meaning of an *empty* answer: when it
    /// returns nothing, the point really does satisfy every terminal's Steiner
    /// cut. This drives the separator through a sequence of points on random
    /// graphs -- which is what builds up and thins out its active list -- and
    /// checks each empty answer against an independent max flow per terminal.
    ///
    /// It also checks the other half: every row that *is* emitted is violated
    /// under the true LP values, whichever pass produced it.
    #[test]
    fn an_empty_separation_means_every_terminal_is_covered() {
        let mut seed = 0x9E3779B97F4A7C15u64;
        let (mut checked_empty, mut checked_rows) = (0usize, 0usize);
        for case in 0..120 {
            let n = 6 + (scramble(&mut seed) % 9) as u32;
            let mut g = DirectedGraph::new(n);
            let mut terminals: Vec<NodeId> = Vec::new();
            for v in 1..=n {
                let terminal = v == 1 || scramble(&mut seed) % 3 == 0;
                g.add_node(
                    v,
                    if terminal { NodeType::Terminal } else { NodeType::Steiner },
                    0.0,
                );
                if terminal {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in 1..=n {
                    if u != v && scramble(&mut seed) % 4 == 0 {
                        g.add_arc(u, v, 1.0 + (scramble(&mut seed) % 5) as f64);
                    }
                }
            }
            if terminals.len() < 2 || g.arcs.is_empty() {
                continue;
            }
            let root = terminals[0];
            // A terminal the root cannot reach at all makes the instance
            // infeasible, and the min cut separating it is the empty arc set --
            // the row `0 >= 1`, which no separator here emits and which the
            // formulation has no way to state. That is outside this separator's
            // contract and outside the pipeline, whose graphs are connected by
            // the time an LP is built, so those terminals are dropped.
            let mut reach = vec![false; g.nodes.len() + 2];
            let mut stack = vec![root];
            reach[root as usize] = true;
            while let Some(v) = stack.pop() {
                for &(w, _) in g.delta_plus(v) {
                    if !reach[w as usize] {
                        reach[w as usize] = true;
                        stack.push(w);
                    }
                }
            }
            terminals.retain(|&t| reach[t as usize]);
            if terminals.len() < 2 {
                continue;
            }
            let mut sep = FlowCutSeparator::new(&g, root, &terminals);
            // A few points in a row, so the active list is carried between them
            // exactly as the cut loop carries it between rounds.
            for step in 0..6 {
                let point: Vec<f64> = (0..g.arcs.len())
                    .map(|_| match scramble(&mut seed) % 4 {
                        0 => 0.0,
                        1 => (scramble(&mut seed) % 100) as f64 / 100.0,
                        _ => 1.0,
                    })
                    .collect();
                // Both regimes of the measured dispatch get exercised.
                sep.lp_secs = if step % 2 == 0 { 0.0 } else { f64::INFINITY };
                let cuts = sep.find_violated_cuts(&point);
                for c in &cuts {
                    let load: f64 =
                        c.cut_arcs.iter().map(|&a| point[a as usize]).sum();
                    assert!(
                        load < 1.0 + 1e-6,
                        "case {case} step {step}: emitted a row of load {load}",
                    );
                    checked_rows += 1;
                }
                if !cuts.is_empty() {
                    continue;
                }
                // Empty: verify independently that no terminal is separable.
                let mut ws = crate::graph::algorithms::MaxFlowWorkspace::new(&g);
                for &t in &terminals {
                    if t == root {
                        continue;
                    }
                    let f = ws.compute(root, t, &point, &g.arcs).flow_value;
                    assert!(
                        f >= 1.0 - 1e-6,
                        "case {case} step {step}: separation was empty but the flow \
                         to terminal {t} is {f}",
                    );
                }
                checked_empty += 1;
            }
        }
        assert!(
            checked_empty > 20 && checked_rows > 200,
            "the generator did not reach both outcomes: {checked_empty} empty \
             separations and {checked_rows} emitted rows",
        );
    }

    fn build_stp_graph() -> DirectedGraph {
        // Simple graph:
        //    1 (root)
        //   / \
        //  2   3
        //   \ /
        //    4 (terminal)
        //
        // Arcs: 1->2, 1->3, 2->4, 3->4
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0); // arc 0
        g.add_arc(1, 3, 1.0); // arc 1
        g.add_arc(2, 4, 1.0); // arc 2
        g.add_arc(3, 4, 1.0); // arc 3
        g
    }

    #[test]
    fn test_no_violated_cuts_when_feasible() {
        let g = build_stp_graph();
        let terminals = vec![1, 4];
        let mut separator = FlowCutSeparator::new(&g, 1, &terminals);

        // Feasible LP solution: arc 1->2 = 1.0, 2->4 = 1.0 (one full path)
        let lp = vec![1.0, 0.0, 1.0, 0.0];
        let cuts = separator.find_violated_cuts(&lp);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_violated_cut_found() {
        let g = build_stp_graph();
        let terminals = vec![1, 4];
        let mut separator = FlowCutSeparator::new(&g, 1, &terminals);

        // Infeasible LP: all arcs at 0.3, total flow to 4 = 0.6 < 1.
        // The root-side cut is `delta+({1}) = {0, 1}` and the terminal-side cut
        // is `delta-({4}) = {2, 3}`; both are separated from one flow.
        let lp = vec![0.3, 0.3, 0.3, 0.3];
        let cuts = separator.find_violated_cuts(&lp);

        assert_eq!(cuts.len(), 2, "root-side and terminal-side cuts");
        for cut in &cuts {
            assert_eq!(cut.separated_terminal, 4);
            let load: f64 = cut.cut_arcs.iter().map(|&a| lp[a as usize]).sum();
            assert!(load < 1.0 - 1e-9, "emitted a satisfied cut, load {load}");
            assert!((cut.violation - (1.0 - load)).abs() < 1e-9);
        }
        let mut families: Vec<Vec<ArcId>> = cuts.iter().map(|c| c.cut_arcs.clone()).collect();
        families.iter_mut().for_each(|f| f.sort_unstable());
        families.sort();
        assert_eq!(families, vec![vec![0, 1], vec![2, 3]]);
    }

    /// The nested loop raises capacities as it goes, so the guard that every
    /// emitted row is scored against the *original* solution is what keeps it
    /// honest. This pins that guard.
    #[test]
    fn every_emitted_cut_is_violated_by_the_point_being_separated() {
        let g = build_stp_graph();
        let terminals = vec![1, 4];
        let mut separator = FlowCutSeparator::new(&g, 1, &terminals);

        for lp in [
            vec![0.3, 0.3, 0.3, 0.3],
            vec![0.9, 0.05, 0.9, 0.05],
            vec![0.5, 0.5, 0.4, 0.4],
            vec![1.0, 0.0, 0.6, 0.0],
        ] {
            for cut in separator.find_violated_cuts(&lp) {
                let load: f64 = cut.cut_arcs.iter().map(|&a| lp[a as usize]).sum();
                assert!(load < 1.0 - 1e-9, "cut {:?} has load {load} on {lp:?}", cut.cut_arcs);
            }
        }
    }

    #[test]
    fn test_multiple_terminals() {
        // Graph: 1 -> 2, 1 -> 3, terminals at 2 and 3
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0); // arc 0
        g.add_arc(1, 3, 1.0); // arc 1

        let terminals = vec![1, 2, 3];
        let mut separator = FlowCutSeparator::new(&g, 1, &terminals);

        // LP: both arcs at 0.4 → both terminals have violated cuts
        let lp = vec![0.4, 0.4];
        let cuts = separator.find_violated_cuts(&lp);
        assert_eq!(cuts.len(), 2);

        // LP: both arcs at 1.0 → no violated cuts
        let lp = vec![1.0, 1.0];
        let cuts = separator.find_violated_cuts(&lp);
        assert!(cuts.is_empty());
    }

    #[test]
    fn test_cut_set_contains_root() {
        let g = build_stp_graph();
        let terminals = vec![1, 4];
        let mut separator = FlowCutSeparator::new(&g, 1, &terminals);

        let lp = vec![0.2, 0.2, 0.2, 0.2];
        let cuts = separator.find_violated_cuts(&lp);

        assert!(!cuts.is_empty());
        // The cut set W must contain the root
        assert!(cuts[0].cut_set.contains(&1));
        // And must NOT contain the separated terminal
        assert!(!cuts[0].cut_set.contains(&4));
    }
}
