use super::Separator;
use crate::graph::{DirectedGraph, NodeId, ArcId};
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
        let mut violated_cuts = Vec::new();

        if self.workspace.is_none() {
            self.workspace = Some(MaxFlowWorkspace::new(self.graph));
        }
        let num_arcs = self.graph.arcs.len();
        self.capacities.clear();
        self.capacities
            .extend(lp_solution.iter().take(num_arcs).map(|&y| y + CREEP));
        self.capacities.resize(num_arcs, CREEP);

        // Stop once the round has enough material: the solver installs a bounded
        // number per round, and further max-flows are wasted work.
        let max_violated = 200;
        let mut seen: std::collections::HashSet<Vec<ArcId>> = std::collections::HashSet::new();

        'terminals: for &terminal in self.terminals {
            if terminal == self.root {
                continue;
            }

            for _ in 0..MAX_NESTED {
                let ws = self.workspace.as_mut().unwrap();
                let result = ws.compute(self.root, terminal, &self.capacities, &self.graph.arcs);
                if result.flow_value >= 1.0 - self.violation_tolerance {
                    break;
                }

                let source_side = result.source_side;
                let mut emitted = false;
                for arcs in [result.cut_arcs, result.sink_cut_arcs] {
                    if arcs.is_empty() {
                        continue;
                    }
                    // Score against the true LP values, never the creeping ones.
                    let load: f64 = arcs
                        .iter()
                        .map(|&a| lp_solution.get(a as usize).copied().unwrap_or(0.0))
                        .sum();
                    if load >= 1.0 - self.violation_tolerance {
                        continue;
                    }
                    let mut key = arcs.clone();
                    key.sort_unstable();
                    if !seen.insert(key) {
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

        // "Back-cut" separation: for Steiner nodes with fractional incoming flow,
        // check if the minimum cut separating them from the root is violated.
        // This finds nested cuts that terminal separation alone would miss.
        if violated_cuts.is_empty() {
            let mut steiner_candidates: Vec<(NodeId, f64)> = Vec::new();
            for node in &self.graph.nodes {
                if self.terminals.contains(&node.id) || node.id == self.root {
                    continue;
                }
                // Compute total incoming flow to this Steiner node
                let in_flow: f64 = self.graph.delta_minus(node.id).iter()
                    .map(|&(_, aid)| lp_solution.get(aid as usize).copied().unwrap_or(0.0))
                    .sum();
                if in_flow > 0.01 && in_flow < 0.999 {
                    steiner_candidates.push((node.id, in_flow));
                }
            }

            // Sort by fractionality (most fractional first)
            steiner_candidates.sort_by(|a, b| {
                let frac_a = (a.1 - 0.5).abs();
                let frac_b = (b.1 - 0.5).abs();
                frac_a.partial_cmp(&frac_b).unwrap_or(std::cmp::Ordering::Equal)
            });

            let ws = self.workspace.as_mut().unwrap();
            for &(node, in_flow) in steiner_candidates.iter().take(10) {
                let result = ws.compute(self.root, node, lp_solution, &self.graph.arcs);
                if result.flow_value < in_flow - self.violation_tolerance {
                    let violation = in_flow - result.flow_value;
                    if violation > self.violation_tolerance {
                        violated_cuts.push(SteinerCut {
                            cut_set: result.source_side,
                            cut_arcs: result.cut_arcs,
                            separated_terminal: node,
                            violation,
                        });
                    }
                }
            }
        }

        violated_cuts.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(std::cmp::Ordering::Equal));

        self.cuts_found = violated_cuts.len() as u32;
        self.total_cuts_generated += self.cuts_found;

        violated_cuts
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
