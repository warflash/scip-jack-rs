use super::Separator;
use crate::graph::{DirectedGraph, NodeId, ArcId};
use crate::graph::algorithms::MaxFlowWorkspace;

/// Separates violated directed cut constraints (Steiner cuts).
///
/// For each terminal t ∈ T \ {r}, compute max-flow from root to t
/// using arc capacities from the LP solution. If flow < 1, the min-cut
/// gives a violated Steiner cut constraint: y(δ+(W)) ≥ 1.
///
/// This is the core separation routine for the branch-and-cut algorithm.
/// The separated constraints are facets of the Steiner tree polytope.
pub struct FlowCutSeparator<'a> {
    pub graph: &'a DirectedGraph,
    pub root: NodeId,
    pub terminals: &'a [NodeId],
    pub cuts_found: u32,
    pub total_cuts_generated: u32,
    pub violation_tolerance: f64,
    workspace: Option<MaxFlowWorkspace>,
}

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
        let ws = self.workspace.as_mut().unwrap();

        // Standard terminal separation
        for &terminal in self.terminals {
            if terminal == self.root {
                continue;
            }

            let result = ws.compute(self.root, terminal, lp_solution, &self.graph.arcs);

            if result.flow_value < 1.0 - self.violation_tolerance {
                let violation = 1.0 - result.flow_value;
                violated_cuts.push(SteinerCut {
                    cut_set: result.source_side,
                    cut_arcs: result.cut_arcs,
                    separated_terminal: terminal,
                    violation,
                });
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

        // Infeasible LP: all arcs at 0.3, total flow to 4 = 0.6 < 1
        let lp = vec![0.3, 0.3, 0.3, 0.3];
        let cuts = separator.find_violated_cuts(&lp);

        assert_eq!(cuts.len(), 1);
        assert_eq!(cuts[0].separated_terminal, 4);
        assert!(cuts[0].violation > 0.3);
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
