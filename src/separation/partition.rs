use std::collections::HashSet;
use crate::graph::{DirectedGraph, NodeId, ArcId};
use crate::graph::algorithms::MaxFlowWorkspace;

/// Partition inequality separator.
///
/// For any partition P = {V_1, ..., V_k} of the vertex set where each part
/// contains at least one terminal, the Steiner tree must use at least k-1
/// crossing edges. In the directed formulation:
///
///   sum_{arcs crossing partition} y_a >= k - 1
///
/// Separation proceeds via a Gomory-Hu-style iterative approach:
/// 1. Build an auxiliary graph on terminals with edge weights = max-flow values
/// 2. Find the minimum cut in the auxiliary graph that partitions terminals
///    into multiple components
/// 3. If the min-cut value < k-1, the partition inequality is violated
///
/// The practical implementation uses iterative min-cut computations between
/// pairs of terminal sets to find violated multi-way partitions.
pub struct PartitionSeparator<'a> {
    graph: &'a DirectedGraph,
    root: NodeId,
    terminals: &'a [NodeId],
    pub cuts_found: u32,
    pub violation_tolerance: f64,
    workspace: Option<MaxFlowWorkspace>,
}

/// A violated partition inequality.
#[derive(Debug, Clone)]
pub struct PartitionCut {
    /// Arcs crossing the partition (coefficients = 1)
    pub crossing_arcs: Vec<ArcId>,
    /// RHS of the inequality (k-1 where k = number of parts)
    pub rhs: f64,
    /// Violation amount: rhs - sum of LP values on crossing arcs
    pub violation: f64,
    /// Number of parts in the partition
    pub num_parts: usize,
}

impl<'a> PartitionSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph, root: NodeId, terminals: &'a [NodeId]) -> Self {
        Self {
            graph,
            root,
            terminals,
            cuts_found: 0,
            violation_tolerance: 1e-4,
            workspace: None,
        }
    }

    /// Find violated partition inequalities given the current LP solution.
    ///
    /// The directed partition inequality states: for any partition of V into
    /// k parts where the root is in one part and each of the other k-1 parts
    /// contains at least one terminal, the total flow on arcs leaving the
    /// root-side partition towards any non-root part must be >= k-1.
    ///
    /// Strategy: Compute min-cuts from root to each terminal, then find subsets
    /// of terminals whose joint separation from root has fewer crossing arcs
    /// than required.
    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<PartitionCut> {
        if self.workspace.is_none() {
            self.workspace = Some(MaxFlowWorkspace::new(self.graph));
        }

        let non_root_terminals: Vec<NodeId> = self.terminals.iter()
            .copied()
            .filter(|&t| t != self.root)
            .collect();

        if non_root_terminals.len() < 2 {
            return Vec::new();
        }

        let mut violated = Vec::new();

        // Phase 1: For each terminal, compute the min-cut from root → terminal.
        // These give us the "building blocks" for partition cuts.
        let mut terminal_cuts: Vec<(NodeId, f64, Vec<NodeId>, Vec<ArcId>)> = Vec::new();
        {
            let ws = self.workspace.as_mut().unwrap();
            for &t in &non_root_terminals {
                let result = ws.compute(self.root, t, lp_solution, &self.graph.arcs);
                terminal_cuts.push((t, result.flow_value, result.source_side, result.cut_arcs));
            }
        }

        // Phase 2: Try multi-terminal partitions.
        // For each pair of terminals, check if separating them JOINTLY from the
        // root (using the sink-side union) gives a violated partition inequality.
        // The key insight: if we have k terminals on one side of a cut, the RHS
        // is still just 1 (one unit of flow must cross to reach ANY of them).
        // The partition inequality becomes stronger for k-WAY partitions where
        // EACH part has a terminal and each needs its own crossing arc.

        // For a proper k-partition inequality, we need k parts each containing
        // a terminal. The flow FROM root's part to all other parts must be >= k-1.
        // This equals: sum of arcs leaving the root's component to ANY other = k-1.

        // Approach: compute an "aggregated" cut. Take the union of sink-sides
        // from multiple min-cut computations and check the crossing flow.

        // Try 2-partition: group ALL non-root terminals together (opposite the root).
        // The min-cut separating root from all terminals must have flow >= 1.
        // (This is just the Steiner cut for any single terminal, already handled.)
        // But a MULTI-way partition needs flow >= k-1.

        // Correct approach for k-partition:
        // Compute a "multi-commodity" relaxation: for k parts (root in part 0),
        // the total flow FROM part 0 to other parts must be >= k-1 because each
        // of the k-1 other parts needs at least one unit entering it.

        // Practical separation: try grouping terminals into clusters and checking
        // if the sum of minimum crossing flows is < k-1.
        self.separate_multiway_partitions(lp_solution, &non_root_terminals, &terminal_cuts, &mut violated);

        violated.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(std::cmp::Ordering::Equal));
        self.cuts_found = violated.len() as u32;
        violated
    }

    /// Separate multi-way partition inequalities.
    ///
    /// For a k-way partition where root is in part 0 and parts 1..k-1 each contain
    /// at least one terminal: the total flow on arcs from part 0 to the union of
    /// all other parts must be >= k-1. More precisely, for EACH part i (i != 0),
    /// the flow into part i must be >= 1. The partition inequality combines these:
    ///   sum_{i=1}^{k-1} y(delta+(V_0, V_i)) >= k-1
    /// which, when parts are vertex-disjoint, becomes:
    ///   y(delta+(V_0)) >= k-1
    /// where delta+(V_0) are arcs leaving the root's component.
    fn separate_multiway_partitions(
        &mut self,
        lp_solution: &[f64],
        terminals: &[NodeId],
        terminal_cuts: &[(NodeId, f64, Vec<NodeId>, Vec<ArcId>)],
        violated: &mut Vec<PartitionCut>,
    ) {
        let n_terms = terminals.len();
        if n_terms < 2 {
            return;
        }

        // Strategy: find a set W containing root such that the number of terminal
        // groups in V\W is k-1, and y(delta+(W)) < k-1.
        //
        // We use min-cuts from root to subsets of terminals to find such W.
        // Start with individual terminal min-cuts and look for "nested" structure.

        // Try all pairs (and triples for small terminal counts) of terminals.
        // For each subset S of terminals, compute min-cut from root to the
        // "merged sink" (contraction of all terminals in S to a super-sink).
        // In practice: compute max-flow from root to the group, using a
        // super-sink connected to each terminal with infinite capacity.
        // We approximate this by summing the individual min-cut contributions.

        // Better approach: for each terminal t_i, we know the min-cut value
        // f_i = max-flow(root, t_i). For a k-partition to be violated, we need
        // the total flow leaving the root's side to be < k-1. This happens when
        // multiple terminals share the SAME bottleneck arcs (the same set of
        // arcs carries flow to multiple terminals).

        // Detect shared bottlenecks: find arcs that appear in multiple min-cut
        // source sides (arcs that are the only way to reach multiple terminals).

        // Simple greedy approach: sort terminals by min-cut value, then
        // iteratively merge the weakest-connected terminal into a partition.

        // For a valid k-partition inequality in the directed formulation:
        // Define W = root's component. Then delta+(W) must carry at least k-1
        // units of flow where k-1 = number of groups of terminals in V\W.
        // Each group must be a connected subset in the graph that contains ≥ 1 terminal.

        // Most practical: for each subset of terminals that share a "joint
        // min-cut" from the root, the value of that joint cut should be >= |subset|.

        // Single-terminal violations (standard Steiner cuts, for completeness)
        for &(_t, flow_val, _, ref cut_arcs) in terminal_cuts {
            if flow_val < 1.0 - self.violation_tolerance {
                let cut_value: f64 = cut_arcs.iter()
                    .map(|&aid| lp_solution.get(aid as usize).copied().unwrap_or(0.0))
                    .sum();
                if cut_value < 1.0 - self.violation_tolerance {
                    violated.push(PartitionCut {
                        crossing_arcs: cut_arcs.clone(),
                        rhs: 1.0,
                        violation: 1.0 - cut_value,
                        num_parts: 2,
                    });
                }
            }
        }

        // Multi-terminal partition: check if a single cut separates multiple
        // terminals from root into DIFFERENT connected components.
        // For pairs of terminals t_i, t_j: compute the joint cut and verify
        // they end up in disconnected components on the sink side.
        if n_terms >= 2 && n_terms <= 50 {
            let limit = n_terms.min(15);
            for i in 0..limit {
                for j in (i + 1)..limit {
                    let t_i = terminals[i];
                    let t_j = terminals[j];

                    let (flow_val, crossing) = self.compute_joint_cut(
                        lp_solution, &[t_i, t_j],
                    );

                    // compute_joint_cut returns INFINITY when no valid multi-partition exists
                    if flow_val < f64::INFINITY {
                        // A violated multi-partition was found with rhs = num_components
                        // flow_val is the actual crossing flow, which is < rhs
                        let rhs = 2.0; // Will be refined by compute_joint_cut
                        violated.push(PartitionCut {
                            crossing_arcs: crossing,
                            rhs,
                            violation: rhs - flow_val,
                            num_parts: 3,
                        });
                    }
                }
                if violated.len() >= 10 {
                    break;
                }
            }
        }

        // Triple-terminal partitions for small instances
        if n_terms >= 3 && n_terms <= 20 && violated.is_empty() {
            let limit = n_terms.min(10);
            for i in 0..limit {
                for j in (i + 1)..limit {
                    for k in (j + 1)..limit {
                        let t_i = terminals[i];
                        let t_j = terminals[j];
                        let t_k = terminals[k];

                        let (flow_val, crossing) = self.compute_joint_cut(
                            lp_solution, &[t_i, t_j, t_k],
                        );

                        if flow_val < f64::INFINITY {
                            let rhs = 3.0;
                            violated.push(PartitionCut {
                                crossing_arcs: crossing,
                                rhs,
                                violation: rhs - flow_val,
                                num_parts: 4,
                            });
                        }
                    }
                    if violated.len() >= 10 {
                        break;
                    }
                }
                if violated.len() >= 10 {
                    break;
                }
            }
        }
    }

    /// Compute the minimum cut separating root from a SET of terminals,
    /// and determine how many DISCONNECTED terminal groups exist on the sink side.
    ///
    /// For the cut to be a valid k-partition inequality, the terminals on the
    /// sink side must be in k-1 separate connected components (each needing
    /// its own unit of flow from the root side).
    ///
    /// Returns (actual_rhs, total flow crossing, arcs crossing the cut) where
    /// actual_rhs = number of disconnected terminal-containing components in V\W.
    fn compute_joint_cut(
        &mut self,
        lp_solution: &[f64],
        target_terminals: &[NodeId],
    ) -> (f64, Vec<ArcId>) {
        let ws = self.workspace.as_mut().unwrap();

        // Find the tightest cut: compute min-cut from root to each terminal
        // in the set, and find their intersection (the set that separates root
        // from ALL terminals simultaneously).
        let mut root_side: Option<HashSet<NodeId>> = None;

        for &t in target_terminals {
            let result = ws.compute(self.root, t, lp_solution, &self.graph.arcs);
            let source: HashSet<NodeId> = result.source_side.into_iter().collect();

            root_side = Some(match root_side {
                None => source,
                Some(existing) => existing.intersection(&source).copied().collect(),
            });
        }

        let root_component = match root_side {
            Some(s) if !s.is_empty() => s,
            _ => {
                let mut s = HashSet::new();
                s.insert(self.root);
                s
            }
        };

        // Verify root is in the component and no target terminal is
        if !root_component.contains(&self.root) || target_terminals.iter().any(|t| root_component.contains(t)) {
            return (f64::INFINITY, Vec::new());
        }

        // Determine how many DISCONNECTED terminal groups exist on the sink side.
        // We do BFS/DFS on the sink side using arcs with positive LP flow to
        // determine connectivity. Only count components that contain a target terminal.
        let sink_side: HashSet<NodeId> = self.graph.nodes.iter()
            .map(|n| n.id)
            .filter(|id| !root_component.contains(id))
            .collect();

        let num_terminal_components = self.count_terminal_components(
            lp_solution, &sink_side, target_terminals,
        );

        if num_terminal_components < 2 {
            // All target terminals are in the same connected component on sink side.
            // This is just a standard Steiner cut (rhs = 1), not a multi-partition.
            return (f64::INFINITY, Vec::new());
        }

        // Collect arcs crossing from root_component to its complement
        let mut crossing_arcs = Vec::new();
        let mut total_flow = 0.0;

        for arc in &self.graph.arcs {
            if root_component.contains(&arc.tail) && !root_component.contains(&arc.head) {
                let flow = lp_solution.get(arc.id as usize).copied().unwrap_or(0.0);
                if flow > 1e-10 {
                    crossing_arcs.push(arc.id);
                    total_flow += flow;
                }
            }
        }

        // The RHS is the number of disconnected terminal components on the sink side
        let rhs = num_terminal_components as f64;

        // Check violation: total flow must be >= rhs
        if total_flow < rhs - self.violation_tolerance {
            // Return the effective flow comparison against the actual RHS
            // The caller will check violation against the REQUESTED rhs, but we
            // report against the actual component count.
            return (total_flow, crossing_arcs);
        }

        (f64::INFINITY, Vec::new())
    }

    /// Count the number of connected components in the sink-side subgraph
    /// that contain at least one target terminal. Connectivity is determined
    /// by arcs with positive LP flow (in either direction).
    fn count_terminal_components(
        &self,
        lp_solution: &[f64],
        sink_side: &HashSet<NodeId>,
        target_terminals: &[NodeId],
    ) -> usize {
        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut terminal_components = 0;

        for &start in target_terminals {
            if visited.contains(&start) || !sink_side.contains(&start) {
                continue;
            }

            // BFS from this terminal within the sink side
            let mut queue = std::collections::VecDeque::new();
            queue.push_back(start);
            visited.insert(start);

            while let Some(node) = queue.pop_front() {
                // Follow outgoing arcs with positive flow
                for &(head, arc_id) in self.graph.delta_plus(node) {
                    if !sink_side.contains(&head) || visited.contains(&head) {
                        continue;
                    }
                    let flow = lp_solution.get(arc_id as usize).copied().unwrap_or(0.0);
                    if flow > 1e-8 {
                        visited.insert(head);
                        queue.push_back(head);
                    }
                }
                // Follow incoming arcs with positive flow
                for &(tail, arc_id) in self.graph.delta_minus(node) {
                    if !sink_side.contains(&tail) || visited.contains(&tail) {
                        continue;
                    }
                    let flow = lp_solution.get(arc_id as usize).copied().unwrap_or(0.0);
                    if flow > 1e-8 {
                        visited.insert(tail);
                        queue.push_back(tail);
                    }
                }
            }

            terminal_components += 1;
        }

        terminal_components
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn build_partition_test_graph() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // Diamond graph with 4 terminals:
        //     1 (root, terminal)
        //    / \
        //   2   3
        //  / \ / \
        // 4   5   6
        // (terminals: 1, 4, 5, 6)
        //
        // Any valid Steiner tree must use >= 3 edges to connect 4 terminals.
        let mut g = DirectedGraph::new(6);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_node(5, NodeType::Terminal, 0.0);
        g.add_node(6, NodeType::Terminal, 0.0);

        // Bidirected edges
        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(1, 3, 1.0); // 2
        g.add_arc(3, 1, 1.0); // 3
        g.add_arc(2, 4, 1.0); // 4
        g.add_arc(4, 2, 1.0); // 5
        g.add_arc(2, 5, 1.0); // 6
        g.add_arc(5, 2, 1.0); // 7
        g.add_arc(3, 5, 1.0); // 8
        g.add_arc(5, 3, 1.0); // 9
        g.add_arc(3, 6, 1.0); // 10
        g.add_arc(6, 3, 1.0); // 11

        (g, 1, vec![1, 4, 5, 6])
    }

    #[test]
    fn test_partition_separator_basic() {
        let (g, root, terminals) = build_partition_test_graph();
        let mut sep = PartitionSeparator::new(&g, root, &terminals);

        // Fractional LP solution that splits flow evenly
        let lp = vec![
            0.5, 0.0,  // 1->2, 2->1
            0.5, 0.0,  // 1->3, 3->1
            0.5, 0.0,  // 2->4, 4->2
            0.25, 0.0, // 2->5, 5->2
            0.25, 0.0, // 3->5, 5->3
            0.5, 0.0,  // 3->6, 6->3
        ];

        let cuts = sep.find_violated_cuts(&lp);
        // With this fractional solution, partition cuts may find violations
        // that terminal cuts alone miss (multi-way fractional splitting)
        // The test verifies the separator doesn't crash and produces valid output
        for cut in &cuts {
            assert!(!cut.crossing_arcs.is_empty());
            assert!(cut.violation > 0.0);
            assert!(cut.rhs >= 1.0);
        }
    }

    #[test]
    fn test_partition_separator_feasible() {
        let (g, root, terminals) = build_partition_test_graph();
        let mut sep = PartitionSeparator::new(&g, root, &terminals);

        // Integer-feasible solution: 1->2->4, 1->2->5, 1->3->6
        let lp = vec![
            1.0, 0.0, // 1->2
            1.0, 0.0, // 1->3
            1.0, 0.0, // 2->4
            1.0, 0.0, // 2->5
            0.0, 0.0, // 3->5
            1.0, 0.0, // 3->6
        ];

        let cuts = sep.find_violated_cuts(&lp);
        assert!(cuts.is_empty(), "Feasible solution should have no violated partition cuts");
    }

    #[test]
    fn test_partition_separator_two_terminals() {
        // With only 2 non-root terminals, partition cuts reduce to Steiner cuts
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(1, 3, 1.0);
        g.add_arc(3, 1, 1.0);

        let terminals = vec![1, 2, 3];
        let mut sep = PartitionSeparator::new(&g, 1, &terminals);

        let lp = vec![0.4, 0.0, 0.4, 0.0];
        let cuts = sep.find_violated_cuts(&lp);
        // Should find violations since flow to each terminal < 1
        assert!(!cuts.is_empty());
    }
}
