use std::collections::VecDeque;
use crate::graph::{NodeId, ArcId, Cost};
use crate::graph::directed::DirectedGraph;

/// Result of the dual ascent procedure (Wong 1984).
///
/// Provides a valid lower bound and reduced costs for each arc.
/// The reduced cost of an arc a is: c_a - sum of dual multipliers
/// that cover arc a. Arcs with high reduced cost relative to the
/// gap (UB - LB) can be fixed to 0 (reduced-cost fixing).
#[derive(Debug, Clone)]
pub struct DualAscentResult {
    /// Valid lower bound on the optimal Steiner tree cost.
    pub lower_bound: Cost,
    /// Reduced cost for each arc (indexed by ArcId).
    pub reduced_costs: Vec<Cost>,
    /// Number of ascent iterations performed.
    pub iterations: u32,
}

/// Wong's dual ascent for the directed Steiner arborescence problem.
///
/// Given root r and terminals T, iteratively finds minimum r-t cuts
/// for each terminal t and increases dual variables along the cut arcs.
/// The sum of all dual increases is a valid lower bound.
///
/// The reduced cost of arc a is: c_a - (sum of dual values on a).
/// An arc with reduced_cost(a) > UB - LB can be fixed to 0.
pub fn dual_ascent(
    graph: &DirectedGraph,
    root: NodeId,
    terminals: &[NodeId],
) -> DualAscentResult {
    let num_arcs = graph.arcs.len();
    let num_nodes = graph.num_nodes as usize + 1;

    let mut reduced = vec![0.0f64; num_arcs];
    for (i, arc) in graph.arcs.iter().enumerate() {
        reduced[i] = arc.cost;
    }

    let mut lower_bound: Cost = 0.0;
    let mut iterations = 0u32;

    // Outer loop: cycle through terminals, increasing duals until no progress.
    // Process terminals in a greedy order: at each step, pick the terminal
    // whose min-cut from root (in residual costs) is largest. This is the
    // "maximum violation first" heuristic from SCIP-Jack.
    let non_root_terminals: Vec<NodeId> = terminals.iter()
        .copied()
        .filter(|&t| t != root)
        .collect();

    if non_root_terminals.is_empty() {
        return DualAscentResult { lower_bound: 0.0, reduced_costs: reduced, iterations: 0 };
    }

    let max_outer_passes = 5;
    for _pass in 0..max_outer_passes {
        let mut any_progress = false;

        for &terminal in &non_root_terminals {
            // Find nodes reachable from root using only ZERO-reduced-cost arcs.
            let mut reachable = vec![false; num_nodes];
            reachable[root as usize] = true;
            let mut queue = VecDeque::new();
            queue.push_back(root);

            while let Some(v) = queue.pop_front() {
                for &(head, arc_id) in graph.delta_plus(v) {
                    if !reachable[head as usize] && reduced[arc_id as usize] <= 1e-10 {
                        reachable[head as usize] = true;
                        queue.push_back(head);
                    }
                }
            }

            if reachable[terminal as usize] {
                continue;
            }

            // Terminal NOT reachable. Perform multiple ascent steps for this terminal
            // until it becomes reachable (saturate the cut).
            loop {
                let mut min_reduced = f64::INFINITY;
                for (i, arc) in graph.arcs.iter().enumerate() {
                    if reachable[arc.tail as usize] && !reachable[arc.head as usize] && reduced[i] > 1e-10 {
                        min_reduced = min_reduced.min(reduced[i]);
                    }
                }

                if min_reduced == f64::INFINITY || min_reduced <= 1e-10 {
                    break;
                }

                for (i, arc) in graph.arcs.iter().enumerate() {
                    if reachable[arc.tail as usize] && !reachable[arc.head as usize] {
                        reduced[i] -= min_reduced;
                        if reduced[i] < 0.0 { reduced[i] = 0.0; }
                    }
                }

                lower_bound += min_reduced;
                iterations += 1;
                any_progress = true;

                // Re-expand zero-cost reachable set
                let mut expanded = true;
                while expanded {
                    expanded = false;
                    for (i, arc) in graph.arcs.iter().enumerate() {
                        if reachable[arc.tail as usize] && !reachable[arc.head as usize]
                            && reduced[i] <= 1e-10
                        {
                            reachable[arc.head as usize] = true;
                            queue.push_back(arc.head);
                            expanded = true;
                        }
                    }
                    // Drain queue for BFS expansion
                    while let Some(v) = queue.pop_front() {
                        for &(head, arc_id) in graph.delta_plus(v) {
                            if !reachable[head as usize] && reduced[arc_id as usize] <= 1e-10 {
                                reachable[head as usize] = true;
                                queue.push_back(head);
                            }
                        }
                    }
                }

                if reachable[terminal as usize] {
                    break;
                }
            }
        }

        if !any_progress {
            break;
        }
    }

    DualAscentResult { lower_bound, reduced_costs: reduced, iterations }
}

/// Compute arcs that can be fixed to 0 via reduced-cost fixing.
/// An arc a can be fixed if: lower_bound + reduced_cost(a) > upper_bound.
/// Returns the list of arc IDs that can be fixed.
pub fn reduced_cost_fixable_arcs(
    da_result: &DualAscentResult,
    upper_bound: Cost,
) -> Vec<ArcId> {
    let gap = upper_bound - da_result.lower_bound;
    if gap <= 1e-9 {
        return Vec::new();
    }

    da_result.reduced_costs.iter()
        .enumerate()
        .filter(|&(_, &rc)| rc > gap + 1e-9)
        .map(|(i, _)| i as ArcId)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    #[test]
    fn test_dual_ascent_simple() {
        // 1(root) --3-- 2(terminal)
        let mut g = DirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 3.0);
        g.add_arc(2, 1, 3.0);

        let result = dual_ascent(&g, 1, &[2]);
        assert!(result.lower_bound >= 3.0 - 1e-6,
            "Lower bound should be at least 3, got {}", result.lower_bound);
    }

    #[test]
    fn test_dual_ascent_multi_terminal() {
        // 1(root) --1-- 2(S) --2-- 3(T)
        //                |
        //               --5-- 4(T)
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 2.0);
        g.add_arc(3, 2, 2.0);
        g.add_arc(2, 4, 5.0);
        g.add_arc(4, 2, 5.0);

        let result = dual_ascent(&g, 1, &[3, 4]);
        // Optimal: 1->2(1) + 2->3(2) + 2->4(5) = 8
        // Dual ascent LB should be <= 8
        assert!(result.lower_bound > 0.0, "Should produce a positive lower bound");
        assert!(result.lower_bound <= 8.0 + 1e-6,
            "Lower bound {} should not exceed optimal 8", result.lower_bound);
    }

    #[test]
    fn test_dual_ascent_lb_valid() {
        // Known optimal: 1->2(1) + 2->3(2) + 2->4(5) = 8
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 2.0);
        g.add_arc(3, 2, 2.0);
        g.add_arc(2, 4, 5.0);
        g.add_arc(4, 2, 5.0);
        g.add_arc(1, 3, 10.0);
        g.add_arc(3, 1, 10.0);
        g.add_arc(1, 4, 8.0);
        g.add_arc(4, 1, 8.0);

        let result = dual_ascent(&g, 1, &[3, 4]);
        assert!(result.lower_bound <= 8.0 + 1e-6);
        assert!(result.reduced_costs.len() == 10);
        assert!(result.reduced_costs.iter().all(|&r| r >= -1e-6),
            "Reduced costs must be non-negative");
    }

    #[test]
    fn test_reduced_cost_fixing() {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 3, 1.0);
        g.add_arc(1, 3, 100.0); // Very expensive direct arc
        g.add_arc(2, 1, 1.0);
        g.add_arc(3, 2, 1.0);
        g.add_arc(3, 1, 100.0);

        let result = dual_ascent(&g, 1, &[3]);
        let fixable = reduced_cost_fixable_arcs(&result, 2.0);
        // Arc 1->3 (cost 100) should be fixable since reduced_cost(100) >> gap(0)
        assert!(!fixable.is_empty() || result.lower_bound >= 2.0 - 1e-6,
            "Should fix expensive arcs or prove optimal");
    }
}
