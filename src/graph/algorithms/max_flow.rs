use std::collections::VecDeque;
use crate::graph::{NodeId, ArcId};
use crate::graph::directed::DirectedGraph;

/// Result of a max-flow computation, including the min-cut.
#[derive(Debug, Clone)]
pub struct MaxFlowResult {
    /// Maximum flow value from source to sink
    pub flow_value: f64,
    /// The min-cut set: nodes reachable from source in the residual graph.
    /// This is the set W in the Steiner cut constraint y(δ+(W)) ≥ 1.
    pub source_side: Vec<NodeId>,
    /// Arcs crossing the cut (from source_side to its complement)
    pub cut_arcs: Vec<ArcId>,
}

/// Compute maximum flow from source to sink using Edmonds-Karp (BFS-based Ford-Fulkerson).
/// Arc capacities are given by the `capacities` array (indexed by ArcId).
///
/// After computing max-flow, extract the min-cut by finding all nodes reachable
/// from the source in the residual graph (these form the source side of the cut).
///
/// For Steiner cut separation: source = root, sink = terminal, capacities = LP solution values.
pub fn max_flow_min_cut(
    graph: &DirectedGraph,
    source: NodeId,
    sink: NodeId,
    capacities: &[f64],
) -> MaxFlowResult {
    let num_arcs = graph.arcs.len();
    let num_nodes = graph.num_nodes as usize;

    // Build residual graph: for each arc, track residual capacity.
    // We also need reverse arcs for the residual graph.
    // Structure: residual[arc_id] = remaining capacity
    //            residual[arc_id + num_arcs] = reverse arc capacity (initially 0)
    let total_arcs = num_arcs * 2;
    let mut residual = vec![0.0f64; total_arcs];

    // Initialize forward arc capacities
    for i in 0..num_arcs {
        residual[i] = capacities[i];
    }

    // Build adjacency for the residual graph
    // For each node, store (neighbor, residual_arc_index, is_forward)
    let mut adj: Vec<Vec<(NodeId, usize)>> = vec![Vec::new(); num_nodes + 1];

    for (i, arc) in graph.arcs.iter().enumerate() {
        // Forward arc: tail -> head, index i
        adj[arc.tail as usize].push((arc.head, i));
        // Reverse arc: head -> tail, index i + num_arcs
        adj[arc.head as usize].push((arc.tail, i + num_arcs));
    }

    let mut total_flow = 0.0;

    // Edmonds-Karp: repeatedly find augmenting paths via BFS
    loop {
        // BFS to find augmenting path from source to sink
        let mut parent: Vec<Option<(NodeId, usize)>> = vec![None; num_nodes + 1];
        let mut visited = vec![false; num_nodes + 1];
        let mut queue = VecDeque::new();

        visited[source as usize] = true;
        queue.push_back(source);

        while let Some(node) = queue.pop_front() {
            if node == sink {
                break;
            }

            for &(neighbor, arc_idx) in &adj[node as usize] {
                if !visited[neighbor as usize] && residual[arc_idx] > 1e-10 {
                    visited[neighbor as usize] = true;
                    parent[neighbor as usize] = Some((node, arc_idx));
                    queue.push_back(neighbor);
                }
            }
        }

        // If sink not reached, no more augmenting paths exist
        if !visited[sink as usize] {
            break;
        }

        // Find bottleneck capacity along the path
        let mut path_flow = f64::INFINITY;
        let mut current = sink;
        while current != source {
            let (prev, arc_idx) = parent[current as usize].unwrap();
            path_flow = path_flow.min(residual[arc_idx]);
            current = prev;
        }

        // Update residual capacities along the path
        current = sink;
        while current != source {
            let (prev, arc_idx) = parent[current as usize].unwrap();
            residual[arc_idx] -= path_flow;
            // Update reverse arc
            let reverse_idx = if arc_idx < num_arcs {
                arc_idx + num_arcs
            } else {
                arc_idx - num_arcs
            };
            residual[reverse_idx] += path_flow;
            current = prev;
        }

        total_flow += path_flow;
    }

    // Extract min-cut: BFS from source in residual graph to find reachable nodes
    let mut reachable = vec![false; num_nodes + 1];
    let mut queue = VecDeque::new();
    reachable[source as usize] = true;
    queue.push_back(source);

    while let Some(node) = queue.pop_front() {
        for &(neighbor, arc_idx) in &adj[node as usize] {
            if !reachable[neighbor as usize] && residual[arc_idx] > 1e-10 {
                reachable[neighbor as usize] = true;
                queue.push_back(neighbor);
            }
        }
    }

    let source_side: Vec<NodeId> = (1..=num_nodes as NodeId)
        .filter(|&n| reachable[n as usize])
        .collect();

    // Find arcs crossing the cut (forward arcs from source_side to complement)
    let cut_arcs: Vec<ArcId> = graph.arcs.iter()
        .enumerate()
        .filter(|(_, arc)| {
            reachable[arc.tail as usize] && !reachable[arc.head as usize]
        })
        .map(|(i, _)| i as ArcId)
        .collect();

    MaxFlowResult {
        flow_value: total_flow,
        source_side,
        cut_arcs,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    #[test]
    fn test_simple_max_flow() {
        // Graph: 1 -> 2 (cap 3), 1 -> 3 (cap 2), 2 -> 4 (cap 2), 3 -> 4 (cap 3)
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 3.0);
        g.add_arc(1, 3, 2.0);
        g.add_arc(2, 4, 2.0);
        g.add_arc(3, 4, 3.0);

        let caps = vec![3.0, 2.0, 2.0, 3.0];
        let result = max_flow_min_cut(&g, 1, 4, &caps);

        // Max flow should be 4 (2 through node 2, 2 through node 3)
        assert!((result.flow_value - 4.0).abs() < 1e-6);
    }

    #[test]
    fn test_max_flow_fractional_capacities() {
        // Simulating LP relaxation values
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(1, 3, 1.0);
        g.add_arc(2, 4, 1.0);
        g.add_arc(3, 4, 1.0);

        // LP solution: each arc at 0.5 (total flow to node 4 = 1.0)
        let caps = vec![0.5, 0.5, 0.5, 0.5];
        let result = max_flow_min_cut(&g, 1, 4, &caps);
        assert!((result.flow_value - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_max_flow_violated_cut() {
        // Graph where flow < 1 indicates a violated Steiner cut
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 3, 1.0);

        // LP values: arc 1->2 at 0.3, arc 2->3 at 0.3
        // Max flow from 1 to 3 = 0.3 < 1 → violated cut!
        let caps = vec![0.3, 0.3];
        let result = max_flow_min_cut(&g, 1, 3, &caps);
        assert!(result.flow_value < 1.0 - 1e-6);

        // The cut should separate source (node 1) from sink (node 3)
        assert!(result.source_side.contains(&1));
        assert!(!result.source_side.contains(&3));
        assert!(!result.cut_arcs.is_empty());
    }

    #[test]
    fn test_min_cut_set() {
        // Bottleneck at middle
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);  // cap 5
        g.add_arc(1, 3, 1.0);  // cap 5
        g.add_arc(2, 4, 1.0);  // cap 1 (bottleneck)
        g.add_arc(3, 4, 1.0);  // cap 1 (bottleneck)

        let caps = vec![5.0, 5.0, 1.0, 1.0];
        let result = max_flow_min_cut(&g, 1, 4, &caps);
        assert!((result.flow_value - 2.0).abs() < 1e-6);

        // Min-cut should be {2->4, 3->4}
        assert!(result.source_side.contains(&1));
        assert!(result.source_side.contains(&2));
        assert!(result.source_side.contains(&3));
        assert!(!result.source_side.contains(&4));
    }
}
