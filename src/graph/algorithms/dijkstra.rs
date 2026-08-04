use std::cmp::Ordering;
use std::collections::BinaryHeap;
use crate::graph::{cmp_cost, NodeId, ArcId, Cost};
use crate::graph::directed::DirectedGraph;

const INF: Cost = f64::INFINITY;

#[derive(Debug, Clone)]
pub struct ShortestPathResult {
    pub distances: Vec<Cost>,
    pub predecessors: Vec<Option<(NodeId, ArcId)>>,
}

impl ShortestPathResult {
    /// Reconstruct the path from source to target as a sequence of arc IDs.
    pub fn path_to(&self, target: NodeId) -> Option<Vec<ArcId>> {
        if self.distances[target as usize] >= INF {
            return None;
        }

        let mut arcs = Vec::new();
        let mut current = target;

        while let Some((pred_node, arc_id)) = self.predecessors[current as usize] {
            arcs.push(arc_id);
            current = pred_node;
        }

        arcs.reverse();
        Some(arcs)
    }

    /// Get all nodes on the path from source to target.
    pub fn nodes_on_path_to(&self, target: NodeId) -> Option<Vec<NodeId>> {
        if self.distances[target as usize] >= INF {
            return None;
        }

        let mut nodes = vec![target];
        let mut current = target;

        while let Some((pred_node, _)) = self.predecessors[current as usize] {
            nodes.push(pred_node);
            current = pred_node;
        }

        nodes.reverse();
        Some(nodes)
    }

    pub fn distance_to(&self, target: NodeId) -> Cost {
        self.distances[target as usize]
    }
}

#[derive(Clone, Copy, PartialEq)]
struct State {
    cost: Cost,
    node: NodeId,
}

impl Eq for State {}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_cost(other.cost, self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compute shortest paths from a source node to all other nodes using Dijkstra's algorithm.
/// Operates on the directed graph with given arc costs (allows custom cost overrides).
pub fn shortest_paths_from(
    graph: &DirectedGraph,
    source: NodeId,
    costs: &[Cost],
) -> ShortestPathResult {
    let n = graph.num_nodes as usize;
    let mut distances = vec![INF; n + 1]; // 1-indexed
    let mut predecessors: Vec<Option<(NodeId, ArcId)>> = vec![None; n + 1];
    let mut heap = BinaryHeap::new();

    distances[source as usize] = 0.0;
    heap.push(State { cost: 0.0, node: source });

    while let Some(State { cost, node }) = heap.pop() {
        if cost > distances[node as usize] {
            continue;
        }

        for &(head, arc_id) in graph.delta_plus(node) {
            let arc_cost = costs[arc_id as usize];
            let next_cost = cost + arc_cost;

            if next_cost < distances[head as usize] {
                distances[head as usize] = next_cost;
                predecessors[head as usize] = Some((node, arc_id));
                heap.push(State { cost: next_cost, node: head });
            }
        }
    }

    ShortestPathResult { distances, predecessors }
}

/// Compute shortest path between two specific nodes.
/// Returns (distance, arc_path) or None if unreachable.
pub fn shortest_path(
    graph: &DirectedGraph,
    source: NodeId,
    target: NodeId,
    costs: &[Cost],
) -> Option<(Cost, Vec<ArcId>)> {
    let result = shortest_paths_from(graph, source, costs);
    let dist = result.distance_to(target);
    if dist >= INF {
        return None;
    }
    result.path_to(target).map(|path| (dist, path))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn build_test_graph() -> (DirectedGraph, Vec<Cost>) {
        // Simple diamond graph:
        //   1 --2--> 2
        //   1 --5--> 3
        //   2 --1--> 4
        //   3 --1--> 4
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 2.0); // arc 0
        g.add_arc(1, 3, 5.0); // arc 1
        g.add_arc(2, 4, 1.0); // arc 2
        g.add_arc(3, 4, 1.0); // arc 3

        let costs = vec![2.0, 5.0, 1.0, 1.0];
        (g, costs)
    }

    #[test]
    fn test_shortest_path_simple() {
        let (g, costs) = build_test_graph();
        let (dist, path) = shortest_path(&g, 1, 4, &costs).unwrap();
        assert!((dist - 3.0).abs() < 1e-9);
        assert_eq!(path, vec![0, 2]); // arc 0 (1->2), arc 2 (2->4)
    }

    #[test]
    fn test_shortest_paths_from() {
        let (g, costs) = build_test_graph();
        let result = shortest_paths_from(&g, 1, &costs);
        assert!((result.distance_to(1) - 0.0).abs() < 1e-9);
        assert!((result.distance_to(2) - 2.0).abs() < 1e-9);
        assert!((result.distance_to(3) - 5.0).abs() < 1e-9);
        assert!((result.distance_to(4) - 3.0).abs() < 1e-9);
    }

    #[test]
    fn test_unreachable() {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0);
        // Node 3 is unreachable from 1

        let costs = vec![1.0];
        assert!(shortest_path(&g, 1, 3, &costs).is_none());
    }
}
