use std::collections::{BinaryHeap, HashSet};
use std::cmp::Ordering;
use crate::graph::Cost;
use super::ReducibleGraph;

/// Bottleneck-based reduction techniques:
///
/// **Bottleneck Steiner Distance (BSD) test**:
/// An edge {u,v} can be removed if c({u,v}) > BSD(u, v), where BSD(u,v)
/// is the minimum bottleneck of any path from u to v that passes through
/// at least one terminal.
///
/// The bottleneck of a path is the maximum edge cost along that path.
/// BSD(u,v) = min over all paths P from u to v through a terminal {max_{e ∈ P} c(e)}.
///
/// Returns number of edges removed.
pub fn bottleneck_reductions(graph: &mut ReducibleGraph) -> u32 {
    let mut removed = 0u32;

    let terminal_list: Vec<u32> = graph.terminals.iter().copied()
        .filter(|&t| graph.is_node_valid(t))
        .collect();

    if terminal_list.is_empty() {
        return 0;
    }

    // Compute bottleneck distances from each terminal using a modified Dijkstra
    // where distance = max edge weight on path (bottleneck distance).
    let terminal_bottlenecks: Vec<Vec<Cost>> = terminal_list.iter()
        .map(|&t| bottleneck_distances_from(graph, t))
        .collect();

    // For each edge, compute BSD and check if edge cost exceeds it
    let edges_to_check: Vec<(u32, u32, u32, f64)> = graph.edges.iter()
        .filter(|e| graph.is_edge_valid(e.id))
        .map(|e| (e.id, e.src, e.dst, e.cost))
        .collect();

    for (eid, src, dst, cost) in edges_to_check {
        if !graph.is_edge_valid(eid) {
            continue;
        }

        // BSD(src, dst) = min over all terminals t of max(bd(src, t), bd(dst, t))
        // where bd(x, t) is the bottleneck distance from x to t
        let mut bsd = f64::INFINITY;
        for (idx, _) in terminal_list.iter().enumerate() {
            let bd_src = terminal_bottlenecks[idx][src as usize];
            let bd_dst = terminal_bottlenecks[idx][dst as usize];
            let through_t = bd_src.max(bd_dst);
            bsd = bsd.min(through_t);
        }

        // If edge cost strictly exceeds BSD, it's not needed in any optimal solution
        if cost > bsd + 1e-9 {
            graph.remove_edge(eid);
            removed += 1;
        }
    }

    removed
}

/// Compute bottleneck distances from a source node to all reachable nodes.
/// The bottleneck distance is the minimum over all paths of the maximum edge weight on that path.
/// Uses a modified Dijkstra where we minimize the max-edge-weight (bottleneck).
fn bottleneck_distances_from(graph: &ReducibleGraph, source: u32) -> Vec<Cost> {
    let n = graph.nodes.len() + 1;
    let mut dist = vec![f64::INFINITY; n];
    let mut visited: HashSet<u32> = HashSet::new();
    let mut heap = BinaryHeap::new();

    dist[source as usize] = 0.0;
    heap.push(BnEntry { bottleneck: 0.0, node: source });

    while let Some(BnEntry { bottleneck, node }) = heap.pop() {
        if visited.contains(&node) {
            continue;
        }
        visited.insert(node);
        dist[node as usize] = bottleneck;

        for (neighbor, eid) in graph.valid_neighbors(node) {
            if visited.contains(&neighbor) {
                continue;
            }
            let edge_cost = graph.edges[eid as usize].cost;
            let new_bn = bottleneck.max(edge_cost);
            if new_bn < dist[neighbor as usize] {
                dist[neighbor as usize] = new_bn;
                heap.push(BnEntry { bottleneck: new_bn, node: neighbor });
            }
        }
    }

    dist
}

#[derive(Clone, PartialEq)]
struct BnEntry {
    bottleneck: Cost,
    node: u32,
}

impl Eq for BnEntry {}

impl Ord for BnEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // Min-heap on bottleneck distance
        other.bottleneck.partial_cmp(&self.bottleneck)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for BnEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{UndirectedGraph, NodeType, SteinerInstance};

    #[test]
    fn test_bottleneck_removes_expensive_edge() {
        // 1(T) --1-- 2(T) --1-- 3(T)
        //              |
        //      4(S) --100-- 5(S)
        //        \           /
        //         1         1
        //          \       /
        //           2(T)  2(T) [via edges to 2]
        //
        // Actually simpler test:
        // 1(T) --1-- 2(T) --1-- 3(S) --100-- 4(S)
        //                        |
        //                        1
        //                        |
        //                       5(T)
        // Edge 3-4 cost 100: BSD(3,4) via terminal 5: max(1, ?) = need path 4 to terminal
        // Let's make a clearer test:
        //
        // 1(T) --2-- 2(S) --2-- 3(T)
        //             |
        //            50
        //             |
        //            4(S)
        // Edge 2-4 cost 50: BSD(2,4) = min over terminals of max(bd(2,t), bd(4,t))
        // bd(2,1) = 2, bd(4,1) = max(50, 2) = 50 => through T1: max(2, 50) = 50
        // bd(2,3) = 2, bd(4,3) = max(50, 2) = 50 => through T3: max(2, 50) = 50
        // BSD = 50. cost = 50. Not strictly greater, so not removed.
        //
        // Change cost of 2-4 to 100:
        // bd(4,1) = max(100, 2) = 100, bd(4,3) = max(100, 2) = 100
        // BSD = min(max(2,100), max(2,100)) = 100. cost = 100. Still not strictly greater.
        //
        // Better test: triangle with one edge being bottleneck
        // 1(T) --1-- 2(T) --1-- 3(T) and edge 1-3 cost 5
        // BSD(1,3) via terminal 2: max(bd(1,2), bd(3,2)) = max(1, 1) = 1
        // So edge 1-3 cost 5 > BSD 1 => removed!
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(1, 3, 5.0); // 2: should be removed, BSD = 1 < 5

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 3,
            num_edges: 3,
            num_terminals: 3,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2, 3],
            root: Some(1),
        };

        let mut rg = ReducibleGraph::from_instance(&instance, &g);
        let removed = bottleneck_reductions(&mut rg);

        assert!(removed >= 1, "Should remove edge with cost > BSD");
        assert!(!rg.is_edge_valid(2), "Edge 1-3 (cost 5, BSD=1) should be removed");
    }

    #[test]
    fn test_bottleneck_keeps_necessary_edge() {
        // 1(T) --3-- 2(T): single connection, BSD is infinity, cannot remove
        let mut g = UndirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 3.0);

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 2,
            num_edges: 1,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2],
            root: Some(1),
        };

        let mut rg = ReducibleGraph::from_instance(&instance, &g);
        let removed = bottleneck_reductions(&mut rg);

        assert_eq!(removed, 0, "Should not remove the only connecting edge");
    }
}
