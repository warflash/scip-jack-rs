use std::collections::BinaryHeap;
use std::cmp::Ordering;
use crate::graph::{cmp_cost, UndirectedGraph, NodeId, Cost};

/// Dreyfus-Wagner DP for the Steiner tree problem in undirected graphs.
///
/// Computes the exact minimum Steiner tree cost in O(3^k * n + 2^k * n^2 + nm log n)
/// where k = |terminals|, n = |nodes|, m = |edges|.
///
/// Based on: Dreyfus & Wagner (1971), "The Steiner problem in graphs".
///
/// Suitable for instances with few terminals (k ≤ ~20). For k > 20, the
/// exponential memory 2^k * n becomes prohibitive.
pub struct DreyfusWagnerResult {
    pub optimal_cost: Cost,
    pub tree_edges: Vec<(NodeId, NodeId, Cost)>,
}

/// Solve the Steiner tree problem exactly using Dreyfus-Wagner DP.
///
/// `graph`: undirected graph
/// `terminals`: list of terminal nodes (must be non-empty)
///
/// Returns `None` if the problem is infeasible (disconnected terminals).
pub fn dreyfus_wagner(graph: &UndirectedGraph, terminals: &[NodeId]) -> Option<DreyfusWagnerResult> {
    if terminals.is_empty() {
        return Some(DreyfusWagnerResult { optimal_cost: 0.0, tree_edges: vec![] });
    }
    if terminals.len() == 1 {
        return Some(DreyfusWagnerResult { optimal_cost: 0.0, tree_edges: vec![] });
    }

    let k = terminals.len();
    if k > 24 {
        return None;
    }

    let n = graph.num_nodes as usize + 1;
    let full_mask = (1u32 << k) - 1;

    // Precompute all-pairs shortest paths from every node (Dijkstra from each)
    let dist = all_pairs_dijkstra(graph, n);

    // dp[S][v] = cost of minimum Steiner tree spanning terminal subset S ∪ {v},
    // where S is a bitmask over terminals[] and v is a node.
    let num_subsets = (full_mask + 1) as usize;
    let mut dp = vec![vec![f64::INFINITY; n]; num_subsets];
    // parent tracking for reconstruction
    // parent[S][v] = how we achieved dp[S][v]:
    //   (split_mask, split_node) if from Steiner recurrence
    //   (0, prev_node) if from shortest-path extension
    let mut parent: Vec<Vec<(u32, u32)>> = vec![vec![(0, 0); n]; num_subsets];

    // Base case: singleton terminal sets
    for (i, &t) in terminals.iter().enumerate() {
        let mask = 1u32 << i;
        for v in 1..n {
            dp[mask as usize][v] = dist[t as usize][v];
            parent[mask as usize][v] = (0, t);
        }
        dp[mask as usize][t as usize] = 0.0;
        parent[mask as usize][t as usize] = (0, t);
    }

    // DP over subsets in increasing size order
    for s in 1..=full_mask {
        let s_idx = s as usize;
        if s.count_ones() < 2 {
            continue;
        }

        // Steiner recurrence: dp[S][v] = min over proper subsets D ⊂ S, D ≠ ∅
        //   dp[D][v] + dp[S\D][v]
        let mut sub = (s - 1) & s;
        while sub > 0 {
            let complement = s ^ sub;
            if sub < complement {
                for v in 1..n {
                    let cost = dp[sub as usize][v] + dp[complement as usize][v];
                    if cost < dp[s_idx][v] {
                        dp[s_idx][v] = cost;
                        parent[s_idx][v] = (sub, v as u32);
                    }
                }
            }
            sub = (sub - 1) & s;
        }

        // Shortest-path extension: dp[S][v] = min over neighbors u of v
        //   dp[S][u] + dist(u, v)
        // Use Dijkstra-like relaxation from all nodes
        let mut heap: BinaryHeap<DpEntry> = BinaryHeap::new();
        for v in 1..n {
            if dp[s_idx][v] < f64::INFINITY {
                heap.push(DpEntry { cost: dp[s_idx][v], node: v as u32 });
            }
        }

        while let Some(DpEntry { cost, node }) = heap.pop() {
            let v = node as usize;
            if cost > dp[s_idx][v] + 1e-10 {
                continue;
            }
            for (u, edge_cost) in graph.neighbors_with_cost(v as u32) {
                let new_cost = cost + edge_cost;
                if new_cost < dp[s_idx][u as usize] - 1e-10 {
                    dp[s_idx][u as usize] = new_cost;
                    parent[s_idx][u as usize] = (s, v as u32);
                    heap.push(DpEntry { cost: new_cost, node: u });
                }
            }
        }
    }

    // Find optimal: dp[full_mask][v] for any v
    let mut best_cost = f64::INFINITY;
    let mut best_node = 1usize;
    for v in 1..n {
        if dp[full_mask as usize][v] < best_cost {
            best_cost = dp[full_mask as usize][v];
            best_node = v;
        }
    }

    if best_cost >= f64::INFINITY / 2.0 {
        return None;
    }

    // Reconstruct tree edges via backtracking
    let mut tree_edges = Vec::new();
    let mut edge_set = std::collections::HashSet::new();
    reconstruct(full_mask, best_node as u32, &dp, &parent, &dist, graph, &mut tree_edges, &mut edge_set);

    Some(DreyfusWagnerResult {
        optimal_cost: best_cost,
        tree_edges,
    })
}

fn reconstruct(
    s: u32,
    v: u32,
    dp: &[Vec<f64>],
    parent: &[Vec<(u32, u32)>],
    dist: &[Vec<f64>],
    graph: &UndirectedGraph,
    edges: &mut Vec<(NodeId, NodeId, Cost)>,
    edge_set: &mut std::collections::HashSet<(u32, u32)>,
) {
    if s == 0 || s.count_ones() <= 1 {
        return;
    }

    let (p_mask, p_node) = parent[s as usize][v as usize];

    if p_mask == s {
        // Came from shortest-path extension: edge (p_node -> v)
        let a = p_node.min(v);
        let b = p_node.max(v);
        if edge_set.insert((a, b)) {
            let cost = find_edge_cost(graph, p_node, v);
            edges.push((p_node, v, cost));
        }
        reconstruct(s, p_node, dp, parent, dist, graph, edges, edge_set);
    } else if p_mask > 0 {
        // Came from Steiner recurrence: split into p_mask and s ^ p_mask at node v
        let complement = s ^ p_mask;
        reconstruct(p_mask, v, dp, parent, dist, graph, edges, edge_set);
        reconstruct(complement, v, dp, parent, dist, graph, edges, edge_set);
    }
    // p_mask == 0: base case (singleton), nothing to recurse
}

fn find_edge_cost(graph: &UndirectedGraph, u: NodeId, v: NodeId) -> Cost {
    for &(n, eid) in graph.neighbors(u) {
        if n == v {
            return graph.edges[eid as usize].cost;
        }
    }
    f64::INFINITY
}

fn all_pairs_dijkstra(graph: &UndirectedGraph, n: usize) -> Vec<Vec<f64>> {
    let mut dist = vec![vec![f64::INFINITY; n]; n];

    for source in 1..n {
        dist[source][source] = 0.0;
        let mut heap = BinaryHeap::new();
        heap.push(DpEntry { cost: 0.0, node: source as u32 });

        while let Some(DpEntry { cost, node }) = heap.pop() {
            if cost > dist[source][node as usize] + 1e-10 {
                continue;
            }
            for (u, edge_cost) in graph.neighbors_with_cost(node) {
                let new_cost = cost + edge_cost;
                if new_cost < dist[source][u as usize] - 1e-10 {
                    dist[source][u as usize] = new_cost;
                    heap.push(DpEntry { cost: new_cost, node: u });
                }
            }
        }
    }

    dist
}

#[derive(Clone, Copy, PartialEq)]
struct DpEntry {
    cost: Cost,
    node: NodeId,
}

impl Eq for DpEntry {}

impl Ord for DpEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_cost(other.cost, self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for DpEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    #[test]
    fn test_dw_two_terminals_path() {
        // 1(T) --3-- 2(S) --4-- 3(T)
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 3.0);
        g.add_edge(2, 3, 4.0);

        let result = dreyfus_wagner(&g, &[1, 3]).unwrap();
        assert!((result.optimal_cost - 7.0).abs() < 1e-6,
            "Expected 7.0, got {}", result.optimal_cost);
    }

    #[test]
    fn test_dw_three_terminals_steiner() {
        // Triangle with Steiner node in center
        //   1(T) --1-- 2(S)
        //   |           |
        //   3(T) --1-- 4(T)
        //   1-2: cost 1, 2-4: cost 1, 1-3: cost 1, 3-4: cost 1
        //   Direct: 1-3: cost 5 (expensive)
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 4, 1.0);
        g.add_edge(1, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(1, 4, 5.0);

        let result = dreyfus_wagner(&g, &[1, 3, 4]).unwrap();
        // Optimal: 1-3 (1) + 1-2 (1) + 2-4 (1) = 3 or 1-3 (1) + 3-4 (1) = 2
        assert!(result.optimal_cost <= 2.0 + 1e-6,
            "Expected ≤ 2.0, got {}", result.optimal_cost);
    }

    #[test]
    fn test_dw_b01_structure() {
        // Small B-series-like: 5 nodes, 3 terminals
        // Optimal: connect terminals 1, 3, 5 via Steiner nodes 2, 4
        let mut g = UndirectedGraph::new(5);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_node(5, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 2.0);
        g.add_edge(2, 3, 3.0);
        g.add_edge(2, 4, 1.0);
        g.add_edge(4, 5, 2.0);
        g.add_edge(3, 5, 10.0);

        let result = dreyfus_wagner(&g, &[1, 3, 5]).unwrap();
        // Optimal: 1-2(2) + 2-3(3) + 2-4(1) + 4-5(2) = 8
        assert!((result.optimal_cost - 8.0).abs() < 1e-6,
            "Expected 8.0, got {}", result.optimal_cost);
    }

    #[test]
    fn test_dw_single_terminal() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);

        let result = dreyfus_wagner(&g, &[1]).unwrap();
        assert!((result.optimal_cost - 0.0).abs() < 1e-6);
    }
}
