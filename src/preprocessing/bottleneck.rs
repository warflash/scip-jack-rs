use super::ReducibleGraph;

/// Bottleneck Steiner Distance (BSD) test:
///
/// An edge {u,v} with cost c can be removed if c > s(u,v), where s(u,v)
/// is the bottleneck Steiner distance. From Rehfeldt-Koch 2023, Theorem 1:
///
///   s(u,v) = bottleneck distance from u to v in the distance network D_G(T ∪ {u,v})
///
/// where D is the complete metric graph on terminals plus the two edge endpoints,
/// with edge weights = shortest-path distances in G.
///
/// Practical computation: s(u,v) = min over terminals t of
///   max(d_G(u,t), d_G(t,v))
/// where d_G is the shortest-path metric in G with edge {u,v} REMOVED.
///
/// Conservative approximation (correct but weaker): use d_G computed on the
/// full graph. This is valid because removing edge {u,v} can only increase
/// distances, so: d_G_minus_e(u,t) >= d_G(u,t). Therefore:
///   s(u,v) >= min_t max(d_G(u,t), d_G(t,v))
///
/// WAIT - that means using full-graph distances gives a LOWER bound on s(u,v),
/// making the test `c > s(u,v)` MORE aggressive (more removals) when using
/// full-graph distances. This could be UNSOUND!
///
/// Correct approach: for each edge {u,v}, compute shortest path distances
/// from u and from v in the graph WITH edge {u,v} removed, then check
/// if any terminal provides an alternative path with bottleneck < c.
///
/// Efficient implementation: compute APSP from terminals, then for each edge
/// {u,v}, check if d(u,t) + d(v,t) < c using terminal distances that avoid
/// the edge. Since terminal Dijkstra uses the full graph, the paths MIGHT
/// use edge {u,v}. If d(u,t) path goes through edge {u,v}:
///   d(u,t) = c({u,v}) + d(v,t)
/// so: d(u,t) + d(v,t) = c + 2*d(v,t) >= c
/// meaning the test `d(u,t) + d(v,t) < c` CANNOT be triggered.
/// This proves the SD test (with strict < c) is correct even with full-graph distances!
///
/// For the BOTTLENECK version (max instead of sum):
///   BSD(u,v) = min_t max(d(u,t), d(v,t))    [not additive - shortest paths]
///
/// Actually the paper's special distance uses d = shortest-path-distance in the
/// metric closure: s(u,v) = min_{P: u→v through ≥1 terminal} max_{e∈P} c(e)
/// where P traverses the distance network. This equals:
///   s(u,v) = min_t max(d_G(u,t), d_G(v,t))
/// where d_G(u,t) is the shortest-path distance from u to t in G.
///
/// Correctness proof for using full-graph distances:
/// If the shortest path from u to t in the full graph uses edge {u,v},
/// then d(u,t) = c({u,v}) + d(v,t), so max(d(u,t), d(v,t)) = c + d(v,t) >= c.
/// Similarly for d(v,t) using edge {u,v}. So any terminal where the test
/// passes (max < c) necessarily provides a path that does NOT use edge {u,v}.
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

    // Compute shortest-path distances from each terminal
    let terminal_dists: Vec<Vec<f64>> = terminal_list.iter()
        .map(|&t| graph.shortest_paths_from(t))
        .collect();

    let edges_to_check: Vec<(u32, u32, u32, f64)> = graph.edges.iter()
        .filter(|e| {
            graph.is_edge_valid(e.id)
                && !graph.contracted_edges.contains(&e.id)
        })
        .map(|e| (e.id, e.src, e.dst, e.cost))
        .collect();

    for (eid, src, dst, cost) in edges_to_check {
        if !graph.is_edge_valid(eid) {
            continue;
        }

        // Compute s(src, dst) = min over all terminals t of max(d(src,t), d(dst,t))
        // If s(src, dst) < cost, edge can be removed (Theorem 1 of Rehfeldt-Koch 2023)
        let mut bsd = f64::INFINITY;

        for (idx, &t) in terminal_list.iter().enumerate() {
            // Skip endpoints themselves: we need a path that goes THROUGH a terminal
            if t == src || t == dst {
                continue;
            }

            let d_src_t = terminal_dists[idx][src as usize];
            let d_dst_t = terminal_dists[idx][dst as usize];

            if d_src_t == f64::INFINITY || d_dst_t == f64::INFINITY {
                continue;
            }

            let through_t = d_src_t.max(d_dst_t);
            bsd = bsd.min(through_t);
        }

        // Remove edge if cost > BSD (strictly dominated by alternative).
        // Use strict inequality with tolerance to avoid numerical precision issues.
        // Since all costs are integers in SteinLib instances, a tolerance of 0.5
        // ensures we only remove edges strictly dominated by integer distances.
        if cost > bsd + 0.5 {
            graph.remove_edge(eid);
            removed += 1;
        }
    }

    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{UndirectedGraph, NodeType, SteinerInstance};

    #[test]
    fn test_bottleneck_removes_expensive_edge() {
        // 1(T) --1-- 2(T) --1-- 3(T) and edge 1-3 cost 5
        // BSD(1,3) via terminal 2: max(d(1,2), d(3,2)) = max(1, 1) = 1
        // Since cost 5 > BSD 1, edge should be removed
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(1, 3, 5.0); // 2: should be removed

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
        // 1(T) --3-- 2(T): single connection, no alternative through another terminal
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

    #[test]
    fn test_bottleneck_steiner_node_path() {
        // 1(T) --2-- 2(S) --2-- 3(T) --2-- 4(S) --10-- 5(T)
        // Edge 4-5 cost 10: BSD via terminal 3: max(d(4,3), d(5,3)) = max(2, ?)
        // d(5,3) via 4-3 = 2 + 2 = 4? No, d(5,3) = 10 + 2 = 12 (only path 5-4-3)
        // Wait, but there's no direct 5-3 edge. d(5,3) = 10 + 2 = 12
        // BSD(4,5) = min_t max(d(4,t), d(5,t))
        //   via t=1: max(2+2, 10+2+2+2) = max(4, 16) = 16
        //   via t=3: max(2, 12) = 12
        // BSD = 12. cost = 10 < BSD, so edge NOT removed. Correct!
        let mut g = UndirectedGraph::new(5);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_node(5, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 2.0); // 0
        g.add_edge(2, 3, 2.0); // 1
        g.add_edge(3, 4, 2.0); // 2
        g.add_edge(4, 5, 10.0); // 3

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 5,
            num_edges: 4,
            num_terminals: 3,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 3, 5],
            root: Some(1),
        };

        let mut rg = ReducibleGraph::from_instance(&instance, &g);
        let removed = bottleneck_reductions(&mut rg);

        assert_eq!(removed, 0, "Should not remove edge 4-5 (cost 10 < BSD 12)");
    }

    #[test]
    fn test_bottleneck_vs_sd() {
        // BSD is strictly stronger than SD for some instances.
        // 1(T) --3-- 2(S) --3-- 3(T) --3-- 4(S) --3-- 5(T)
        //            |                                  |
        //            +------------- 5 -----------------+
        //
        // Edge 2-5 cost 5:
        // SD test: d(2,t) + d(5,t) for each terminal t:
        //   t=1: d(2,1) + d(5,1) = 3 + (5 or 9) = 8 or 12. Min path: 3+5=8? No, d(5,1)=9 via 5-4-3-2-1
        //   Actually with edge 2-5: d(5,1) = min(5+3, 3+3+3+3) = min(8, 12) = 8
        //   SD: d(2,t)+d(5,t) via t=3: d(2,3)+d(5,3) = 3 + min(5+3,3+3)=3+5(via 2-5-?)...
        // This gets complex. Let's use a simpler distinguishing example.
        //
        // 1(T) --1-- 2(T) --5-- 3(T)
        //            |           |
        //            +----3------+
        //
        // Edges: 1-2(1), 2-3(5), 2-3(3) [parallel]
        // With parallel edges: edge 2-3 cost 5. SD: d(2,1)+d(3,1) = 1+min(5,3)+1 = 1+2=3? 
        // No: d(3,1) = min(5+1, 3+1) = 4. So SD: d(2,1)+d(3,1) = 1+4 = 5 = cost. Not < cost. Not removed by SD.
        // BSD: max(d(2,1), d(3,1)) = max(1, 4) = 4 < 5. Removed by BSD!
        //
        // Actually this example doesn't work cleanly with our graph structure (parallel edges).
        // Let me just verify basic correctness.

        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        // 1 --1-- 2 --1-- 3 --1-- 4
        //         |               |
        //         +------5--------+
        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(3, 4, 1.0); // 2
        g.add_edge(2, 4, 5.0); // 3: cost 5

        // BSD(2,4) = min_t max(d(2,t), d(4,t))
        //   t=1: max(d(2,1), d(4,1)) = max(1, min(5+1, 1+1+1)) = max(1, 3) = 3
        // Since cost 5 > BSD 3, edge should be removed
        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 4,
            num_edges: 4,
            num_terminals: 3,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2, 4],
            root: Some(1),
        };

        let mut rg = ReducibleGraph::from_instance(&instance, &g);
        let removed = bottleneck_reductions(&mut rg);

        assert!(removed >= 1, "BSD should remove edge 2-4 (cost 5, BSD=3)");
    }
}
