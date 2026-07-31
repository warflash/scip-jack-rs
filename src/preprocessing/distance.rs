use super::ReducibleGraph;

/// Distance-based reduction techniques:
///
/// 1. **Special Distance (SD) test**: An edge {u,v} can be removed if there exists a path
///    from u to v through at least one terminal that is no more expensive than c({u,v}).
///    Formally: remove {u,v} if min_{t ∈ T} (d(u,t) + d(v,t)) ≤ c({u,v})
///    where d(x,y) is the shortest path distance.
///
/// 2. **Nearest Vertex (NV) test**: A more aggressive version that uses "special distances"
///    (bottleneck distances through terminals).
///
/// Returns number of edges removed.
pub fn distance_reductions(graph: &mut ReducibleGraph) -> u32 {
    let mut removed = 0u32;

    // Compute shortest path distances from each terminal
    let terminal_list: Vec<u32> = graph.terminals.iter().copied()
        .filter(|&t| graph.is_node_valid(t))
        .collect();

    if terminal_list.is_empty() {
        return 0;
    }

    // Precompute distances from all terminals
    let terminal_dists: Vec<Vec<f64>> = terminal_list.iter()
        .map(|&t| graph.shortest_paths_from(t))
        .collect();

    // Nodes adjacent to any contracted node have distorted shortest-path distances,
    // so edges touching those nodes must be excluded from the SD test.
    let mut contraction_affected: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for &eid in &graph.contracted_edges {
        if graph.is_edge_valid(eid) {
            let e = &graph.edges[eid as usize];
            contraction_affected.insert(e.src);
            contraction_affected.insert(e.dst);
        }
    }

    let edges_to_check: Vec<(u32, u32, u32, f64)> = graph.edges.iter()
        .filter(|e| {
            graph.is_edge_valid(e.id)
                && !graph.contracted_edges.contains(&e.id)
                && !contraction_affected.contains(&e.src)
                && !contraction_affected.contains(&e.dst)
        })
        .map(|e| (e.id, e.src, e.dst, e.cost))
        .collect();

    for (eid, src, dst, cost) in edges_to_check {
        if !graph.is_edge_valid(eid) {
            continue;
        }

        // Check: is there a terminal t such that d(src, t) + d(dst, t) < cost?
        // (Strict inequality: the alternative path must be STRICTLY cheaper
        // for the edge to be provably redundant)
        let mut can_remove = false;
        for (idx, &t) in terminal_list.iter().enumerate() {
            if t == src || t == dst {
                continue;
            }

            let d_src_t = terminal_dists[idx][src as usize];
            let d_dst_t = terminal_dists[idx][dst as usize];

            if d_src_t + d_dst_t < cost - 1e-9 {
                can_remove = true;
                break;
            }
        }

        if can_remove {
            graph.remove_edge(eid);
            removed += 1;
        }
    }

    // The "long edge" test is only valid when the nearest terminals are the SAME terminal.
    // If d(u,t) + d(v,t) <= c({u,v}) for some terminal t, the SD test above already handles it.
    // The general "nearest terminal sum" test is NOT sound for different terminals.

    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{UndirectedGraph, NodeType, SteinerInstance};

    #[test]
    fn test_sd_removes_dominated_edge() {
        // 1(T) --1-- 2(T) --1-- 3(T)
        //   \                  /
        //    -------- 10 -----
        // Edge 1-3 with cost 10 is dominated: d(1,2)+d(3,2) = 1+1 = 2 < 10
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 3, 10.0); // Should be removed

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
        let removed = distance_reductions(&mut rg);

        assert!(removed >= 1, "Should remove dominated edge");
        assert!(!rg.is_edge_valid(2), "Edge 1-3 (id=2) should be removed");
    }

    #[test]
    fn test_sd_keeps_necessary_edge() {
        // 1(T) --5-- 2(T): single edge between terminals, cannot be removed
        let mut g = UndirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 5.0);

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
        let removed = distance_reductions(&mut rg);

        assert_eq!(removed, 0, "Should not remove the only edge");
    }
}
