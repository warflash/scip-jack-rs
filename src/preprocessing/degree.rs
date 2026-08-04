use crate::graph::{EdgeId, Cost};
use super::ReducibleGraph;

/// Degree-based reduction techniques:
///
/// 1. **Degree-1 test**: Remove non-terminal nodes with degree 1 (and incident edge)
/// 2. **Degree-2 test**: Contract non-terminal nodes with degree 2 (replace with direct edge)
/// 3. **Terminal degree-1 test**: Fix the unique edge incident to a degree-1 terminal
/// 4. **Parallel edge removal**: Keep only the cheapest among parallel edges
///
/// Returns (number_of_changes, fixed_edges, lower_bound_offset).
pub fn degree_reductions(graph: &mut ReducibleGraph) -> (u32, Vec<EdgeId>, Cost) {
    let mut changes = 0u32;
    let mut fixed_edges: Vec<EdgeId> = Vec::new();
    let lb_offset: Cost = 0.0;
    let mut changed = true;

    while changed {
        changed = false;

        let nodes = graph.valid_nodes();
        for &node in &nodes {
            let degree = graph.degree(node);

            // Degree-0: isolated node, just remove it (unless it's a terminal)
            if degree == 0 && !graph.is_terminal(node) {
                graph.remove_node(node);
                changes += 1;
                changed = true;
                continue;
            }

            // Degree-1 Steiner: remove node and edge
            if degree == 1 && !graph.is_terminal(node) {
                graph.remove_node(node);
                changes += 1;
                changed = true;
                continue;
            }

            // Degree-1 Terminal: fix the incident edge (it must be in every optimal solution)
            // Note: we do NOT add to lb_offset here because the edge remains in the graph
            // and will be counted in the solver's solution. We just record which edges are fixed.
            if degree == 1 && graph.is_terminal(node) {
                if let Some((_, eid)) = graph.valid_neighbors_iter(node).next() {
                    if !fixed_edges.contains(&eid) {
                        fixed_edges.push(eid);
                    }
                }
            }

            // Degree-2 Steiner: contract
            if degree == 2 && !graph.is_terminal(node) {
                if graph.contract_degree2(node).is_some() {
                    changes += 1;
                    changed = true;
                    continue;
                }
            }
        }

        // Parallel edge removal: for each pair of adjacent nodes, keep only cheapest edge
        changes += remove_parallel_edges(graph);
    }

    (changes, fixed_edges, lb_offset)
}

/// Remove parallel edges between same pair of nodes, keeping only the cheapest,
/// and drop self-loops.
///
/// A loop `{u, u}` is a cycle on its own, so no tree contains it and deleting it
/// preserves every solution. Keying loops by `(u, u)` in the parallel-edge map
/// would instead keep one of them forever, and a surviving loop is not merely
/// useless: it lands twice in the LP's flow-balance row for `u`, which is an
/// invalid model rather than a weak one.
fn remove_parallel_edges(graph: &mut ReducibleGraph) -> u32 {
    let mut removed = 0u32;
    let mut seen: std::collections::HashMap<(u32, u32), (EdgeId, Cost)> = std::collections::HashMap::new();
    let mut to_remove: Vec<EdgeId> = Vec::new();

    for edge in &graph.edges {
        if !graph.is_edge_valid(edge.id) {
            continue;
        }

        if edge.src == edge.dst {
            to_remove.push(edge.id);
            continue;
        }

        let key = if edge.src < edge.dst {
            (edge.src, edge.dst)
        } else {
            (edge.dst, edge.src)
        };

        match seen.get(&key) {
            Some(&(existing_eid, existing_cost)) => {
                if edge.cost < existing_cost {
                    to_remove.push(existing_eid);
                    seen.insert(key, (edge.id, edge.cost));
                } else {
                    to_remove.push(edge.id);
                }
            }
            None => {
                seen.insert(key, (edge.id, edge.cost));
            }
        }
    }

    for eid in to_remove {
        graph.remove_edge(eid);
        removed += 1;
    }

    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{UndirectedGraph, NodeType, SteinerInstance};

    #[test]
    fn test_parallel_edge_removal() {
        let mut g = UndirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 5.0); // 0
        g.add_edge(1, 2, 3.0); // 1
        g.add_edge(1, 2, 7.0); // 2

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 2,
            num_edges: 3,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2],
            root: Some(1),
        };

        let mut rg = ReducibleGraph::from_instance(&instance, &g);
        let (changes, _, _) = degree_reductions(&mut rg);

        assert!(changes >= 2, "Should remove 2 parallel edges, removed {}", changes);
        // The cheapest edge (cost 3) should remain
        let valid = rg.valid_edges();
        assert_eq!(valid.len(), 1);
        assert_eq!(rg.edges[valid[0] as usize].cost, 3.0);
    }
}
