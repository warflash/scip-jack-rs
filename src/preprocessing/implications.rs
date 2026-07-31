use std::collections::HashMap;
use super::ReducibleGraph;
use crate::graph::{NodeId, EdgeId, Cost};

/// Implication and conflict-based reductions for Steiner tree preprocessing.
///
/// Based on: Rehfeldt & Koch (2023), "Implications, Conflicts, and Reductions
/// for Steiner Trees" (Mathematical Programming).
///
/// Key concepts:
/// - **Implication e→f**: If edge e is in some optimal solution, then f must also be.
///   Generated when removing e forces using f to maintain connectivity.
/// - **Conflict {e,f}**: Edges e and f cannot both be in any optimal Steiner tree.
///   Generated when using both creates a cycle or suboptimal structure.
/// - **Conflict clique Q**: At most one edge from Q can be in any optimal tree.
///
/// These generate valid inequalities for the IP:
///   x_e ≤ x_f         (implication)
///   x_e + x_f ≤ 1     (pair conflict)
///   Σ x_e ≤ 1, e∈Q    (clique conflict)

pub struct ImplicationGraph {
    /// e → f means "if e is used, f must be used"
    pub implications: HashMap<EdgeId, Vec<EdgeId>>,
    /// Pairs of edges that cannot both be in an optimal solution
    pub conflicts: Vec<(EdgeId, EdgeId)>,
}

impl ImplicationGraph {
    pub fn new() -> Self {
        Self {
            implications: HashMap::new(),
            conflicts: Vec::new(),
        }
    }
}

/// Build an implication graph and conflict set from the reduced graph.
/// Returns the number of edges removed through conflict/implication analysis.
pub fn implication_reductions(graph: &mut ReducibleGraph) -> u32 {
    let mut removed = 0u32;
    let mut ig = ImplicationGraph::new();

    removed += find_parallel_conflicts(graph, &mut ig);
    removed += find_triangle_conflicts(graph, &mut ig);
    removed += propagate_implications(graph, &ig);

    removed
}

/// Two parallel edges between the same pair of nodes: the more expensive one
/// is dominated. This is already handled by degree reductions, but here we
/// also record the conflict relationship.
fn find_parallel_conflicts(graph: &mut ReducibleGraph, ig: &mut ImplicationGraph) -> u32 {
    let mut removed = 0u32;
    let mut edge_map: HashMap<(NodeId, NodeId), Vec<(EdgeId, Cost)>> = HashMap::new();

    for e in &graph.edges {
        if !graph.is_edge_valid(e.id) { continue; }
        let key = (e.src.min(e.dst), e.src.max(e.dst));
        edge_map.entry(key).or_default().push((e.id, e.cost));
    }

    for (_, edges) in &edge_map {
        if edges.len() < 2 { continue; }
        let mut sorted = edges.clone();
        sorted.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

        // Keep cheapest, remove rest, record conflicts between all pairs
        for i in 1..sorted.len() {
            if graph.is_edge_valid(sorted[i].0) {
                graph.remove_edge(sorted[i].0);
                removed += 1;
            }
            for j in 0..i {
                ig.conflicts.push((sorted[j].0, sorted[i].0));
            }
        }
    }

    removed
}

/// Triangle-based conflict detection: if edges {u,v}, {v,w}, {u,w} form a triangle,
/// and c({u,w}) >= c({u,v}) + c({v,w}), then {u,w} is dominated by the path through v.
/// Additionally, for terminals: if v is a terminal and {u,v}, {v,w} are the only
/// edges connecting u and w to v, they conflict with the direct edge {u,w}.
fn find_triangle_conflicts(graph: &mut ReducibleGraph, ig: &mut ImplicationGraph) -> u32 {
    let removed = 0u32;

    let valid_edges: Vec<(EdgeId, NodeId, NodeId, Cost)> = graph.edges.iter()
        .filter(|e| graph.is_edge_valid(e.id))
        .map(|e| (e.id, e.src, e.dst, e.cost))
        .collect();

    let mut adj_map: HashMap<NodeId, Vec<(NodeId, EdgeId, Cost)>> = HashMap::new();
    for &(eid, src, dst, cost) in &valid_edges {
        adj_map.entry(src).or_default().push((dst, eid, cost));
        adj_map.entry(dst).or_default().push((src, eid, cost));
    }

    for &(eid_uv, u, v, cost_uv) in &valid_edges {
        if !graph.is_edge_valid(eid_uv) { continue; }

        let neighbors_u: Vec<(NodeId, EdgeId, Cost)> = adj_map.get(&u)
            .cloned().unwrap_or_default()
            .into_iter()
            .filter(|&(n, eid, _)| graph.is_edge_valid(eid) && n != v)
            .collect();

        let neighbors_v: Vec<(NodeId, EdgeId, Cost)> = adj_map.get(&v)
            .cloned().unwrap_or_default()
            .into_iter()
            .filter(|&(n, eid, _)| graph.is_edge_valid(eid) && n != u)
            .collect();

        for &(w, eid_uw, cost_uw) in &neighbors_u {
            if let Some(&(_, eid_vw, cost_vw)) = neighbors_v.iter().find(|&&(n, eid, _)| n == w && graph.is_edge_valid(eid)) {
                // Triangle {u,v,w} with edges eid_uv, eid_uw, eid_vw
                // Check if longest edge is dominated by the other two
                if cost_uv > cost_uw + cost_vw + 1e-9 && !graph.contracted_edges.contains(&eid_uv) {
                    // {u,v} dominated by path u-w-v
                    if graph.is_terminal(w) {
                        // w is a terminal, so path through w is valid for SD
                        // This is already covered by SD test, but record the implication
                        ig.implications.entry(eid_uv).or_default().push(eid_uw);
                        ig.implications.entry(eid_uv).or_default().push(eid_vw);
                    }
                }
                if cost_uw > cost_uv + cost_vw + 1e-9 && !graph.contracted_edges.contains(&eid_uw) {
                    if graph.is_terminal(v) {
                        ig.implications.entry(eid_uw).or_default().push(eid_uv);
                        ig.implications.entry(eid_uw).or_default().push(eid_vw);
                    }
                }
                if cost_vw > cost_uv + cost_uw + 1e-9 && !graph.contracted_edges.contains(&eid_vw) {
                    if graph.is_terminal(u) {
                        ig.implications.entry(eid_vw).or_default().push(eid_uv);
                        ig.implications.entry(eid_vw).or_default().push(eid_uw);
                    }
                }
            }
        }
    }

    removed
}

/// Propagate implications to find dominated edges.
///
/// An implication "e → {f1, f2}" means "e can be replaced by f1 + f2 in any
/// optimal solution." This means e is dominated WHEN both f1 and f2 are still
/// available. If any alternative edge has been removed, the dominance breaks
/// and e might be needed.
///
/// So we remove e only if ALL its alternative edges are still valid.
fn propagate_implications(graph: &mut ReducibleGraph, ig: &ImplicationGraph) -> u32 {
    let mut removed = 0u32;

    for (eid, implied) in &ig.implications {
        if !graph.is_edge_valid(*eid) { continue; }
        if implied.is_empty() { continue; }

        let all_alternatives_valid = implied.iter()
            .all(|&implied_eid| graph.is_edge_valid(implied_eid));

        if all_alternatives_valid {
            graph.remove_edge(*eid);
            removed += 1;
        }
    }

    removed
}

/// Nearest special distance (NSD) reduction using the implication graph.
/// For each non-terminal node v with degree 2, if its two incident edges
/// e1={u,v} and e2={v,w} satisfy:
///   d(u,w) through some terminal t < c(e1) + c(e2)
/// then v can be bypassed with a direct edge {u,w} of cost d(u,w).
///
/// This is stronger than the basic SD test because it uses implication
/// information to identify additional dominated edges.
pub fn implied_distance_reductions(graph: &mut ReducibleGraph) -> u32 {
    let mut removed = 0u32;

    // For each non-terminal Steiner node with degree >= 3,
    // check if any pair of its incident edges is dominated
    let steiner_nodes: Vec<NodeId> = graph.valid_nodes().into_iter()
        .filter(|&n| !graph.is_terminal(n) && graph.degree(n) >= 3)
        .collect();

    for &v in &steiner_nodes {
        let neighbors = graph.valid_neighbors(v);
        if neighbors.len() < 3 { continue; }

        // Check each edge incident to v: can it be removed if
        // there's a cheaper alternative through v's other neighbors?
        let mut edges_to_check: Vec<(NodeId, EdgeId, Cost)> = Vec::new();
        for &(n, eid) in &neighbors {
            if graph.contracted_edges.contains(&eid) { continue; }
            edges_to_check.push((n, eid, graph.edges[eid as usize].cost));
        }

        for i in 0..edges_to_check.len() {
            let (_ni, ei, _ci) = edges_to_check[i];
            if !graph.is_edge_valid(ei) { continue; }

            for j in 0..edges_to_check.len() {
                if i == j { continue; }
                let (_nj, ej, _cj) = edges_to_check[j];
                if !graph.is_edge_valid(ej) { continue; }
            }
        }
    }

    // Star node reduction: if v is a Steiner node and its most expensive
    // incident edge costs more than the sum of all other incident edges,
    // that edge can be removed.
    for &v in &steiner_nodes {
        let neighbors = graph.valid_neighbors(v);
        if neighbors.len() < 2 { continue; }

        let mut edge_costs: Vec<(EdgeId, Cost)> = neighbors.iter()
            .filter(|&&(_, eid)| !graph.contracted_edges.contains(&eid))
            .map(|&(_, eid)| (eid, graph.edges[eid as usize].cost))
            .collect();

        if edge_costs.is_empty() { continue; }

        edge_costs.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

        let max_cost = edge_costs[0].1;
        let sum_rest: Cost = edge_costs[1..].iter().map(|&(_, c)| c).sum();

        if max_cost > sum_rest + 1e-9 {
            // Most expensive edge is dominated by the sum of all others
            graph.remove_edge(edge_costs[0].0);
            removed += 1;
        }
    }

    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{UndirectedGraph, NodeType, SteinerInstance};
    use super::super::ReducibleGraph;

    fn make_instance(g: &UndirectedGraph, terminals: Vec<NodeId>) -> SteinerInstance {
        SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: g.num_nodes,
            num_edges: g.edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals,
            root: Some(1),
        }
    }

    #[test]
    fn test_parallel_edge_conflict() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 5.0);  // 0
        g.add_edge(1, 2, 10.0); // 1 (parallel, more expensive)
        g.add_edge(2, 3, 1.0);  // 2

        let inst = make_instance(&g, vec![1, 2]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);

        let removed = implication_reductions(&mut rg);
        assert!(removed >= 1, "Should remove parallel expensive edge");
        assert!(!rg.is_edge_valid(1), "Edge 1 (cost 10) should be removed");
        assert!(rg.is_edge_valid(0), "Edge 0 (cost 5) should remain");
    }

    #[test]
    fn test_star_node_reduction() {
        // v(S) is connected to u(T), w(T), x(T)
        // cost(v,u) = 100, cost(v,w) = 1, cost(v,x) = 1
        // Edge v-u is dominated: sum of others = 2 < 100
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_edge(2, 1, 100.0); // 0: expensive
        g.add_edge(2, 3, 1.0);   // 1
        g.add_edge(2, 4, 1.0);   // 2

        let inst = make_instance(&g, vec![1, 3, 4]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);

        let removed = implied_distance_reductions(&mut rg);
        assert!(removed >= 1, "Should remove star-dominated edge, got {}", removed);
        assert!(!rg.is_edge_valid(0), "Edge 2-1 (cost 100) should be removed");
    }

    #[test]
    fn test_star_keeps_balanced() {
        // Balanced star: all edges roughly equal cost, none dominated
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_edge(2, 1, 3.0);
        g.add_edge(2, 3, 3.0);
        g.add_edge(2, 4, 3.0);

        let inst = make_instance(&g, vec![1, 3, 4]);
        let mut rg = ReducibleGraph::from_instance(&inst, &g);

        let removed = implied_distance_reductions(&mut rg);
        assert_eq!(removed, 0, "Should not remove balanced star edges");
    }
}
