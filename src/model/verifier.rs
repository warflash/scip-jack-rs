use std::collections::{HashSet, VecDeque};
use crate::graph::{NodeId, ArcId, Cost};
use crate::graph::directed::DirectedGraph;
use super::SteinerSolution;

/// Independent solution verifier.
///
/// Checks five properties of a candidate Steiner arborescence:
/// 1. Connectivity: all terminals reachable from root via selected arcs
/// 2. Terminal coverage: every terminal has at least one incoming arc
/// 3. Acyclicity: the arc set forms a DAG (arborescence)
/// 4. Cost consistency: recomputed cost matches reported objective_value
/// 5. Arc validity: all arc IDs exist in the graph
///
/// This is the "exactness firewall" from the research memo §P0.4.
#[derive(Debug)]
pub struct VerificationResult {
    pub is_valid: bool,
    pub violations: Vec<String>,
    pub recomputed_cost: Cost,
}

pub fn verify_solution(
    graph: &DirectedGraph,
    root: NodeId,
    terminals: &[NodeId],
    solution: &SteinerSolution,
) -> VerificationResult {
    let mut violations = Vec::new();

    // Check 0: arc validity
    for &arc_id in &solution.arcs {
        if arc_id as usize >= graph.arcs.len() {
            violations.push(format!("Arc {} does not exist (graph has {} arcs)", arc_id, graph.arcs.len()));
        }
    }
    if !violations.is_empty() {
        return VerificationResult { is_valid: false, violations, recomputed_cost: f64::NAN };
    }

    // Check 1: recompute cost
    let mut recomputed_cost: Cost = 0.0;
    for &arc_id in &solution.arcs {
        let cost = graph.arcs[arc_id as usize].cost;
        if cost.is_nan() || cost.is_infinite() {
            violations.push(format!("Arc {} has invalid cost: {}", arc_id, cost));
        }
        recomputed_cost += cost;
    }

    let cost_diff = (recomputed_cost - solution.objective_value).abs();
    if cost_diff > 1e-6 {
        violations.push(format!(
            "Cost mismatch: reported {:.6}, recomputed {:.6} (diff {:.6})",
            solution.objective_value, recomputed_cost, cost_diff
        ));
    }

    // Check 2: connectivity via BFS from root
    let arc_set: HashSet<ArcId> = solution.arcs.iter().copied().collect();
    let mut reachable: HashSet<NodeId> = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(root);
    reachable.insert(root);

    while let Some(node) = queue.pop_front() {
        for &(head, arc_id) in graph.delta_plus(node) {
            if arc_set.contains(&arc_id) && !reachable.contains(&head) {
                reachable.insert(head);
                queue.push_back(head);
            }
        }
    }

    let mut unreachable_terminals = Vec::new();
    for &t in terminals {
        if !reachable.contains(&t) {
            unreachable_terminals.push(t);
        }
    }
    if !unreachable_terminals.is_empty() {
        violations.push(format!(
            "Terminals not reachable from root {}: {:?}",
            root, unreachable_terminals
        ));
    }

    // Check 3: terminal coverage (each non-root terminal has an incoming selected arc)
    for &t in terminals {
        if t == root { continue; }
        let has_incoming = graph.delta_minus(t).iter()
            .any(|&(_, aid)| arc_set.contains(&aid));
        if !has_incoming {
            violations.push(format!("Terminal {} has no incoming selected arc", t));
        }
    }

    // Check 4: acyclicity (topological sort check on selected arc subgraph)
    // Build indegree map for selected arcs only
    let solution_nodes: HashSet<NodeId> = solution.arcs.iter()
        .flat_map(|&aid| {
            let arc = &graph.arcs[aid as usize];
            [arc.tail, arc.head]
        })
        .collect();

    let mut in_degree: std::collections::HashMap<NodeId, u32> = std::collections::HashMap::new();
    let mut adj_out: std::collections::HashMap<NodeId, Vec<NodeId>> = std::collections::HashMap::new();

    for &nid in &solution_nodes {
        in_degree.entry(nid).or_insert(0);
        adj_out.entry(nid).or_insert_with(Vec::new);
    }

    for &arc_id in &solution.arcs {
        let arc = &graph.arcs[arc_id as usize];
        *in_degree.entry(arc.head).or_insert(0) += 1;
        adj_out.entry(arc.tail).or_insert_with(Vec::new).push(arc.head);
    }

    // Kahn's algorithm for topological sort
    let mut topo_queue: VecDeque<NodeId> = VecDeque::new();
    for (&node, &deg) in &in_degree {
        if deg == 0 {
            topo_queue.push_back(node);
        }
    }

    let mut processed = 0usize;
    while let Some(v) = topo_queue.pop_front() {
        processed += 1;
        if let Some(neighbors) = adj_out.get(&v) {
            for &u in neighbors {
                if let Some(d) = in_degree.get_mut(&u) {
                    *d -= 1;
                    if *d == 0 {
                        topo_queue.push_back(u);
                    }
                }
            }
        }
    }

    if processed < solution_nodes.len() {
        violations.push(format!(
            "Cycle detected: only {}/{} nodes in topological order",
            processed, solution_nodes.len()
        ));
    }

    // Check 5: no duplicate arcs
    if arc_set.len() != solution.arcs.len() {
        violations.push(format!(
            "Duplicate arcs: {} unique out of {} listed",
            arc_set.len(), solution.arcs.len()
        ));
    }

    VerificationResult {
        is_valid: violations.is_empty(),
        violations,
        recomputed_cost,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    #[test]
    fn test_verify_valid_solution() {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0); // arc 0
        g.add_arc(2, 3, 2.0); // arc 1
        g.add_arc(2, 1, 1.0);
        g.add_arc(3, 2, 2.0);

        let sol = SteinerSolution::new(vec![0, 1], vec![1, 2, 3], 3.0);
        let result = verify_solution(&g, 1, &[3], &sol);
        assert!(result.is_valid, "Valid solution flagged as invalid: {:?}", result.violations);
        assert!((result.recomputed_cost - 3.0).abs() < 1e-6);
    }

    #[test]
    fn test_verify_disconnected_solution() {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0); // arc 0
        g.add_arc(3, 4, 1.0); // arc 1 (disconnected from root)
        g.add_arc(2, 1, 1.0);
        g.add_arc(4, 3, 1.0);

        let sol = SteinerSolution::new(vec![0, 1], vec![1, 2, 3, 4], 2.0);
        let result = verify_solution(&g, 1, &[4], &sol);
        assert!(!result.is_valid);
        assert!(result.violations.iter().any(|v| v.contains("not reachable")));
    }

    #[test]
    fn test_verify_cost_mismatch() {
        let mut g = DirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 5.0);
        g.add_arc(2, 1, 5.0);

        let sol = SteinerSolution::new(vec![0], vec![1, 2], 999.0);
        let result = verify_solution(&g, 1, &[2], &sol);
        assert!(!result.is_valid);
        assert!(result.violations.iter().any(|v| v.contains("Cost mismatch")));
    }

    #[test]
    fn test_verify_cycle() {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0); // arc 0
        g.add_arc(2, 3, 1.0); // arc 1
        g.add_arc(3, 2, 1.0); // arc 2 (creates cycle 2→3→2)

        let sol = SteinerSolution::new(vec![0, 1, 2], vec![1, 2, 3], 3.0);
        let result = verify_solution(&g, 1, &[3], &sol);
        assert!(!result.is_valid);
        assert!(result.violations.iter().any(|v| v.contains("Cycle")));
    }
}
