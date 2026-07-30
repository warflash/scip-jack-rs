use crate::graph::{DirectedGraph, NodeId, NodeType, Node};
use crate::graph::SteinerInstance;

/// Transformation 3 (PCSTP to SAP) from the paper.
///
/// Let P = (V, E, p) be a PCSTP, construct SAP P' = (V', A', T', c', r'):
/// 1. Add artificial root vertex v_0, set r := v_0
/// 2. Apply Transformation 2 (RPCSTP to SAP) to get P'
/// 3. Add arcs (r', t_i) with c'(a) := 0 for each t_i ∈ T
///
/// Additionally, the root constraint is enforced:
///   Σ_{a ∈ δ+(r'), c'(a)=0} y_a ≤ 1                     (9)
pub fn transform_pcstp(instance: &SteinerInstance) -> (DirectedGraph, NodeId, Vec<NodeId>, bool) {
    let prize_nodes: Vec<&Node> = instance.nodes.iter()
        .filter(|n| n.weight > 0.0)
        .collect();

    // Need: original nodes + 1 artificial root + dummy terminals
    let artificial_root_id = instance.num_nodes;
    let total_nodes = instance.num_nodes + 1 + prize_nodes.len() as u32;
    let mut dg = DirectedGraph::new(total_nodes);

    // Add original nodes
    for node in &instance.nodes {
        dg.add_node(node.id, node.node_type, node.weight);
    }

    // Step 1: Add artificial root
    dg.add_node(artificial_root_id, NodeType::Steiner, 0.0);

    // Add original edges as arcs
    for edge in &instance.edges {
        dg.add_arc(edge.src, edge.dst, edge.cost);
        dg.add_arc(edge.dst, edge.src, edge.cost);
    }

    let mut new_terminals = Vec::new();

    // Step 2-3: For each prize node, create dummy terminal
    let mut next_id = artificial_root_id + 1;
    for prize_node in &prize_nodes {
        let dummy_id = next_id;
        next_id += 1;

        dg.add_node(dummy_id, NodeType::Terminal, 0.0);
        // Arc from original node to dummy (cost 0)
        dg.add_arc(prize_node.id, dummy_id, 0.0);
        // Arc from artificial root to dummy (cost = prize)
        dg.add_arc(artificial_root_id, dummy_id, prize_node.weight);

        new_terminals.push(dummy_id);
    }

    // Step 3: Add zero-cost arcs from root to original prize nodes
    for prize_node in &prize_nodes {
        dg.add_arc(artificial_root_id, prize_node.id, 0.0);
    }

    // has_root_constraint = true means constraint (9) must be enforced
    (dg, artificial_root_id, new_terminals, true)
}
