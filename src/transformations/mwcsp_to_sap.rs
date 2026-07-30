use crate::graph::{DirectedGraph, NodeId, NodeType, Node};
use crate::graph::SteinerInstance;

/// Transformation 4 (MWCSP to SAP) from the paper.
///
/// Given MWCSP P = (V, E, p), construct SAP P'' = (V'', A'', T'', c'', r''):
/// 1. V' := V, A' := {(v,w) : {v,w} ∈ E}
/// 2. c'(a) for a=(v,w): = -p(w) if p(w) < 0, else 0
/// 3. p'(v): = p(v) if p(v) > 0, else 0
/// 4. Perform Transformation 3 (PCSTP to SAP) on (V', A', c', p')
///
/// Objective value relationship: C(S) = -C''(S'') + Σ_{v: p(v)>0} p(v)
pub fn transform_mwcsp(instance: &SteinerInstance) -> (DirectedGraph, NodeId, Vec<NodeId>, f64) {
    let positive_weight_sum: f64 = instance.nodes.iter()
        .filter(|n| n.weight > 0.0)
        .map(|n| n.weight)
        .sum();

    let positive_nodes: Vec<&Node> = instance.nodes.iter()
        .filter(|n| n.weight > 0.0)
        .collect();

    let artificial_root_id = instance.num_nodes;
    let total_nodes = instance.num_nodes + 1 + positive_nodes.len() as u32;
    let mut dg = DirectedGraph::new(total_nodes);

    // Add original nodes
    for node in &instance.nodes {
        dg.add_node(node.id, node.node_type, node.weight);
    }

    // Add artificial root
    dg.add_node(artificial_root_id, NodeType::Steiner, 0.0);

    // Step 1-2: Add arcs with modified costs
    for edge in &instance.edges {
        let dst_node = instance.nodes.iter().find(|n| n.id == edge.dst).unwrap();
        let src_node = instance.nodes.iter().find(|n| n.id == edge.src).unwrap();

        // c'(v,w) = -p(w) if p(w) < 0, else 0
        let cost_to_dst = if dst_node.weight < 0.0 { -dst_node.weight } else { 0.0 };
        let cost_to_src = if src_node.weight < 0.0 { -src_node.weight } else { 0.0 };

        dg.add_arc(edge.src, edge.dst, cost_to_dst);
        dg.add_arc(edge.dst, edge.src, cost_to_src);
    }

    // Step 3-4: Apply PCSTP transformation for positive-weight nodes
    let mut new_terminals = Vec::new();
    let mut next_id = artificial_root_id + 1;

    for pos_node in &positive_nodes {
        let dummy_id = next_id;
        next_id += 1;

        dg.add_node(dummy_id, NodeType::Terminal, 0.0);
        dg.add_arc(pos_node.id, dummy_id, 0.0);
        dg.add_arc(artificial_root_id, dummy_id, pos_node.weight);

        new_terminals.push(dummy_id);
    }

    // Zero-cost arcs from root to positive nodes
    for pos_node in &positive_nodes {
        dg.add_arc(artificial_root_id, pos_node.id, 0.0);
    }

    (dg, artificial_root_id, new_terminals, positive_weight_sum)
}
