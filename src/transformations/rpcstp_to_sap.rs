use crate::graph::{DirectedGraph, NodeId, NodeType, Node};
use crate::graph::SteinerInstance;

/// Transformation 2 (RPCSTP to SAP) from the paper.
///
/// For RPCSTP P = (V, E, p, r), construct SAP P' = (V', A', T', c', r'):
/// 1. V' := V, A' := {(v,w) : {v,w} ∈ E}, r' := r, c'(a) = c({v,w})
/// 2. For each v with p(v) > 0 (call them t_1..t_s):
///    Add new node t'_i and arc (t_i, t'_i) with cost 0
/// 3. Add arcs (r', t'_i) with weight p(t_i)
/// 4. T' := {t'_1, ..., t'_s}
pub fn transform_rpcstp(instance: &SteinerInstance) -> (DirectedGraph, NodeId, Vec<NodeId>) {
    let prize_nodes: Vec<&Node> = instance.nodes.iter()
        .filter(|n| n.weight > 0.0)
        .collect();

    let total_nodes = instance.num_nodes + prize_nodes.len() as u32;
    let mut dg = DirectedGraph::new(total_nodes);

    // Step 1: Add original nodes and arcs
    for node in &instance.nodes {
        dg.add_node(node.id, node.node_type, node.weight);
    }

    for edge in &instance.edges {
        dg.add_arc(edge.src, edge.dst, edge.cost);
        dg.add_arc(edge.dst, edge.src, edge.cost);
    }

    let root = instance.root.expect("RPCSTP requires a root node");
    let mut new_terminals = Vec::new();

    // Steps 2-4: For each prize node, add dummy terminal
    let mut next_id = instance.num_nodes;
    for prize_node in &prize_nodes {
        let dummy_id = next_id;
        next_id += 1;

        dg.add_node(dummy_id, NodeType::Terminal, 0.0);
        // Arc from original node to dummy (cost 0)
        dg.add_arc(prize_node.id, dummy_id, 0.0);
        // Arc from root to dummy (cost = prize/penalty)
        dg.add_arc(root, dummy_id, prize_node.weight);

        new_terminals.push(dummy_id);
    }

    (dg, root, new_terminals)
}
