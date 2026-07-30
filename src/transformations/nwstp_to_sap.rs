use crate::graph::{DirectedGraph, NodeId};
use crate::graph::SteinerInstance;

/// Transformation 1 (NWSTP to SAP) from the paper.
///
/// Given NWSTP P = (V, E, T, c, p), construct SAP P' = (V', A', T', c', r'):
/// 1. V' := V, T' := T, A' := {(v,w) ∈ V'×V' : {v,w} ∈ E}
/// 2. c'(a) = c({v,w}) + p(w) for a = (v,w) ∈ A'
/// 3. Choose root r' ∈ T' arbitrarily
pub fn transform_nwstp(instance: &SteinerInstance) -> (DirectedGraph, NodeId, Vec<NodeId>) {
    let mut dg = DirectedGraph::new(instance.num_nodes);

    for node in &instance.nodes {
        dg.add_node(node.id, node.node_type, node.weight);
    }

    // Replace each edge with two anti-parallel arcs, adding node weight to head
    for edge in &instance.edges {
        let w_dst = instance.nodes.iter()
            .find(|n| n.id == edge.dst)
            .map_or(0.0, |n| n.weight);
        let w_src = instance.nodes.iter()
            .find(|n| n.id == edge.src)
            .map_or(0.0, |n| n.weight);

        // c'(v,w) = c({v,w}) + p(w)
        dg.add_arc(edge.src, edge.dst, edge.cost + w_dst);
        // c'(w,v) = c({v,w}) + p(v)
        dg.add_arc(edge.dst, edge.src, edge.cost + w_src);
    }

    let root = instance.root.unwrap_or(instance.terminals[0]);
    let terminals = instance.terminals.clone();

    (dg, root, terminals)
}
