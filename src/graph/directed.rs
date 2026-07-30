use std::collections::HashMap;
use super::types::*;

/// Directed graph (digraph) using adjacency list representation.
/// Used for the Steiner arborescence formulation where each undirected edge
/// becomes two anti-parallel arcs.
#[derive(Debug, Clone)]
pub struct DirectedGraph {
    pub num_nodes: u32,
    pub nodes: Vec<Node>,
    pub arcs: Vec<Arc>,
    /// Outgoing arcs: node -> [(head, arc_id)]
    out_adjacency: HashMap<NodeId, Vec<(NodeId, ArcId)>>,
    /// Incoming arcs: node -> [(tail, arc_id)]
    in_adjacency: HashMap<NodeId, Vec<(NodeId, ArcId)>>,
}

impl DirectedGraph {
    pub fn new(num_nodes: u32) -> Self {
        Self {
            num_nodes,
            nodes: Vec::with_capacity(num_nodes as usize),
            arcs: Vec::new(),
            out_adjacency: HashMap::with_capacity(num_nodes as usize),
            in_adjacency: HashMap::with_capacity(num_nodes as usize),
        }
    }

    pub fn add_node(&mut self, id: NodeId, node_type: NodeType, weight: Cost) {
        self.nodes.push(Node { id, node_type, weight });
        self.out_adjacency.entry(id).or_default();
        self.in_adjacency.entry(id).or_default();
    }

    pub fn add_arc(&mut self, tail: NodeId, head: NodeId, cost: Cost) -> ArcId {
        let arc_id = self.arcs.len() as ArcId;
        self.arcs.push(Arc { id: arc_id, tail, head, cost });
        self.out_adjacency.entry(tail).or_default().push((head, arc_id));
        self.in_adjacency.entry(head).or_default().push((tail, arc_id));
        arc_id
    }

    /// δ+(v): outgoing arcs from node v
    pub fn delta_plus(&self, node: NodeId) -> &[(NodeId, ArcId)] {
        self.out_adjacency.get(&node).map_or(&[], |v| v.as_slice())
    }

    /// δ⁻(v): incoming arcs to node v
    pub fn delta_minus(&self, node: NodeId) -> &[(NodeId, ArcId)] {
        self.in_adjacency.get(&node).map_or(&[], |v| v.as_slice())
    }

    /// δ+(W): arcs with tail in W and head in V \ W
    pub fn delta_plus_set(&self, w: &[NodeId]) -> Vec<ArcId> {
        let w_set: std::collections::HashSet<NodeId> = w.iter().copied().collect();
        let mut result = Vec::new();
        for &node in w {
            for &(head, arc_id) in self.delta_plus(node) {
                if !w_set.contains(&head) {
                    result.push(arc_id);
                }
            }
        }
        result
    }

    pub fn out_degree(&self, node: NodeId) -> usize {
        self.out_adjacency.get(&node).map_or(0, |v| v.len())
    }

    pub fn in_degree(&self, node: NodeId) -> usize {
        self.in_adjacency.get(&node).map_or(0, |v| v.len())
    }

    pub fn num_arcs(&self) -> u32 {
        self.arcs.len() as u32
    }

    /// Create a directed graph from an undirected graph by replacing each edge
    /// with two anti-parallel arcs (the fundamental STP → SAP transformation).
    pub fn from_undirected(graph: &super::UndirectedGraph) -> Self {
        let mut dg = Self::new(graph.num_nodes);

        for node in &graph.nodes {
            dg.add_node(node.id, node.node_type, node.weight);
        }

        for edge in &graph.edges {
            dg.add_arc(edge.src, edge.dst, edge.cost);
            dg.add_arc(edge.dst, edge.src, edge.cost);
        }

        dg
    }
}
