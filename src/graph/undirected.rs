use std::collections::HashMap;
use super::types::*;

/// Undirected graph using adjacency list representation.
/// Stores edges as pairs and maintains adjacency information for efficient traversal.
#[derive(Debug, Clone)]
pub struct UndirectedGraph {
    pub num_nodes: u32,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    adjacency: HashMap<NodeId, Vec<(NodeId, EdgeId)>>,
}

impl UndirectedGraph {
    pub fn new(num_nodes: u32) -> Self {
        Self {
            num_nodes,
            nodes: Vec::with_capacity(num_nodes as usize),
            edges: Vec::new(),
            adjacency: HashMap::with_capacity(num_nodes as usize),
        }
    }

    pub fn add_node(&mut self, id: NodeId, node_type: NodeType, weight: Cost) {
        self.nodes.push(Node { id, node_type, weight });
        self.adjacency.entry(id).or_default();
    }

    pub fn add_edge(&mut self, src: NodeId, dst: NodeId, cost: Cost) -> EdgeId {
        let edge_id = self.edges.len() as EdgeId;
        self.edges.push(Edge { id: edge_id, src, dst, cost });
        self.adjacency.entry(src).or_default().push((dst, edge_id));
        self.adjacency.entry(dst).or_default().push((src, edge_id));
        edge_id
    }

    pub fn neighbors(&self, node: NodeId) -> &[(NodeId, EdgeId)] {
        self.adjacency.get(&node).map_or(&[], |v| v.as_slice())
    }

    pub fn degree(&self, node: NodeId) -> usize {
        self.adjacency.get(&node).map_or(0, |v| v.len())
    }

    pub fn num_edges(&self) -> u32 {
        self.edges.len() as u32
    }
}
