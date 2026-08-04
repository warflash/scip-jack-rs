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
    out_adjacency: Vec<Vec<(NodeId, ArcId)>>,
    /// Incoming arcs: node -> [(tail, arc_id)]
    in_adjacency: Vec<Vec<(NodeId, ArcId)>>,
}

impl DirectedGraph {
    pub fn new(num_nodes: u32) -> Self {
        Self {
            num_nodes,
            nodes: Vec::with_capacity(num_nodes as usize),
            arcs: Vec::new(),
            out_adjacency: vec![Vec::new(); num_nodes as usize + 1],
            in_adjacency: vec![Vec::new(); num_nodes as usize + 1],
        }
    }

    #[inline]
    fn ensure_node(&mut self, id: NodeId) {
        let required = id as usize + 1;
        if self.out_adjacency.len() < required {
            self.out_adjacency.resize_with(required, Vec::new);
            self.in_adjacency.resize_with(required, Vec::new);
        }
    }

    pub fn add_node(&mut self, id: NodeId, node_type: NodeType, weight: Cost) {
        self.ensure_node(id);
        self.nodes.push(Node { id, node_type, weight });
    }

    pub fn add_arc(&mut self, tail: NodeId, head: NodeId, cost: Cost) -> ArcId {
        self.ensure_node(tail);
        self.ensure_node(head);
        let arc_id = self.arcs.len() as ArcId;
        self.arcs.push(Arc { id: arc_id, tail, head, cost });
        self.out_adjacency[tail as usize].push((head, arc_id));
        self.in_adjacency[head as usize].push((tail, arc_id));
        arc_id
    }

    /// δ+(v): outgoing arcs from node v
    #[inline]
    pub fn delta_plus(&self, node: NodeId) -> &[(NodeId, ArcId)] {
        self.out_adjacency.get(node as usize).map_or(&[], Vec::as_slice)
    }

    /// δ⁻(v): incoming arcs to node v
    #[inline]
    pub fn delta_minus(&self, node: NodeId) -> &[(NodeId, ArcId)] {
        self.in_adjacency.get(node as usize).map_or(&[], Vec::as_slice)
    }

    /// δ+(W): arcs with tail in W and head in V \ W
    pub fn delta_plus_set(&self, w: &[NodeId]) -> Vec<ArcId> {
        let mut in_set = vec![false; self.out_adjacency.len()];
        for &node in w {
            if let Some(slot) = in_set.get_mut(node as usize) {
                *slot = true;
            }
        }
        let mut result = Vec::new();
        for &node in w {
            for &(head, arc_id) in self.delta_plus(node) {
                if !in_set.get(head as usize).copied().unwrap_or(false) {
                    result.push(arc_id);
                }
            }
        }
        result
    }

    pub fn out_degree(&self, node: NodeId) -> usize {
        self.out_adjacency.get(node as usize).map_or(0, Vec::len)
    }

    pub fn in_degree(&self, node: NodeId) -> usize {
        self.in_adjacency.get(node as usize).map_or(0, Vec::len)
    }

    pub fn num_arcs(&self) -> u32 {
        self.arcs.len() as u32
    }

    /// Create a directed graph from an undirected graph by replacing each edge
    /// with two anti-parallel arcs (the fundamental STP → SAP transformation).
    pub fn from_undirected(graph: &super::UndirectedGraph) -> Self {
        let mut dg = Self::new(graph.num_nodes);
        dg.arcs.reserve(graph.edges.len().saturating_mul(2));

        for node in &graph.nodes {
            dg.add_node(node.id, node.node_type, node.weight);
            let degree = graph.neighbors(node.id).len();
            dg.out_adjacency[node.id as usize].reserve(degree);
            dg.in_adjacency[node.id as usize].reserve(degree);
        }

        for edge in &graph.edges {
            dg.add_arc(edge.src, edge.dst, edge.cost);
            dg.add_arc(edge.dst, edge.src, edge.cost);
        }

        dg
    }
}
