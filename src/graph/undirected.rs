use super::types::*;

/// Undirected graph using adjacency list representation.
/// Stores edges as pairs and maintains adjacency information for efficient traversal.
#[derive(Debug, Clone)]
pub struct UndirectedGraph {
    pub num_nodes: u32,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    /// Adjacency indexed directly by the one-based node id.
    pub adjacency: Vec<Vec<(NodeId, EdgeId)>>,
    /// Edge costs in the same incidence order as `adjacency`.
    ///
    /// Dijkstra-style passes usually need the neighboring vertex and cost but
    /// not the edge id. Keeping this compact parallel cache avoids a second
    /// pointer chase through `edges` in those inner loops.
    adjacency_costs: Vec<Vec<Cost>>,
}

impl UndirectedGraph {
    pub fn new(num_nodes: u32) -> Self {
        Self {
            num_nodes,
            nodes: Vec::with_capacity(num_nodes as usize),
            edges: Vec::new(),
            adjacency: vec![Vec::new(); num_nodes as usize + 1],
            adjacency_costs: vec![Vec::new(); num_nodes as usize + 1],
        }
    }

    #[inline]
    fn ensure_node(&mut self, id: NodeId) {
        let required = id as usize + 1;
        if self.adjacency.len() < required {
            self.adjacency.resize_with(required, Vec::new);
            self.adjacency_costs.resize_with(required, Vec::new);
        }
    }

    pub fn add_node(&mut self, id: NodeId, node_type: NodeType, weight: Cost) {
        self.ensure_node(id);
        self.nodes.push(Node { id, node_type, weight });
    }

    pub fn add_edge(&mut self, src: NodeId, dst: NodeId, cost: Cost) -> EdgeId {
        self.ensure_node(src);
        self.ensure_node(dst);
        let edge_id = self.edges.len() as EdgeId;
        self.edges.push(Edge { id: edge_id, src, dst, cost });
        self.adjacency[src as usize].push((dst, edge_id));
        self.adjacency[dst as usize].push((src, edge_id));
        self.adjacency_costs[src as usize].push(cost);
        self.adjacency_costs[dst as usize].push(cost);
        edge_id
    }

    #[inline]
    pub fn neighbors(&self, node: NodeId) -> &[(NodeId, EdgeId)] {
        self.adjacency.get(node as usize).map_or(&[], Vec::as_slice)
    }

    /// Neighbor and cost pairs for shortest-path relaxations.
    #[inline]
    pub fn neighbors_with_cost(&self, node: NodeId) -> impl Iterator<Item = (NodeId, Cost)> + '_ {
        let neighbors = self.adjacency.get(node as usize).map_or(&[][..], Vec::as_slice);
        let costs = self.adjacency_costs.get(node as usize).map_or(&[][..], Vec::as_slice);
        neighbors
            .iter()
            .zip(costs.iter())
            .map(|(&(neighbor, _), &cost)| (neighbor, cost))
    }

    #[inline]
    pub fn degree(&self, node: NodeId) -> usize {
        self.adjacency.get(node as usize).map_or(0, Vec::len)
    }

    pub fn num_edges(&self) -> u32 {
        self.edges.len() as u32
    }
}
