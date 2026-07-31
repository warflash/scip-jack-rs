pub mod degree;
pub mod distance;
pub mod bottleneck;
pub mod implications;

use std::collections::{HashMap, HashSet, BinaryHeap};
use std::cmp::Ordering;
use crate::graph::{UndirectedGraph, NodeId, EdgeId, Cost, NodeType, Node, Edge, SteinerInstance};

/// A graph wrapper that supports efficient node/edge removal for preprocessing.
/// Uses validity flags to mark removed elements without rebuilding the structure.
#[derive(Debug, Clone)]
pub struct ReducibleGraph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub adjacency: HashMap<NodeId, Vec<(NodeId, EdgeId)>>,
    pub terminals: HashSet<NodeId>,
    pub root: Option<NodeId>,
    node_valid: Vec<bool>,
    edge_valid: Vec<bool>,
    /// Edges created by degree-2 contraction (should not be subject to SD test)
    pub contracted_edges: HashSet<EdgeId>,
    /// Nodes that have been contracted (degree-2 removal targets)
    pub contracted_nodes: HashSet<NodeId>,
}

impl ReducibleGraph {
    pub fn from_instance(instance: &SteinerInstance, graph: &UndirectedGraph) -> Self {
        let n = graph.num_nodes as usize;
        let m = graph.edges.len();

        let terminal_set: HashSet<NodeId> = instance.terminals.iter().copied().collect();
        let mut adjacency: HashMap<NodeId, Vec<(NodeId, EdgeId)>> = HashMap::new();

        for edge in &graph.edges {
            adjacency.entry(edge.src).or_default().push((edge.dst, edge.id));
            adjacency.entry(edge.dst).or_default().push((edge.src, edge.id));
        }

        for node in &graph.nodes {
            adjacency.entry(node.id).or_default();
        }

        Self {
            nodes: graph.nodes.clone(),
            edges: graph.edges.clone(),
            adjacency,
            terminals: terminal_set,
            root: instance.root,
            node_valid: vec![true; n + 1],
            edge_valid: vec![true; m],
            contracted_edges: HashSet::new(),
            contracted_nodes: HashSet::new(),
        }
    }

    pub fn is_node_valid(&self, node: NodeId) -> bool {
        (node as usize) < self.node_valid.len() && self.node_valid[node as usize]
    }

    pub fn is_edge_valid(&self, edge: EdgeId) -> bool {
        (edge as usize) < self.edge_valid.len() && self.edge_valid[edge as usize]
    }

    pub fn degree(&self, node: NodeId) -> usize {
        self.adjacency.get(&node).map_or(0, |neighbors| {
            neighbors.iter().filter(|&&(_, eid)| self.is_edge_valid(eid)).count()
        })
    }

    pub fn valid_neighbors(&self, node: NodeId) -> Vec<(NodeId, EdgeId)> {
        self.adjacency.get(&node).map_or(Vec::new(), |neighbors| {
            neighbors.iter()
                .filter(|&&(n, eid)| self.is_node_valid(n) && self.is_edge_valid(eid))
                .copied()
                .collect()
        })
    }

    pub fn is_terminal(&self, node: NodeId) -> bool {
        self.terminals.contains(&node)
    }

    /// Remove a node and all its incident edges.
    pub fn remove_node(&mut self, node: NodeId) {
        if (node as usize) < self.node_valid.len() {
            self.node_valid[node as usize] = false;
        }
        // Invalidate all incident edges
        if let Some(neighbors) = self.adjacency.get(&node).cloned() {
            for &(_, eid) in &neighbors {
                if (eid as usize) < self.edge_valid.len() {
                    self.edge_valid[eid as usize] = false;
                }
            }
        }
    }

    /// Remove an edge (keep nodes).
    pub fn remove_edge(&mut self, edge_id: EdgeId) {
        if (edge_id as usize) < self.edge_valid.len() {
            self.edge_valid[edge_id as usize] = false;
        }
    }

    /// Contract a degree-2 Steiner node: replace v with direct edge between its two neighbors.
    /// Returns the cost of the new edge (if contraction happened), and the edges that were removed.
    pub fn contract_degree2(&mut self, node: NodeId) -> Option<(EdgeId, Cost)> {
        let neighbors = self.valid_neighbors(node);
        if neighbors.len() != 2 {
            return None;
        }
        if self.is_terminal(node) {
            return None;
        }

        let (n1, e1) = neighbors[0];
        let (n2, e2) = neighbors[1];
        let cost1 = self.edges[e1 as usize].cost;
        let cost2 = self.edges[e2 as usize].cost;
        let new_cost = cost1 + cost2;

        self.remove_edge(e1);
        self.remove_edge(e2);
        self.node_valid[node as usize] = false;
        self.contracted_nodes.insert(node);

        let new_eid = self.edges.len() as EdgeId;
        self.edges.push(Edge { id: new_eid, src: n1, dst: n2, cost: new_cost });
        self.edge_valid.push(true);
        self.contracted_edges.insert(new_eid);
        self.adjacency.entry(n1).or_default().push((n2, new_eid));
        self.adjacency.entry(n2).or_default().push((n1, new_eid));

        Some((new_eid, new_cost))
    }

    /// Compute shortest paths from source to all nodes (Dijkstra on the reduced graph).
    pub fn shortest_paths_from(&self, source: NodeId) -> Vec<Cost> {
        let n = self.nodes.len() + 1;
        let mut dist = vec![f64::INFINITY; n];
        let mut heap = BinaryHeap::new();

        dist[source as usize] = 0.0;
        heap.push(DijkEntry { cost: 0.0, node: source });

        while let Some(DijkEntry { cost, node }) = heap.pop() {
            if cost > dist[node as usize] {
                continue;
            }
            for (neighbor, eid) in self.valid_neighbors(node) {
                let edge_cost = self.edges[eid as usize].cost;
                let new_cost = cost + edge_cost;
                if new_cost < dist[neighbor as usize] {
                    dist[neighbor as usize] = new_cost;
                    heap.push(DijkEntry { cost: new_cost, node: neighbor });
                }
            }
        }

        dist
    }

    /// Get all valid node IDs.
    pub fn valid_nodes(&self) -> Vec<NodeId> {
        self.nodes.iter()
            .filter(|n| self.is_node_valid(n.id))
            .map(|n| n.id)
            .collect()
    }

    /// Get all valid edge IDs.
    pub fn valid_edges(&self) -> Vec<EdgeId> {
        self.edges.iter()
            .filter(|e| self.is_edge_valid(e.id))
            .map(|e| e.id)
            .collect()
    }

    /// Build a new UndirectedGraph and SteinerInstance from the reduced state.
    pub fn to_instance(&self) -> (SteinerInstance, UndirectedGraph) {
        let valid_nodes = self.valid_nodes();
        let valid_edges = self.valid_edges();

        // Create node ID remapping
        let mut node_map: HashMap<NodeId, NodeId> = HashMap::new();
        let mut new_id = 1u32;
        for &nid in &valid_nodes {
            node_map.insert(nid, new_id);
            new_id += 1;
        }

        let num_nodes = valid_nodes.len() as u32;
        let mut graph = UndirectedGraph::new(num_nodes);

        for &nid in &valid_nodes {
            let new_nid = node_map[&nid];
            let nt = if self.terminals.contains(&nid) { NodeType::Terminal } else { NodeType::Steiner };
            let weight = self.nodes.iter().find(|n| n.id == nid).map_or(0.0, |n| n.weight);
            graph.add_node(new_nid, nt, weight);
        }

        for &eid in &valid_edges {
            let edge = &self.edges[eid as usize];
            if let (Some(&new_src), Some(&new_dst)) = (node_map.get(&edge.src), node_map.get(&edge.dst)) {
                graph.add_edge(new_src, new_dst, edge.cost);
            }
        }

        let mut terminals: Vec<NodeId> = self.terminals.iter()
            .filter(|&&t| node_map.contains_key(&t))
            .map(|&t| node_map[&t])
            .collect();
        terminals.sort();

        let root = self.root.and_then(|r| node_map.get(&r).copied());

        let instance = SteinerInstance {
            name: String::from("reduced"),
            comment: String::new(),
            num_nodes,
            num_edges: valid_edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: graph.nodes.clone(),
            edges: graph.edges.clone(),
            terminals,
            root,
        };

        (instance, graph)
    }

    /// Count valid nodes.
    pub fn num_valid_nodes(&self) -> u32 {
        self.nodes.iter().filter(|n| self.is_node_valid(n.id)).count() as u32
    }

    /// Count valid edges.
    pub fn num_valid_edges(&self) -> u32 {
        self.edges.iter().filter(|e| self.is_edge_valid(e.id)).count() as u32
    }
}

#[derive(Clone, PartialEq)]
struct DijkEntry {
    cost: Cost,
    node: NodeId,
}

impl Eq for DijkEntry {}

impl Ord for DijkEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.partial_cmp(&self.cost)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for DijkEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Result of preprocessing: statistics about what was removed/fixed.
pub struct PreprocessingResult {
    pub nodes_removed: u32,
    pub edges_removed: u32,
    pub edges_fixed: Vec<EdgeId>,
    pub lower_bound_offset: Cost,
}

/// Apply all reduction techniques in a sound order:
///
/// 1. Iterative: degree reductions + SD test + implications
///    The SD test uses contraction-aware guards to avoid removing edges
///    whose shortest paths are distorted by degree-2 contractions.
///
/// The SD test only applies to edges whose BOTH endpoints are NOT adjacent
/// to any contracted node, ensuring it operates on undistorted distances.
pub fn preprocess(instance: &SteinerInstance, graph: &UndirectedGraph) -> (ReducibleGraph, PreprocessingResult) {
    let mut rg = ReducibleGraph::from_instance(instance, graph);

    let initial_nodes = rg.num_valid_nodes();
    let initial_edges = rg.num_valid_edges();
    let mut total_fixed: Vec<EdgeId> = Vec::new();
    let mut lb_offset = 0.0;

    let mut iteration = 0u32;

    loop {
        let (deg_removed, fixed, offset) = degree::degree_reductions(&mut rg);
        total_fixed.extend(fixed);
        lb_offset += offset;

        // SD test: only on the first iteration (clean graph) or if no
        // contractions occurred (safe to re-run).
        let dist_removed = if iteration == 0 || rg.contracted_edges.is_empty() {
            distance::distance_reductions(&mut rg)
        } else {
            0
        };

        // Implication reductions: triangle dominance + conflict propagation.
        // Only run when graph has settled (no degree reductions or SD removals
        // in this iteration), as implications depend on current graph structure.
        let impl_removed = if deg_removed == 0 && dist_removed == 0 {
            implications::implication_reductions(&mut rg)
        } else {
            0
        };

        if deg_removed + dist_removed + impl_removed == 0 {
            break;
        }
        iteration += 1;
    }

    let result = PreprocessingResult {
        nodes_removed: initial_nodes - rg.num_valid_nodes(),
        edges_removed: initial_edges - rg.num_valid_edges(),
        edges_fixed: total_fixed,
        lower_bound_offset: lb_offset,
    };

    (rg, result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_degree1_instance() -> (SteinerInstance, UndirectedGraph) {
        // Node 4 is a degree-1 Steiner node — should be removed
        // 1(T) -- 2(S) -- 3(T)
        //          |
        //         4(S)
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(2, 4, 5.0); // 2

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 4,
            num_edges: 3,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 3],
            root: Some(1),
        };

        (instance, g)
    }

    #[test]
    fn test_degree1_steiner_removed() {
        let (instance, graph) = build_degree1_instance();
        let (rg, result) = preprocess(&instance, &graph);

        assert!(result.nodes_removed >= 1, "Should remove degree-1 Steiner node");
        assert!(!rg.is_node_valid(4), "Node 4 should be removed");
        assert!(rg.is_node_valid(1), "Terminal 1 should remain");
        assert!(rg.is_node_valid(3), "Terminal 3 should remain");
    }

    #[test]
    fn test_degree2_contraction() {
        // 1(T) -- 2(S) -- 3(T): node 2 has degree 2, should be contracted
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 2.0);
        g.add_edge(2, 3, 3.0);

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 3,
            num_edges: 2,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 3],
            root: Some(1),
        };

        let (rg, result) = preprocess(&instance, &g);

        assert!(!rg.is_node_valid(2), "Degree-2 Steiner node should be contracted");
        assert!(result.nodes_removed >= 1);
    }

    #[test]
    fn test_terminals_never_removed() {
        let (instance, graph) = build_degree1_instance();
        let (rg, _) = preprocess(&instance, &graph);

        for &t in &instance.terminals {
            assert!(rg.is_node_valid(t), "Terminal {} was incorrectly removed", t);
        }
    }

    #[test]
    fn test_expensive_edge_removed_by_distance() {
        // 1(T) --1-- 2(T) --1-- 3(T)
        //   \                  /
        //    -------- 100 ----
        // Edge 1-3 with cost 100 should be removed since d(1,3) via 2 = 2 < 100
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(1, 3, 100.0); // 2

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 3,
            num_edges: 3,
            num_terminals: 3,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2, 3],
            root: Some(1),
        };

        let (rg, result) = preprocess(&instance, &g);

        assert!(!rg.is_edge_valid(2), "Expensive edge 1-3 should be removed");
        assert!(result.edges_removed >= 1);
    }
}
