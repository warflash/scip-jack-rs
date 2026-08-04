//! Compact adjacency snapshot of the live part of a [`ReducibleGraph`].
//!
//! `ReducibleGraph::shortest_paths_from` allocates a `Vec` per settled vertex,
//! which is far too slow to run once per terminal — let alone once per candidate
//! vertex — on the larger instances. Every reduction test in this module runs
//! Dijkstra over the same snapshot instead.
//!
//! Vertices can be *masked out* after the snapshot is taken. That is what makes
//! the vertex-deletion test sound: each candidate is judged against a graph from
//! which the previously deleted candidates are already absent, so the deletions
//! compose instead of each being justified against a graph that no longer exists.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::graph::{cmp_cost, Cost, EdgeId, NodeId};

use super::ReducibleGraph;

pub struct Csr {
    pub num_nodes: usize,
    start: Vec<u32>,
    head: Vec<u32>,
    cost: Vec<Cost>,
    edge: Vec<EdgeId>,
    /// Vertices excluded from every traversal.
    masked: Vec<bool>,
}

/// Reusable Dijkstra scratch space. Reallocating `dist` per candidate vertex
/// dominates the vertex test on large instances, so the caller keeps one of
/// these and the algorithm only resets the entries it actually touched.
pub struct DijkstraWorkspace {
    pub dist: Vec<Cost>,
    /// First edge on the path from the source, or `u32::MAX`.
    pub first: Vec<EdgeId>,
    /// Source index that settled the vertex, or `u32::MAX`.
    pub base: Vec<u32>,
    touched: Vec<u32>,
    heap: BinaryHeap<(Reverse<Ordered>, u32)>,
}

impl DijkstraWorkspace {
    pub fn new(num_nodes: usize) -> Self {
        Self {
            dist: vec![Cost::INFINITY; num_nodes],
            first: vec![u32::MAX; num_nodes],
            base: vec![u32::MAX; num_nodes],
            touched: Vec::new(),
            heap: BinaryHeap::new(),
        }
    }

    fn reset(&mut self) {
        for &v in &self.touched {
            self.dist[v as usize] = Cost::INFINITY;
            self.first[v as usize] = u32::MAX;
            self.base[v as usize] = u32::MAX;
        }
        self.touched.clear();
        self.heap.clear();
    }
}

impl Csr {
    pub fn build(graph: &ReducibleGraph) -> Self {
        let num_nodes = graph.nodes.iter().map(|n| n.id as usize).max().unwrap_or(0) + 1;
        let mut degree = vec![0u32; num_nodes + 1];
        for e in &graph.edges {
            if graph.is_edge_valid(e.id) && graph.is_node_valid(e.src) && graph.is_node_valid(e.dst) {
                degree[e.src as usize + 1] += 1;
                degree[e.dst as usize + 1] += 1;
            }
        }
        for i in 0..num_nodes {
            degree[i + 1] += degree[i];
        }
        let start = degree.clone();
        let mut fill = start.clone();
        let incidence = degree[num_nodes] as usize;
        let mut head = vec![0u32; incidence];
        let mut cost = vec![0.0; incidence];
        let mut edge = vec![0u32; incidence];
        for e in &graph.edges {
            if !graph.is_edge_valid(e.id) || !graph.is_node_valid(e.src) || !graph.is_node_valid(e.dst) {
                continue;
            }
            let ia = fill[e.src as usize] as usize;
            head[ia] = e.dst;
            cost[ia] = e.cost;
            edge[ia] = e.id;
            fill[e.src as usize] += 1;
            let ib = fill[e.dst as usize] as usize;
            head[ib] = e.src;
            cost[ib] = e.cost;
            edge[ib] = e.id;
            fill[e.dst as usize] += 1;
        }
        let masked = vec![false; num_nodes];
        Self { num_nodes, start, head, cost, edge, masked }
    }

    pub fn mask(&mut self, v: NodeId) {
        self.masked[v as usize] = true;
    }

    pub fn unmask(&mut self, v: NodeId) {
        self.masked[v as usize] = false;
    }

    pub fn is_masked(&self, v: NodeId) -> bool {
        self.masked[v as usize]
    }

    pub fn neighbors(&self, v: NodeId) -> impl Iterator<Item = (NodeId, Cost, EdgeId)> + '_ {
        let (s, e) = (self.start[v as usize] as usize, self.start[v as usize + 1] as usize);
        (s..e).map(move |i| (self.head[i], self.cost[i], self.edge[i]))
    }

    pub fn degree(&self, v: NodeId) -> usize {
        self.neighbors(v).filter(|&(u, _, _)| !self.masked[u as usize]).count()
    }

    /// Plain single-source Dijkstra returning a fresh distance vector.
    pub fn dijkstra(&self, source: NodeId) -> Vec<Cost> {
        let mut ws = DijkstraWorkspace::new(self.num_nodes);
        self.dijkstra_into(&[source], Cost::INFINITY, &mut ws);
        std::mem::replace(&mut ws.dist, Vec::new())
    }

    /// Multi-source Dijkstra bounded by `radius`, writing into `ws`.
    ///
    /// Vertices beyond `radius` keep `Cost::INFINITY`. Every reduction test here
    /// treats an unreachable vertex as offering no shortcut, so truncating the
    /// search can only weaken a test, never invalidate one.
    ///
    /// `ws.base[v]` is the index into `sources` of the source that settled `v`
    /// and `ws.first[v]` is the first edge of that path.
    pub fn dijkstra_into(&self, sources: &[NodeId], radius: Cost, ws: &mut DijkstraWorkspace) {
        ws.reset();
        for (i, &s) in sources.iter().enumerate() {
            if self.masked[s as usize] || ws.dist[s as usize] == 0.0 {
                continue;
            }
            ws.dist[s as usize] = 0.0;
            ws.base[s as usize] = i as u32;
            ws.touched.push(s);
            ws.heap.push((Reverse(Ordered(0.0)), s));
        }

        while let Some((Reverse(Ordered(d)), v)) = ws.heap.pop() {
            if d > ws.dist[v as usize] + 1e-12 {
                continue;
            }
            let (s, e) = (self.start[v as usize] as usize, self.start[v as usize + 1] as usize);
            for i in s..e {
                let u = self.head[i];
                if self.masked[u as usize] {
                    continue;
                }
                let nd = d + self.cost[i];
                if nd > radius + 1e-9 || nd >= ws.dist[u as usize] - 1e-12 {
                    continue;
                }
                if ws.dist[u as usize] == Cost::INFINITY {
                    ws.touched.push(u);
                }
                ws.dist[u as usize] = nd;
                ws.base[u as usize] = ws.base[v as usize];
                // `first[v] == MAX` marks `v` as a source, so `u` is the first
                // hop off it. Testing the distance instead would misfire on
                // zero-cost edges.
                ws.first[u as usize] = if ws.first[v as usize] == u32::MAX {
                    self.edge[i]
                } else {
                    ws.first[v as usize]
                };
                ws.heap.push((Reverse(Ordered(nd)), u));
            }
        }
    }
}

#[derive(PartialEq)]
pub struct Ordered(pub Cost);
impl Eq for Ordered {}
impl Ord for Ordered {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        cmp_cost(self.0, other.0)
    }
}
impl PartialOrd for Ordered {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
