use std::collections::VecDeque;
use crate::graph::{cmp_cost, DirectedGraph, NodeId, ArcId};

/// Terminal-Free (TF) set cut separator (Section 11.3 of research memo).
///
/// For a terminal-free set S and edge e in E(S):
///   x(δ(S)) >= 2 * x_e
///
/// Validity: In any inclusion-minimal Steiner tree, a terminal-free connected
/// component must have at least 2 boundary edges. Otherwise it would be a
/// dead-end branch that could be pruned without disconnecting terminals.
///
/// Separation oracle: For each non-terminal edge e={u,v} with x_e > ε,
/// compute min s-t cut from {u,v} (merged) to the terminal set using
/// undirected capacities x_e. If min-cut < 2*x_e, the source side gives
/// a violated inequality.

pub struct TfCut {
    pub set_nodes: Vec<NodeId>,
    pub boundary_arcs: Vec<(ArcId, ArcId)>,
    pub edge_arc_pair: (ArcId, ArcId),
    pub violation: f64,
}

pub struct TfCutSeparator<'a> {
    graph: &'a DirectedGraph,
    terminals: &'a [NodeId],
    pub cuts_found: u32,
    pub violation_tolerance: f64,
    terminal_flags: Vec<u8>,
    x: Vec<f64>,
    candidates: Vec<(usize, f64)>,
    residual_adj: Vec<Vec<(usize, usize)>>,
    residual_cap: Vec<f64>,
    parent: Vec<Option<(usize, usize)>>,
    visited: Vec<bool>,
    reachable: Vec<bool>,
    queue: VecDeque<usize>,
}

impl<'a> TfCutSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph, terminals: &'a [NodeId]) -> Self {
        let max_node = graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let total_nodes = max_node + 3;
        let num_edges = graph.arcs.len() / 2;
        let mut terminal_flags = vec![0u8; max_node + 1];
        for &t in terminals {
            terminal_flags[t as usize] = 1;
        }
        Self {
            graph,
            terminals,
            cuts_found: 0,
            violation_tolerance: 1e-4,
            terminal_flags,
            x: Vec::with_capacity(num_edges),
            candidates: Vec::new(),
            residual_adj: vec![Vec::new(); total_nodes],
            residual_cap: Vec::with_capacity(graph.arcs.len() + terminals.len() * 2 + 4),
            parent: vec![None; total_nodes],
            visited: vec![false; total_nodes],
            reachable: vec![false; total_nodes],
            queue: VecDeque::with_capacity(total_nodes),
        }
    }

    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<TfCut> {
        let num_arcs = self.graph.arcs.len();
        let num_edges = num_arcs / 2;

        self.x.resize(num_edges, 0.0);
        for i in 0..num_edges {
            let fwd = lp_solution[2 * i];
            let rev = lp_solution[2 * i + 1];
            self.x[i] = fwd + rev;
        }

        let max_node = self.graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;

        let mut violated_cuts = Vec::new();

        // Collect candidate edges sorted by x_e descending (most fractional first).
        // Only check top candidates to avoid O(|E|) max-flow computations on dense graphs.
        self.candidates.clear();
        self.candidates.extend((0..num_edges)
            .filter(|&i| self.x[i] >= 0.1)
            .filter(|&i| {
                let arc = &self.graph.arcs[2 * i];
                self.terminal_flags[arc.tail as usize] == 0
                    && self.terminal_flags[arc.head as usize] == 0
            })
            .map(|i| (i, self.x[i])));
        self.candidates.sort_by(|a, b| cmp_cost(b.1, a.1));
        self.candidates.truncate(50);

        for i in 0..self.candidates.len() {
            let (edge_idx, x_val) = self.candidates[i];
            let arc = &self.graph.arcs[2 * edge_idx];
            let u = arc.tail;
            let v = arc.head;
            let threshold = 2.0 * x_val;

            if let Some(cut) = self.find_min_cut_to_terminals(u, v, edge_idx, max_node, threshold) {
                violated_cuts.push(cut);
            }
        }

        self.cuts_found += violated_cuts.len() as u32;
        violated_cuts
    }

    /// Find min-cut from merged {u,v} to terminal set.
    /// Returns a TfCut if the min-cut value < threshold.
    fn find_min_cut_to_terminals(
        &mut self,
        u: NodeId,
        v: NodeId,
        edge_idx: usize,
        max_node: usize,
        threshold: f64,
    ) -> Option<TfCut> {
        let num_edges = self.x.len();

        // Max-flow from super-source (representing merged {u,v}) to super-sink (terminals).
        // We use BFS-based augmenting paths on the undirected capacities.
        // Node IDs: 0..max_node are graph nodes, max_node+1 = super-source, max_node+2 = super-sink
        let source = max_node + 1;
        let sink = max_node + 2;
        // Residual capacities stored per edge direction.
        // For undirected edge i between a and b: capacity x[i] in both directions.
        // Plus source->u, source->v (infinite), and terminal->sink (infinite).
        let inf_cap = 1e10;

        // Build residual graph as adjacency list with (neighbor, capacity_ref_index, is_reverse)
        // Use edge-indexed residual: residual[edge_idx * 2] = fwd, residual[edge_idx * 2 + 1] = rev
        // Plus extra edges for source/sink connections.

        // Simpler approach: sparse residual with Vec<(neighbor, residual_cap, rev_edge_idx)>
        for adj in &mut self.residual_adj {
            adj.clear();
        }
        self.residual_cap.clear();

        // Add graph edges (undirected = two directed)
        for i in 0..num_edges {
            if self.x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            let a = arc.tail as usize;
            let b = arc.head as usize;

            let fwd_idx = self.residual_cap.len();
            self.residual_cap.push(self.x[i]);
            let rev_idx = self.residual_cap.len();
            self.residual_cap.push(self.x[i]);

            self.residual_adj[a].push((b, fwd_idx));
            self.residual_adj[b].push((a, rev_idx));
        }

        // Source -> u, Source -> v (infinite capacity)
        for &node in &[u, v] {
            let fwd_idx = self.residual_cap.len();
            self.residual_cap.push(inf_cap);
            let rev_idx = self.residual_cap.len();
            self.residual_cap.push(0.0);
            self.residual_adj[source].push((node as usize, fwd_idx));
            self.residual_adj[node as usize].push((source, rev_idx));
        }

        // Terminal -> sink (infinite capacity)
        for &t in self.terminals {
            let fwd_idx = self.residual_cap.len();
            self.residual_cap.push(inf_cap);
            let rev_idx = self.residual_cap.len();
            self.residual_cap.push(0.0);
            self.residual_adj[t as usize].push((sink, fwd_idx));
            self.residual_adj[sink].push((t as usize, rev_idx));
        }

        // Build reverse edge mapping: for each edge at index i, its reverse is i^1
        // (since we add them in pairs: fwd then rev)

        // Edmonds-Karp (BFS augmenting paths)
        let mut total_flow = 0.0;
        loop {
            // Early termination if flow already >= threshold
            if total_flow >= threshold - self.violation_tolerance {
                return None;
            }

            // BFS to find augmenting path
            self.parent.fill(None); // (from_node, edge_idx)
            self.visited.fill(false);
            self.queue.clear();
            self.queue.push_back(source);
            self.visited[source] = true;

            let mut found_sink = false;
            while let Some(node) = self.queue.pop_front() {
                if node == sink {
                    found_sink = true;
                    break;
                }
                for &(neighbor, edge_idx) in &self.residual_adj[node] {
                    if !self.visited[neighbor] && self.residual_cap[edge_idx] > 1e-10 {
                        self.visited[neighbor] = true;
                        self.parent[neighbor] = Some((node, edge_idx));
                        self.queue.push_back(neighbor);
                    }
                }
            }

            if !found_sink { break; }

            // Find bottleneck
            let mut bottleneck = f64::INFINITY;
            let mut node = sink;
            while let Some((prev, edge_idx)) = self.parent[node] {
                bottleneck = bottleneck.min(self.residual_cap[edge_idx]);
                node = prev;
            }

            // Update residuals
            let mut node = sink;
            while let Some((prev, edge_idx)) = self.parent[node] {
                self.residual_cap[edge_idx] -= bottleneck;
                self.residual_cap[edge_idx ^ 1] += bottleneck;
                node = prev;
            }

            total_flow += bottleneck;
        }

        // Check violation
        let violation = threshold - total_flow;
        if violation < self.violation_tolerance {
            return None;
        }

        // Extract min-cut: source-reachable set in residual graph
        self.reachable.fill(false);
        self.queue.clear();
        self.queue.push_back(source);
        self.reachable[source] = true;
        while let Some(node) = self.queue.pop_front() {
            for &(neighbor, edge_idx) in &self.residual_adj[node] {
                if !self.reachable[neighbor] && self.residual_cap[edge_idx] > 1e-10 {
                    self.reachable[neighbor] = true;
                    self.queue.push_back(neighbor);
                }
            }
        }

        // Set S = reachable graph nodes (excluding source/sink pseudo-nodes)
        let set_nodes: Vec<NodeId> = (0..=max_node)
            .filter(|&n| self.reachable[n])
            .map(|n| n as NodeId)
            .collect();

        // Boundary edges: edges with one endpoint in S, one outside
        let mut boundary_arcs: Vec<(ArcId, ArcId)> = Vec::new();
        for i in 0..num_edges {
            let arc = &self.graph.arcs[2 * i];
            let a_in = self.reachable[arc.tail as usize];
            let b_in = self.reachable[arc.head as usize];
            if a_in != b_in {
                boundary_arcs.push(((2 * i) as ArcId, (2 * i + 1) as ArcId));
            }
        }

        Some(TfCut {
            set_nodes,
            boundary_arcs,
            edge_arc_pair: ((2 * edge_idx) as ArcId, (2 * edge_idx + 1) as ArcId),
            violation,
        })
    }
}
