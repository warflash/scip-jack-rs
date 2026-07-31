use std::collections::{HashSet, VecDeque};
use crate::graph::{DirectedGraph, NodeId, ArcId};

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
}

impl<'a> TfCutSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph, terminals: &'a [NodeId]) -> Self {
        Self {
            graph,
            terminals,
            cuts_found: 0,
            violation_tolerance: 1e-4,
        }
    }

    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<TfCut> {
        let num_arcs = self.graph.arcs.len();
        let num_edges = num_arcs / 2;
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();

        let mut x: Vec<f64> = vec![0.0; num_edges];
        for i in 0..num_edges {
            let fwd = lp_solution.get(2 * i).copied().unwrap_or(0.0);
            let rev = lp_solution.get(2 * i + 1).copied().unwrap_or(0.0);
            x[i] = fwd + rev;
        }

        let max_node = self.graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;

        // Build undirected adjacency: node -> [(neighbor, edge_idx)]
        let mut adj: Vec<Vec<(NodeId, usize)>> = vec![Vec::new(); max_node + 1];
        for i in 0..num_edges {
            if x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            adj[arc.tail as usize].push((arc.head, i));
            adj[arc.head as usize].push((arc.tail, i));
        }

        let mut violated_cuts = Vec::new();

        // Collect candidate edges sorted by x_e descending (most fractional first).
        // Only check top candidates to avoid O(|E|) max-flow computations on dense graphs.
        let mut candidates: Vec<(usize, f64)> = (0..num_edges)
            .filter(|&i| x[i] >= 0.1)
            .filter(|&i| {
                let arc = &self.graph.arcs[2 * i];
                !terminal_set.contains(&arc.tail) && !terminal_set.contains(&arc.head)
            })
            .map(|i| (i, x[i]))
            .collect();
        candidates.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        candidates.truncate(50);

        for (edge_idx, x_val) in candidates {
            let arc = &self.graph.arcs[2 * edge_idx];
            let u = arc.tail;
            let v = arc.head;
            let threshold = 2.0 * x_val;

            if let Some(cut) = self.find_min_cut_to_terminals(
                u, v, edge_idx, &x, &adj, &terminal_set, max_node, threshold,
            ) {
                violated_cuts.push(cut);
            }
        }

        self.cuts_found += violated_cuts.len() as u32;
        violated_cuts
    }

    /// Find min-cut from merged {u,v} to terminal set.
    /// Returns a TfCut if the min-cut value < threshold.
    fn find_min_cut_to_terminals(
        &self,
        u: NodeId,
        v: NodeId,
        edge_idx: usize,
        x: &[f64],
        _adj: &[Vec<(NodeId, usize)>],
        _terminal_set: &HashSet<NodeId>,
        max_node: usize,
        threshold: f64,
    ) -> Option<TfCut> {
        let num_edges = x.len();

        // Max-flow from super-source (representing merged {u,v}) to super-sink (terminals).
        // We use BFS-based augmenting paths on the undirected capacities.
        // Node IDs: 0..max_node are graph nodes, max_node+1 = super-source, max_node+2 = super-sink
        let source = max_node + 1;
        let sink = max_node + 2;
        let total_nodes = max_node + 3;

        // Residual capacities stored per edge direction.
        // For undirected edge i between a and b: capacity x[i] in both directions.
        // Plus source->u, source->v (infinite), and terminal->sink (infinite).
        let inf_cap = 1e10;

        // Build residual graph as adjacency list with (neighbor, capacity_ref_index, is_reverse)
        // Use edge-indexed residual: residual[edge_idx * 2] = fwd, residual[edge_idx * 2 + 1] = rev
        // Plus extra edges for source/sink connections.

        // Simpler approach: sparse residual with Vec<(neighbor, residual_cap, rev_edge_idx)>
        let mut graph_adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); total_nodes];
        let mut capacities: Vec<f64> = Vec::new();

        // Add graph edges (undirected = two directed)
        for i in 0..num_edges {
            if x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            let a = arc.tail as usize;
            let b = arc.head as usize;

            let fwd_idx = capacities.len();
            capacities.push(x[i]);
            let rev_idx = capacities.len();
            capacities.push(x[i]);

            graph_adj[a].push((b, fwd_idx));
            graph_adj[b].push((a, rev_idx));
        }

        // Source -> u, Source -> v (infinite capacity)
        for &node in &[u, v] {
            let fwd_idx = capacities.len();
            capacities.push(inf_cap);
            let rev_idx = capacities.len();
            capacities.push(0.0);
            graph_adj[source].push((node as usize, fwd_idx));
            graph_adj[node as usize].push((source, rev_idx));
        }

        // Terminal -> sink (infinite capacity)
        for &t in self.terminals {
            let fwd_idx = capacities.len();
            capacities.push(inf_cap);
            let rev_idx = capacities.len();
            capacities.push(0.0);
            graph_adj[t as usize].push((sink, fwd_idx));
            graph_adj[sink].push((t as usize, rev_idx));
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
            let mut parent: Vec<Option<(usize, usize)>> = vec![None; total_nodes]; // (from_node, edge_idx)
            let mut visited = vec![false; total_nodes];
            let mut queue = VecDeque::new();
            queue.push_back(source);
            visited[source] = true;

            let mut found_sink = false;
            while let Some(node) = queue.pop_front() {
                if node == sink {
                    found_sink = true;
                    break;
                }
                for &(neighbor, edge_idx) in &graph_adj[node] {
                    if !visited[neighbor] && capacities[edge_idx] > 1e-10 {
                        visited[neighbor] = true;
                        parent[neighbor] = Some((node, edge_idx));
                        queue.push_back(neighbor);
                    }
                }
            }

            if !found_sink { break; }

            // Find bottleneck
            let mut bottleneck = f64::INFINITY;
            let mut node = sink;
            while let Some((prev, edge_idx)) = parent[node] {
                bottleneck = bottleneck.min(capacities[edge_idx]);
                node = prev;
            }

            // Update residuals
            let mut node = sink;
            while let Some((prev, edge_idx)) = parent[node] {
                capacities[edge_idx] -= bottleneck;
                capacities[edge_idx ^ 1] += bottleneck;
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
        let mut reachable = vec![false; total_nodes];
        let mut queue = VecDeque::new();
        queue.push_back(source);
        reachable[source] = true;
        while let Some(node) = queue.pop_front() {
            for &(neighbor, edge_idx) in &graph_adj[node] {
                if !reachable[neighbor] && capacities[edge_idx] > 1e-10 {
                    reachable[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }

        // Set S = reachable graph nodes (excluding source/sink pseudo-nodes)
        let set_nodes: Vec<NodeId> = (0..=max_node)
            .filter(|&n| reachable[n] && n != source && n != sink)
            .map(|n| n as NodeId)
            .collect();

        // Boundary edges: edges with one endpoint in S, one outside
        let set_flags: HashSet<NodeId> = set_nodes.iter().copied().collect();
        let mut boundary_arcs: Vec<(ArcId, ArcId)> = Vec::new();
        for i in 0..num_edges {
            let arc = &self.graph.arcs[2 * i];
            let a_in = set_flags.contains(&arc.tail);
            let b_in = set_flags.contains(&arc.head);
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
