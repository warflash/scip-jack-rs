use std::collections::BinaryHeap;
use std::cmp::Ordering;
use crate::graph::{DirectedGraph, NodeId, ArcId};

/// Cycle closure separator for the Forest-Closed BCR relaxation.
///
/// Introduce undirected x_e = y_{uv} + y_{vu} and add:
///   x(C) <= |C| - 1   for every simple cycle C
///
/// Separation: find minimum-weight cycles with lengths (1 - x_e).
/// If minimum cycle weight < 1, the cycle inequality is violated.
///
/// The exact separation is the minimum-weight simple cycle problem with
/// non-negative edge weights w_e = 1 - x_e. For each node v, we find the
/// shortest cycle through v by computing shortest path from all neighbors
/// of v back to v (excluding v). The overall minimum gives the most
/// violated cycle.

pub struct CycleCut {
    pub edge_indices: Vec<u32>,
    pub arc_ids: Vec<ArcId>,
    pub violation: f64,
}

pub struct CycleCutSeparator<'a> {
    graph: &'a DirectedGraph,
    pub cuts_found: u32,
    pub violation_tolerance: f64,
}

impl<'a> CycleCutSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph) -> Self {
        Self {
            graph,
            cuts_found: 0,
            violation_tolerance: 1e-4,
        }
    }

    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<CycleCut> {
        let num_arcs = self.graph.arcs.len();
        let num_edges = num_arcs / 2;

        let mut x: Vec<f64> = vec![0.0; num_edges];
        for i in 0..num_edges {
            let fwd = lp_solution.get(2 * i).copied().unwrap_or(0.0);
            let rev = lp_solution.get(2 * i + 1).copied().unwrap_or(0.0);
            x[i] = fwd + rev;
        }

        // Build undirected adjacency with edge weights w_e = 1 - x_e.
        // Only include edges in the fractional support (x_e > 0).
        let max_node = self.graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let mut adj: Vec<Vec<(NodeId, usize, f64)>> = vec![Vec::new(); max_node + 1];

        for i in 0..num_edges {
            if x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            let w = (1.0 - x[i]).max(0.0);
            adj[arc.tail as usize].push((arc.head, i, w));
            adj[arc.head as usize].push((arc.tail, i, w));
        }

        // Collect nodes in the fractional support, sorted by total incident
        // fractional flow (highest first - these are most likely part of
        // violated cycles).
        let mut node_flow: Vec<(NodeId, f64)> = Vec::new();
        for node in &self.graph.nodes {
            let v = node.id as usize;
            if adj[v].is_empty() { continue; }
            let total: f64 = adj[v].iter().map(|&(_, ei, _)| x[ei]).sum();
            node_flow.push((node.id, total));
        }
        node_flow.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(Ordering::Equal));

        // For each candidate node, find the shortest cycle through it.
        // A cycle through v consists of an edge (v, u) plus a path from u back to v
        // not using v as an intermediate.
        let mut violated_cuts: Vec<CycleCut> = Vec::new();
        let mut used_edges: Vec<bool> = vec![false; num_edges];

        // Limit the number of Dijkstra runs based on graph density
        let max_source_nodes = 100.min(node_flow.len());

        for &(v, _) in node_flow.iter().take(max_source_nodes) {
            if violated_cuts.len() >= 30 { break; }

            let neighbors: Vec<(NodeId, usize, f64)> = adj[v as usize].clone();
            if neighbors.len() < 2 { continue; }

            // Run Dijkstra from v in the graph with v removed.
            // This gives shortest paths from v's neighbors back to each other.
            // A cycle through v = edge(v,u) + shortest_path(u, w, avoiding v) + edge(w,v)
            let _dist = dijkstra_from_node_avoiding(v, &adj, max_node);

            // For each pair of neighbors (u, w), the cycle v-u-...-w-v has weight
            // w(v,u) + dist[u->w without v] + w(w,v). Since the graph is undirected,
            // dist[u] gives the shortest path from the "source super-node" that
            // starts from all neighbors simultaneously.
            //
            // Actually, for the correct approach: for each neighbor u of v,
            // the shortest cycle through v via u first is:
            //   w(v,u) + shortest_path(u -> v, not using edge(v,u) directly)
            // But since we removed v, we need path from u to another neighbor w,
            // then + w(w,v).

            // Better approach: shortest cycle through v = min over edges (v,u):
            //   w(v,u) + dist(u, v) in graph with v removed
            // But v is removed, so we can't reach v. Instead:
            //   shortest cycle = min over pairs of edges (v,u), (v,w):
            //     w(v,u) + shortest_path(u->w, avoiding v) + w(v,w)
            // This equals: for fixed first edge (v,u), find minimum over second edge (v,w):
            //   w(v,u) + dist[w] + w(v,w) where dist is shortest path from u avoiding v.

            // Even better: run Dijkstra from ALL neighbors of v simultaneously with
            // source labels, find the shortest path between two DIFFERENT neighbors.
            let cycle_result = find_shortest_cycle_through(v, &neighbors, &adj, max_node, &x);

            if let Some((cost, edges)) = cycle_result {
                if cost < 1.0 - self.violation_tolerance {
                    let violation = 1.0 - cost;
                    let mut all_new = true;
                    for &e in &edges {
                        if used_edges[e] { all_new = false; break; }
                    }
                    if !all_new && violation < 0.05 { continue; }

                    for &e in &edges { used_edges[e] = true; }

                    let mut arc_ids: Vec<ArcId> = Vec::with_capacity(edges.len() * 2);
                    let edge_indices: Vec<u32> = edges.iter().map(|&e| e as u32).collect();
                    for &ei in &edge_indices {
                        arc_ids.push(2 * ei as ArcId);
                        arc_ids.push(2 * ei as ArcId + 1);
                    }

                    violated_cuts.push(CycleCut {
                        edge_indices,
                        arc_ids,
                        violation,
                    });
                }
            }
        }

        violated_cuts.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(Ordering::Equal));
        self.cuts_found = violated_cuts.len() as u32;
        violated_cuts
    }
}

/// Find the shortest cycle through node v by running Dijkstra from each of v's
/// neighbors in the graph with v removed.
///
/// Returns (cycle_weight, edge_indices) or None.
fn find_shortest_cycle_through(
    v: NodeId,
    neighbors: &[(NodeId, usize, f64)],
    adj: &[Vec<(NodeId, usize, f64)>],
    max_node: usize,
    _x: &[f64],
) -> Option<(f64, Vec<usize>)> {
    // For efficiency, we use a multi-source Dijkstra: start from all neighbors
    // of v simultaneously, labeling each with its source identity. When we reach
    // a node from two different sources, we've found a cycle.
    //
    // But more precisely: we want the shortest u->w path (avoiding v) for
    // any two distinct neighbors u, w of v, and then the cycle weight is
    // w(v,u) + path_weight(u,w) + w(w,v).

    if neighbors.len() < 2 { return None; }

    // For up to ~20 neighbors, run individual Dijkstra from each.
    // For more, use the two-source trick.
    let max_neighbor_runs = 12.min(neighbors.len());

    let mut best_cost = f64::INFINITY;
    let mut best_path: Option<Vec<usize>> = None;
    let mut best_first_edge: Option<usize> = None;
    let mut best_last_edge: Option<usize> = None;

    // Sort neighbors by edge weight (smallest first for early termination)
    let mut sorted_neighbors = neighbors.to_vec();
    sorted_neighbors.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(Ordering::Equal));

    for i in 0..max_neighbor_runs {
        let (u, ei, wi) = sorted_neighbors[i];

        // Early termination: if wi alone >= best_cost, skip
        if wi >= best_cost { break; }

        // Dijkstra from u, avoiding v
        let (dist, prev) = dijkstra_from_avoiding(u, v, adj, max_node);

        // Check all other neighbors of v
        for j in 0..neighbors.len() {
            if i == j && sorted_neighbors[i].0 == neighbors[j].0 { continue; }
            let (w, ej, wj) = neighbors[j];
            if w == u && ei == ej { continue; }
            if w == u { continue; }

            let d = dist[w as usize];
            if d >= f64::INFINITY / 2.0 { continue; }

            let cycle_cost = wi + d + wj;
            if cycle_cost < best_cost {
                best_cost = cycle_cost;
                best_first_edge = Some(ei);
                best_last_edge = Some(ej);
                // Reconstruct path edges
                let mut path_edges = Vec::new();
                let mut cur = w;
                while cur != u {
                    if let Some((pred, edge_idx)) = prev[cur as usize] {
                        path_edges.push(edge_idx);
                        cur = pred;
                    } else {
                        break;
                    }
                }
                best_path = Some(path_edges);
            }
        }
    }

    if best_cost < f64::INFINITY / 2.0 {
        let mut all_edges: Vec<usize> = Vec::new();
        if let Some(fe) = best_first_edge { all_edges.push(fe); }
        if let Some(le) = best_last_edge { all_edges.push(le); }
        if let Some(path) = best_path { all_edges.extend(path); }
        all_edges.sort();
        all_edges.dedup();
        Some((best_cost, all_edges))
    } else {
        None
    }
}

/// Run Dijkstra from `source` avoiding node `avoid`.
/// Returns (distances, prev_map) where prev_map maps node_idx -> (predecessor, edge_idx).
fn dijkstra_from_avoiding(
    source: NodeId,
    avoid: NodeId,
    adj: &[Vec<(NodeId, usize, f64)>],
    max_node: usize,
) -> (Vec<f64>, Vec<Option<(NodeId, usize)>>) {
    let mut dist = vec![f64::INFINITY; max_node + 1];
    let mut prev: Vec<Option<(NodeId, usize)>> = vec![None; max_node + 1];
    let mut heap = BinaryHeap::new();

    dist[source as usize] = 0.0;
    heap.push(DEntry { cost: 0.0, node: source });

    while let Some(DEntry { cost, node }) = heap.pop() {
        if cost > dist[node as usize] + 1e-10 { continue; }

        for &(next, edge_idx, w) in &adj[node as usize] {
            if next == avoid { continue; }
            let new_cost = cost + w;
            if new_cost < dist[next as usize] - 1e-10 {
                dist[next as usize] = new_cost;
                prev[next as usize] = Some((node, edge_idx));
                heap.push(DEntry { cost: new_cost, node: next });
            }
        }
    }

    (dist, prev)
}

/// Run Dijkstra from `source` in the graph with `avoid` removed.
/// Simple version used for distance computation only.
fn dijkstra_from_node_avoiding(
    avoid: NodeId,
    _adj: &[Vec<(NodeId, usize, f64)>],
    max_node: usize,
) -> Vec<f64> {
    // This isn't directly used anymore, but kept for potential future use
    let mut dist = vec![f64::INFINITY; max_node + 1];
    dist[avoid as usize] = 0.0;
    dist
}

#[derive(Clone, PartialEq)]
struct DEntry { cost: f64, node: NodeId }
impl Eq for DEntry {}
impl Ord for DEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.partial_cmp(&self.cost).unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}
impl PartialOrd for DEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}
