use std::collections::BinaryHeap;
use std::cmp::Ordering;
use crate::graph::{cmp_cost, DirectedGraph, NodeId, ArcId};

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
    x: Vec<f64>,
    adj: Vec<Vec<(NodeId, usize, f64)>>,
    node_flow: Vec<(NodeId, f64)>,
    used_edges: Vec<bool>,
    dijkstra: CycleDijkstraWorkspace,
}

struct CycleDijkstraWorkspace {
    dist: Vec<f64>,
    prev: Vec<Option<(NodeId, usize)>>,
    heap: BinaryHeap<DEntry>,
    sorted_neighbors: Vec<(NodeId, usize, f64)>,
    path: Vec<usize>,
}

impl CycleDijkstraWorkspace {
    fn new(num_nodes: usize) -> Self {
        Self {
            dist: vec![f64::INFINITY; num_nodes],
            prev: vec![None; num_nodes],
            heap: BinaryHeap::new(),
            sorted_neighbors: Vec::new(),
            path: Vec::new(),
        }
    }
}

impl<'a> CycleCutSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph) -> Self {
        let max_node = graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let num_edges = graph.arcs.len() / 2;
        Self {
            graph,
            cuts_found: 0,
            violation_tolerance: 1e-4,
            x: Vec::with_capacity(num_edges),
            adj: vec![Vec::new(); max_node + 1],
            node_flow: Vec::with_capacity(max_node + 1),
            used_edges: vec![false; num_edges],
            dijkstra: CycleDijkstraWorkspace::new(max_node + 1),
        }
    }

    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<CycleCut> {
        let num_arcs = self.graph.arcs.len();
        let num_edges = num_arcs / 2;

        self.x.resize(num_edges, 0.0);
        for i in 0..num_edges {
            self.x[i] = lp_solution[2 * i] + lp_solution[2 * i + 1];
        }

        // Build undirected adjacency with edge weights w_e = 1 - x_e.
        // Only include edges in the fractional support (x_e > 0).
        let max_node = self.graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        if self.adj.len() <= max_node {
            self.adj.resize_with(max_node + 1, Vec::new);
        }
        for neighbours in &mut self.adj {
            neighbours.clear();
        }

        for i in 0..num_edges {
            if self.x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            let w = (1.0 - self.x[i]).max(0.0);
            self.adj[arc.tail as usize].push((arc.head, i, w));
            self.adj[arc.head as usize].push((arc.tail, i, w));
        }

        // Collect nodes in the fractional support, sorted by total incident
        // fractional flow (highest first - these are most likely part of
        // violated cycles).
        self.node_flow.clear();
        for node in &self.graph.nodes {
            let v = node.id as usize;
            if self.adj[v].is_empty() { continue; }
            let total: f64 = self.adj[v].iter().map(|&(_, ei, _)| self.x[ei]).sum();
            self.node_flow.push((node.id, total));
        }
        self.node_flow.sort_by(|a, b| cmp_cost(b.1, a.1));

        // For each candidate node, find the shortest cycle through it.
        // A cycle through v consists of an edge (v, u) plus a path from u back to v
        // not using v as an intermediate.
        let mut violated_cuts: Vec<CycleCut> = Vec::new();
        self.used_edges.fill(false);

        // Limit the number of Dijkstra runs based on graph density
        let max_source_nodes = 100.min(self.node_flow.len());

        for &(v, _) in self.node_flow.iter().take(max_source_nodes) {
            if violated_cuts.len() >= 30 { break; }

            let neighbors = &self.adj[v as usize];
            if neighbors.len() < 2 { continue; }

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
            let cycle_result = find_shortest_cycle_through(
                v,
                neighbors,
                &self.adj,
                max_node,
                &mut self.dijkstra,
            );

            if let Some((cost, edges)) = cycle_result {
                if cost < 1.0 - self.violation_tolerance {
                    let violation = 1.0 - cost;
                    let mut all_new = true;
                    for &e in &edges {
                        if self.used_edges[e] { all_new = false; break; }
                    }
                    if !all_new && violation < 0.05 { continue; }

                    for &e in &edges { self.used_edges[e] = true; }

                    let mut arc_ids: Vec<ArcId> = Vec::with_capacity(edges.len() * 2);
                    let edge_indices: Vec<u32> = edges.iter().map(|&e| e as u32).collect();
                    for &ei in &edge_indices {
                        arc_ids.push(2 * ei as ArcId);
                        arc_ids.push(2 * ei as ArcId + 1);
                    }

                    // `x(C) <= |C| - 1` is valid only when C really is a simple
                    // cycle; for a path it would forbid a tree from using every
                    // edge of that path. The reconstruction below is only correct
                    // because the u-w path avoids v, so the three pieces are
                    // vertex-disjoint apart from their endpoints.
                    debug_assert!(
                        is_simple_cycle(&edge_indices, self.graph),
                        "cycle separator emitted a non-cycle: {edge_indices:?}"
                    );
                    violated_cuts.push(CycleCut {
                        edge_indices,
                        arc_ids,
                        violation,
                    });
                }
            }
        }

        violated_cuts.sort_by(|a, b| cmp_cost(b.violation, a.violation));
        self.cuts_found = violated_cuts.len() as u32;
        violated_cuts
    }
}

/// True when `edges` (undirected edge indices) form one simple cycle: connected,
/// every incident vertex of degree exactly two, and as many vertices as edges.
pub(crate) fn is_simple_cycle(edges: &[u32], graph: &DirectedGraph) -> bool {
    if edges.len() < 3 {
        return false;
    }
    let mut degree: std::collections::HashMap<NodeId, u32> = std::collections::HashMap::new();
    let mut adj: std::collections::HashMap<NodeId, Vec<NodeId>> = std::collections::HashMap::new();
    for &e in edges {
        let arc = &graph.arcs[2 * e as usize];
        *degree.entry(arc.tail).or_insert(0) += 1;
        *degree.entry(arc.head).or_insert(0) += 1;
        adj.entry(arc.tail).or_default().push(arc.head);
        adj.entry(arc.head).or_default().push(arc.tail);
    }
    if degree.len() != edges.len() {
        return false;
    }
    if degree.values().any(|&d| d != 2) {
        return false;
    }
    // Connectivity.
    let start = *degree.keys().next().unwrap();
    let mut seen = std::collections::HashSet::from([start]);
    let mut stack = vec![start];
    while let Some(v) = stack.pop() {
        for &u in adj.get(&v).map(|v| v.as_slice()).unwrap_or(&[]) {
            if seen.insert(u) {
                stack.push(u);
            }
        }
    }
    seen.len() == degree.len()
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
    ws: &mut CycleDijkstraWorkspace,
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
    let mut best_found = false;
    let mut best_first_edge: Option<usize> = None;
    let mut best_last_edge: Option<usize> = None;

    // Sort neighbors by edge weight (smallest first for early termination)
    ws.sorted_neighbors.clear();
    ws.sorted_neighbors.extend_from_slice(neighbors);
    ws.sorted_neighbors.sort_by(|a, b| cmp_cost(a.2, b.2));

    for i in 0..max_neighbor_runs {
        let (u, ei, wi) = ws.sorted_neighbors[i];

        // Early termination: if wi alone >= best_cost, skip
        if wi >= best_cost { break; }

        // Dijkstra from u, avoiding v
        dijkstra_from_avoiding(u, v, adj, max_node, ws);

        // Check all other neighbors of v
        for j in 0..neighbors.len() {
            if i == j && ws.sorted_neighbors[i].0 == neighbors[j].0 { continue; }
            let (w, ej, wj) = neighbors[j];
            if w == u && ei == ej { continue; }
            if w == u { continue; }

            let d = ws.dist[w as usize];
            if d >= f64::INFINITY / 2.0 { continue; }

            let cycle_cost = wi + d + wj;
            if cycle_cost < best_cost {
                best_cost = cycle_cost;
                best_first_edge = Some(ei);
                best_last_edge = Some(ej);
                // Reconstruct the winning path once, after all source runs. The
                // predecessor storage is reused for each Dijkstra instead of
                // allocating a path vector on every improvement.
                best_found = true;
            }
        }
    }

    if best_cost < f64::INFINITY / 2.0 {
        if !best_found {
            return None;
        }
        ws.path.clear();
        // The winning source is encoded by the first edge's endpoint in the
        // search above. Re-run that one shortest path to recover predecessors
        // after the final Dijkstra run.
        let first_edge = best_first_edge?;
        let last_edge = best_last_edge?;
        let start = neighbors
            .iter()
            .find(|&&(_, edge, _)| edge == first_edge)
            .map(|&(node, _, _)| node)?;
        let target = neighbors
            .iter()
            .find(|&&(_, edge, _)| edge == last_edge)
            .map(|&(node, _, _)| node)?;
        dijkstra_from_avoiding(start, v, adj, max_node, ws);
        let mut cur = target;
        while cur != start {
            if let Some((pred, edge_idx)) = ws.prev[cur as usize] {
                ws.path.push(edge_idx);
                cur = pred;
            } else {
                break;
            }
        }
        let mut all_edges: Vec<usize> = Vec::new();
        all_edges.push(first_edge);
        all_edges.push(last_edge);
        all_edges.extend_from_slice(&ws.path);
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
    _max_node: usize,
    ws: &mut CycleDijkstraWorkspace,
) {
    ws.dist.fill(f64::INFINITY);
    ws.prev.fill(None);
    ws.heap.clear();

    ws.dist[source as usize] = 0.0;
    ws.heap.push(DEntry { cost: 0.0, node: source });

    while let Some(DEntry { cost, node }) = ws.heap.pop() {
        if cost > ws.dist[node as usize] + 1e-10 { continue; }

        for &(next, edge_idx, w) in &adj[node as usize] {
            if next == avoid { continue; }
            let new_cost = cost + w;
            if new_cost < ws.dist[next as usize] - 1e-10 {
                ws.dist[next as usize] = new_cost;
                ws.prev[next as usize] = Some((node, edge_idx));
                ws.heap.push(DEntry { cost: new_cost, node: next });
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
struct DEntry { cost: f64, node: NodeId }
impl Eq for DEntry {}
impl Ord for DEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_cost(other.cost, self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}
impl PartialOrd for DEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{NodeType, UndirectedGraph};

    /// Square with both diagonals, so several cycles pass through every vertex.
    fn square_with_diagonals() -> DirectedGraph {
        let mut g = UndirectedGraph::new(4);
        for v in 1..=4u32 {
            g.add_node(v, NodeType::Steiner, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(4, 1, 1.0);
        g.add_edge(1, 3, 1.0);
        g.add_edge(2, 4, 1.0);
        DirectedGraph::from_undirected(&g)
    }

    #[test]
    fn every_emitted_cut_is_a_simple_cycle() {
        // `x(C) <= |C| - 1` is only valid for a cycle. If the separator ever
        // returned a path instead, the inequality would forbid a tree from using
        // all of that path's edges and the dual bound would become unsound.
        let g = square_with_diagonals();
        let mut sep = CycleCutSeparator::new(&g);
        // x_e = 0.8 on every edge, so w_e = 0.2 and any triangle weighs 0.6 < 1.
        let lp = vec![0.4; g.arcs.len()];
        let cuts = sep.find_violated_cuts(&lp);
        assert!(!cuts.is_empty(), "expected violated cycle inequalities");
        for c in &cuts {
            assert!(
                is_simple_cycle(&c.edge_indices, &g),
                "emitted a non-cycle: {:?}",
                c.edge_indices
            );
        }
    }

    #[test]
    fn a_spanning_tree_satisfies_every_emitted_cut() {
        // Direct check of validity: the inequality must not cut off any tree.
        let g = square_with_diagonals();
        let mut sep = CycleCutSeparator::new(&g);
        let lp = vec![0.4; g.arcs.len()];
        let cuts = sep.find_violated_cuts(&lp);

        // Star tree on {1,2,3,4}: edges 1-2, 1-4, 1-3 (indices 0, 3, 4).
        let tree_edges = [0usize, 3, 4];
        for c in &cuts {
            let used = c
                .edge_indices
                .iter()
                .filter(|e| tree_edges.contains(&(**e as usize)))
                .count();
            assert!(
                used <= c.edge_indices.len() - 1,
                "cycle cut over {:?} is violated by a spanning tree",
                c.edge_indices
            );
        }
    }

    #[test]
    fn no_cuts_when_the_support_is_a_tree() {
        let g = square_with_diagonals();
        let mut sep = CycleCutSeparator::new(&g);
        let mut lp = vec![0.0; g.arcs.len()];
        for e in [0usize, 3, 4] {
            lp[2 * e] = 1.0;
        }
        assert!(sep.find_violated_cuts(&lp).is_empty());
    }

    #[test]
    fn rejects_non_cycles() {
        let g = square_with_diagonals();
        assert!(is_simple_cycle(&[0, 1, 2, 3], &g), "1-2-3-4-1 is a cycle");
        assert!(!is_simple_cycle(&[0, 1], &g), "a two-edge path is not a cycle");
        assert!(!is_simple_cycle(&[0, 1, 2], &g), "1-2-3-4 is a path, not a cycle");
    }
}
