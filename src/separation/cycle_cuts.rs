use std::collections::{BinaryHeap, HashMap, HashSet};
use std::cmp::Ordering;
use crate::graph::{DirectedGraph, NodeId, ArcId};

/// Cycle closure separator for the Forest-Closed BCR relaxation.
///
/// Introduce undirected x_e = y_{uv} + y_{vu} and add:
///   x(C) ≤ |C| - 1   for every simple cycle C
///
/// Separation: find minimum-weight cycles with lengths (1 - x_e).
/// If minimum cycle weight < 1, the cycle inequality is violated.

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

        // Build adjacency using HashMap to handle sparse node IDs
        let mut adj: HashMap<NodeId, Vec<(NodeId, usize, f64)>> = HashMap::new();
        for i in 0..num_edges {
            if x[i] < 1e-8 { continue; }
            let arc = &self.graph.arcs[2 * i];
            let w = (1.0 - x[i]).max(0.0);
            adj.entry(arc.tail).or_default().push((arc.head, i, w));
            adj.entry(arc.head).or_default().push((arc.tail, i, w));
        }

        let mut active_nodes: Vec<NodeId> = adj.keys().copied().collect();
        active_nodes.sort();

        let mut violated_cuts = Vec::new();
        let mut used_edges: HashSet<usize> = HashSet::new();

        // Only process nodes with degree >= 2
        for &v in &active_nodes {
            let neighbors = match adj.get(&v) {
                Some(n) if n.len() >= 2 => n.clone(),
                _ => continue,
            };

            for i in 0..neighbors.len().min(8) {
                for j in (i+1)..neighbors.len().min(8) {
                    let (u, ei, wi) = neighbors[i];
                    let (w, ej, wj) = neighbors[j];

                    if used_edges.contains(&ei) || used_edges.contains(&ej) { continue; }
                    if ei == ej { continue; }

                    let path_cost = dijkstra_avoid_sparse(u, w, v, &adj);

                    let cycle_cost = wi + wj + path_cost;

                    if cycle_cost < 1.0 - self.violation_tolerance {
                        let violation = 1.0 - cycle_cost;

                        let arc_ids = vec![
                            (2 * ei) as ArcId, (2 * ei + 1) as ArcId,
                            (2 * ej) as ArcId, (2 * ej + 1) as ArcId,
                        ];

                        used_edges.insert(ei);
                        used_edges.insert(ej);

                        violated_cuts.push(CycleCut {
                            edge_indices: vec![ei as u32, ej as u32],
                            arc_ids,
                            violation,
                        });

                        if violated_cuts.len() >= 10 { break; }
                    }
                }
                if violated_cuts.len() >= 10 { break; }
            }
            if violated_cuts.len() >= 10 { break; }
        }

        violated_cuts.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(Ordering::Equal));
        self.cuts_found = violated_cuts.len() as u32;
        violated_cuts
    }
}

fn dijkstra_avoid_sparse(
    source: NodeId,
    target: NodeId,
    avoid: NodeId,
    adj: &HashMap<NodeId, Vec<(NodeId, usize, f64)>>,
) -> f64 {
    if source == target { return 0.0; }

    let mut dist: HashMap<NodeId, f64> = HashMap::new();
    let mut heap = BinaryHeap::new();

    dist.insert(source, 0.0);
    heap.push(DEntry { cost: 0.0, node: source });

    while let Some(DEntry { cost, node }) = heap.pop() {
        if node == target { return cost; }
        if cost > *dist.get(&node).unwrap_or(&f64::INFINITY) + 1e-10 { continue; }

        if let Some(neighbors) = adj.get(&node) {
            for &(next, _, w) in neighbors {
                if next == avoid { continue; }
                let new_cost = cost + w;
                if new_cost < *dist.get(&next).unwrap_or(&f64::INFINITY) - 1e-10 {
                    dist.insert(next, new_cost);
                    heap.push(DEntry { cost: new_cost, node: next });
                }
            }
        }
    }

    *dist.get(&target).unwrap_or(&f64::INFINITY)
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
