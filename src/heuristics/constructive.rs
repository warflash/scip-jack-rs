use super::PrimalHeuristic;
use crate::graph::{DirectedGraph, NodeId, Cost};
use crate::model::SteinerSolution;

/// Shortest-path-based constructive heuristic (Takahashi & Matsuyama, 1980).
///
/// Algorithm:
/// 1. Start with one vertex (preferably a terminal)
/// 2. In each step, connect current subtree to nearest terminal via shortest path
/// 3. Repeat until all terminals are spanned
/// 4. Pruning: construct MST on computed tree vertices, remove degree-1 non-terminals
///
/// During branch-and-cut, uses altered edge weights: (1 - x_e) · c(e)
/// to bias towards edges in the LP solution.
///
/// Started from multiple vertices (100 initial calls, 10 after each LP).
pub struct ConstructiveHeuristic {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub num_starts: u32,
    pub lp_weights: Option<Vec<f64>>,
}

impl ConstructiveHeuristic {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        Self {
            graph,
            root,
            terminals,
            num_starts: 100,
            lp_weights: None,
        }
    }

    pub fn with_lp_weights(mut self, weights: Vec<f64>) -> Self {
        self.lp_weights = Some(weights);
        self.num_starts = 10;
        self
    }

    /// Compute effective arc costs incorporating LP solution bias.
    fn effective_costs(&self) -> Vec<Cost> {
        match &self.lp_weights {
            Some(y) => {
                self.graph.arcs.iter().enumerate().map(|(i, arc)| {
                    (1.0 - y[i]) * arc.cost
                }).collect()
            }
            None => self.graph.arcs.iter().map(|a| a.cost).collect(),
        }
    }

    /// Run single constructive heuristic from a given start node.
    fn construct_from(&self, _start: NodeId, _costs: &[Cost]) -> Option<SteinerSolution> {
        // TODO: Implement shortest-path-based construction
        // 1. Initialize tree with start node
        // 2. While not all terminals are spanned:
        //    a. Find nearest terminal to current tree (Dijkstra)
        //    b. Add shortest path to tree
        // 3. Prune: remove degree-1 Steiner nodes
        None
    }
}

impl PrimalHeuristic for ConstructiveHeuristic {
    fn run(&mut self) -> Option<SteinerSolution> {
        let costs = self.effective_costs();
        let mut best: Option<SteinerSolution> = None;

        // Start from terminals first (empirical advantage per paper)
        let start_nodes: Vec<NodeId> = self.terminals.iter()
            .copied()
            .take(self.num_starts as usize)
            .collect();

        for start in start_nodes {
            if let Some(sol) = self.construct_from(start, &costs) {
                match &best {
                    None => best = Some(sol),
                    Some(current_best) if sol.objective_value < current_best.objective_value => {
                        best = Some(sol);
                    }
                    _ => {}
                }
            }
        }

        best
    }
}
