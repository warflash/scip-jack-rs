use crate::graph::{DirectedGraph, NodeId, Cost};

/// The directed cut formulation for the Steiner arborescence problem.
///
/// Variables: y_a ∈ {0, 1} for each arc a ∈ A
///
/// min  c^T y                                               (1)
/// s.t. y(δ+(W)) ≥ 1,  ∀W ⊂ V, r ∈ W, (V\W) ∩ T ≠ ∅      (2)
///      y(δ⁻(v)) = 0,  if v = r                            (3a)
///      y(δ⁻(v)) = 1,  if v ∈ T \ {r}                      (3b)
///      y(δ⁻(v)) ≤ 1,  if v ∈ N                            (3c)
///      y(δ⁻(v)) ≤ y(δ+(v)), ∀v ∈ N                        (4)
///      y(δ⁻(v)) ≥ y_a, ∀a ∈ δ+(v), v ∈ N                  (5)
///      0 ≤ y_a ≤ 1,    ∀a ∈ A                              (6)
///      y_a ∈ {0, 1},    ∀a ∈ A                              (7)
pub struct CutFormulation {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub steiner_nodes: Vec<NodeId>,
}

impl CutFormulation {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
        let steiner_nodes: Vec<NodeId> = graph.nodes.iter()
            .map(|n| n.id)
            .filter(|id| !terminal_set.contains(id))
            .collect();

        Self { graph, root, terminals, steiner_nodes }
    }

    pub fn num_variables(&self) -> u32 {
        self.graph.num_arcs()
    }

    pub fn objective_coefficients(&self) -> Vec<Cost> {
        self.graph.arcs.iter().map(|a| a.cost).collect()
    }

    /// Check if a given arc assignment violates any Steiner cut constraint (2).
    /// Returns violated cuts as sets W where y(δ+(W)) < 1.
    pub fn find_violated_cuts(&self, y: &[f64]) -> Vec<Vec<NodeId>> {
        // Separation by max-flow / min-cut computation
        // For each terminal t ∈ T \ {r}, compute max-flow from r to t
        // If max-flow < 1, the min-cut gives a violated constraint
        let mut violated = Vec::new();

        for &terminal in &self.terminals {
            if terminal == self.root {
                continue;
            }
            let (flow_value, cut_set) = self.compute_max_flow_min_cut(y, terminal);
            if flow_value < 1.0 - 1e-6 {
                violated.push(cut_set);
            }
        }

        violated
    }

    /// Compute max-flow from root to target using arc capacities y.
    /// Returns (flow_value, min_cut_set) where min_cut_set contains root.
    fn compute_max_flow_min_cut(&self, y: &[f64], target: NodeId) -> (f64, Vec<NodeId>) {
        // TODO: Implement max-flow algorithm (e.g., push-relabel or Dinic's)
        let _ = (y, target);
        (0.0, vec![self.root])
    }

    /// Check flow conservation constraints (3a-3c).
    pub fn check_flow_constraints(&self, y: &[f64]) -> bool {
        // (3a) y(δ⁻(r)) = 0
        let in_root: f64 = self.graph.delta_minus(self.root).iter()
            .map(|&(_, arc_id)| y[arc_id as usize])
            .sum();
        if in_root.abs() > 1e-6 {
            return false;
        }

        // (3b) y(δ⁻(v)) = 1 for v ∈ T \ {r}
        for &t in &self.terminals {
            if t == self.root { continue; }
            let in_t: f64 = self.graph.delta_minus(t).iter()
                .map(|&(_, arc_id)| y[arc_id as usize])
                .sum();
            if (in_t - 1.0).abs() > 1e-6 {
                return false;
            }
        }

        // (3c) y(δ⁻(v)) ≤ 1 for v ∈ N
        for &v in &self.steiner_nodes {
            let in_v: f64 = self.graph.delta_minus(v).iter()
                .map(|&(_, arc_id)| y[arc_id as usize])
                .sum();
            if in_v > 1.0 + 1e-6 {
                return false;
            }
        }

        true
    }
}
