use super::Separator;
use crate::graph::{DirectedGraph, NodeId};

/// Separates violated directed cut constraints (Steiner cuts).
///
/// For each terminal t ∈ T \ {r}, compute max-flow from root to t
/// using arc capacities from the LP solution. If flow < 1, the min-cut
/// gives a violated Steiner cut constraint: y(δ+(W)) ≥ 1.
pub struct FlowCutSeparator {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub cuts_found: u32,
}

impl FlowCutSeparator {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        Self { graph, root, terminals, cuts_found: 0 }
    }
}

impl Separator for FlowCutSeparator {
    fn separate(&mut self, _lp_solution: &[f64]) -> u32 {
        // TODO: For each terminal t ≠ root:
        //   1. Set arc capacities to y values from LP solution
        //   2. Compute max-flow from root to t
        //   3. If max-flow < 1 - epsilon:
        //      - Extract min-cut set W (containing root)
        //      - Add constraint: sum of y_a for a ∈ δ+(W) ≥ 1
        //      - Increment cuts_found
        0
    }
}
