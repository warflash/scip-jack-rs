use crate::graph::{NodeId, ArcId, Cost};

/// A feasible solution to the Steiner tree problem represented as a set of arcs
/// forming a Steiner arborescence.
#[derive(Debug, Clone)]
pub struct SteinerSolution {
    pub arcs: Vec<ArcId>,
    pub nodes: Vec<NodeId>,
    pub objective_value: Cost,
    pub is_optimal: bool,
}

impl SteinerSolution {
    pub fn new(arcs: Vec<ArcId>, nodes: Vec<NodeId>, objective_value: Cost) -> Self {
        Self {
            arcs,
            nodes,
            objective_value,
            is_optimal: false,
        }
    }

    pub fn empty() -> Self {
        Self {
            arcs: Vec::new(),
            nodes: Vec::new(),
            objective_value: f64::INFINITY,
            is_optimal: false,
        }
    }

    pub fn is_feasible(&self) -> bool {
        !self.arcs.is_empty() && self.objective_value < f64::INFINITY
    }

    pub fn is_empty(&self) -> bool {
        self.arcs.is_empty()
    }
}
