use crate::model::SteinerSolution;

/// Status of the branch-and-bound solving process.
#[derive(Debug, Clone, PartialEq)]
pub enum SolveStatus {
    Optimal,
    Feasible,
    Infeasible,
    TimeLimit,
    MemoryLimit,
    NodeLimit,
}

/// A node in the branch-and-bound tree.
#[derive(Debug, Clone)]
pub struct BbNode {
    pub id: u64,
    pub parent: Option<u64>,
    pub depth: u32,
    pub dual_bound: f64,
    pub primal_bound: f64,
    /// Variable fixings: (arc_id, fixed_value)
    pub fixings: Vec<(u32, f64)>,
}

/// The branch-and-bound tree managing the search.
pub struct BranchAndBoundTree {
    pub nodes: Vec<BbNode>,
    pub open_nodes: Vec<u64>,
    pub best_solution: Option<SteinerSolution>,
    pub global_dual_bound: f64,
    pub global_primal_bound: f64,
    pub nodes_processed: u64,
    pub status: SolveStatus,
}

impl BranchAndBoundTree {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            open_nodes: Vec::new(),
            best_solution: None,
            global_dual_bound: f64::NEG_INFINITY,
            global_primal_bound: f64::INFINITY,
            nodes_processed: 0,
            status: SolveStatus::Feasible,
        }
    }

    pub fn gap(&self) -> f64 {
        if self.global_primal_bound == f64::INFINITY {
            return f64::INFINITY;
        }
        if self.global_primal_bound.abs() < 1e-10 {
            return 0.0;
        }
        (self.global_primal_bound - self.global_dual_bound) / self.global_primal_bound.abs()
    }

    pub fn is_solved(&self) -> bool {
        self.gap() < 1e-6
    }

    pub fn update_primal(&mut self, solution: SteinerSolution) {
        if solution.objective_value < self.global_primal_bound {
            self.global_primal_bound = solution.objective_value;
            self.best_solution = Some(solution);
        }
    }

    /// Prune nodes whose dual bound exceeds the global primal bound.
    pub fn prune(&mut self) {
        self.open_nodes.retain(|&node_id| {
            self.nodes[node_id as usize].dual_bound < self.global_primal_bound - 1e-6
        });
    }
}
