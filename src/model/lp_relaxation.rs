use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use highs::{RowProblem, Sense, HighsModelStatus};

/// LP relaxation of the directed cut formulation for the Steiner arborescence problem.
///
/// Manages the constraint matrix and interfaces with HiGHS for solving.
/// Supports dynamic cut addition for the branch-and-cut framework.
pub struct LpRelaxation {
    pub num_vars: u32,
    pub objective: Vec<Cost>,
    pub solution: Vec<f64>,
    pub dual_bound: f64,
    /// Constraint storage: each row is (arc_indices, coefficients, lower_bound, upper_bound)
    constraints: Vec<LpConstraint>,
    /// Status of the last solve
    pub status: LpStatus,
    /// Number of LP solves performed
    pub solve_count: u64,
}

#[derive(Debug, Clone)]
struct LpConstraint {
    vars: Vec<u32>,
    coeffs: Vec<f64>,
    lb: f64,
    ub: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LpStatus {
    NotSolved,
    Optimal,
    Infeasible,
    Unbounded,
    Error,
}

impl LpRelaxation {
    /// Create a new LP relaxation from the directed cut formulation.
    ///
    /// Initializes with:
    /// - Variables y_a ∈ [0, 1] for each arc
    /// - Objective: min Σ c(a) * y_a
    /// - Flow conservation constraints (3a, 3b, 3c)
    /// - Flow balance constraints (4)
    pub fn from_formulation(graph: &DirectedGraph, root: NodeId, terminals: &[NodeId], steiner_nodes: &[NodeId]) -> Self {
        let num_arcs = graph.num_arcs();
        let objective: Vec<Cost> = graph.arcs.iter().map(|a| a.cost).collect();

        let mut lp = Self {
            num_vars: num_arcs,
            objective: objective.clone(),
            solution: vec![0.0; num_arcs as usize],
            dual_bound: f64::NEG_INFINITY,
            constraints: Vec::new(),
            status: LpStatus::NotSolved,
            solve_count: 0,
        };

        // (3a) y(δ⁻(root)) = 0: no incoming flow to root
        let in_root: Vec<(u32, f64)> = graph.delta_minus(root).iter()
            .map(|&(_, arc_id)| (arc_id, 1.0))
            .collect();
        if !in_root.is_empty() {
            lp.add_constraint_raw(&in_root, 0.0, 0.0);
        }

        // (3b) y(δ⁻(t)) = 1 for each terminal t ≠ root
        for &t in terminals {
            if t == root { continue; }
            let in_t: Vec<(u32, f64)> = graph.delta_minus(t).iter()
                .map(|&(_, arc_id)| (arc_id, 1.0))
                .collect();
            if !in_t.is_empty() {
                lp.add_constraint_raw(&in_t, 1.0, 1.0);
            }
        }

        // (3c) y(δ⁻(v)) ≤ 1 for each Steiner node v
        for &v in steiner_nodes {
            let in_v: Vec<(u32, f64)> = graph.delta_minus(v).iter()
                .map(|&(_, arc_id)| (arc_id, 1.0))
                .collect();
            if !in_v.is_empty() {
                lp.add_constraint_raw(&in_v, 0.0, 1.0);
            }
        }

        // (4) y(δ⁻(v)) ≤ y(δ+(v)) for each Steiner node v
        // Rewritten: -y(δ+(v)) + y(δ⁻(v)) ≤ 0
        for &v in steiner_nodes {
            let mut vars_coeffs: Vec<(u32, f64)> = Vec::new();
            for &(_, arc_id) in graph.delta_minus(v) {
                vars_coeffs.push((arc_id, 1.0));
            }
            for &(_, arc_id) in graph.delta_plus(v) {
                vars_coeffs.push((arc_id, -1.0));
            }
            if !vars_coeffs.is_empty() {
                lp.add_constraint_raw(&vars_coeffs, f64::NEG_INFINITY, 0.0);
            }
        }

        // (5) y(δ⁻(v)) ≥ y_a for each a ∈ δ+(v), for Steiner nodes v
        // Rewritten: y(δ⁻(v)) - y_a ≥ 0
        for &v in steiner_nodes {
            let in_arcs: Vec<ArcId> = graph.delta_minus(v).iter()
                .map(|&(_, arc_id)| arc_id)
                .collect();

            for &(_, out_arc) in graph.delta_plus(v) {
                let mut vars_coeffs: Vec<(u32, f64)> = Vec::new();
                for &in_arc in &in_arcs {
                    vars_coeffs.push((in_arc, 1.0));
                }
                vars_coeffs.push((out_arc, -1.0));
                if !vars_coeffs.is_empty() {
                    lp.add_constraint_raw(&vars_coeffs, 0.0, f64::INFINITY);
                }
            }
        }

        lp
    }

    /// Simplified constructor for basic usage.
    pub fn new(num_vars: u32, objective: Vec<Cost>) -> Self {
        Self {
            num_vars,
            objective,
            solution: vec![0.0; num_vars as usize],
            dual_bound: f64::NEG_INFINITY,
            constraints: Vec::new(),
            status: LpStatus::NotSolved,
            solve_count: 0,
        }
    }

    fn add_constraint_raw(&mut self, vars_coeffs: &[(u32, f64)], lb: f64, ub: f64) {
        let vars: Vec<u32> = vars_coeffs.iter().map(|&(v, _)| v).collect();
        let coeffs: Vec<f64> = vars_coeffs.iter().map(|&(_, c)| c).collect();
        self.constraints.push(LpConstraint { vars, coeffs, lb, ub });
    }

    /// Add a Steiner cut constraint: Σ y_a ≥ 1 for arcs crossing the cut.
    pub fn add_steiner_cut(&mut self, cut_arcs: &[ArcId]) {
        let vars_coeffs: Vec<(u32, f64)> = cut_arcs.iter()
            .map(|&aid| (aid, 1.0))
            .collect();
        self.add_constraint_raw(&vars_coeffs, 1.0, f64::INFINITY);
    }

    /// Add a general cut (constraint) to the LP.
    pub fn add_cut(&mut self, arc_ids: &[ArcId], coefficients: &[f64], rhs: f64) {
        let vars_coeffs: Vec<(u32, f64)> = arc_ids.iter()
            .zip(coefficients.iter())
            .map(|(&aid, &coeff)| (aid, coeff))
            .collect();
        self.add_constraint_raw(&vars_coeffs, rhs, f64::INFINITY);
    }

    /// Solve the LP relaxation using HiGHS.
    pub fn solve(&mut self) -> f64 {
        let mut pb = RowProblem::default();

        // Add variables: y_a ∈ [0, 1] with objective coefficient c(a)
        let cols: Vec<highs::Col> = self.objective.iter()
            .map(|&cost| pb.add_column(cost, 0.0..=1.0))
            .collect();

        // Add all constraints
        for constraint in &self.constraints {
            let row_entries: Vec<(highs::Col, f64)> = constraint.vars.iter()
                .zip(constraint.coeffs.iter())
                .map(|(&var_idx, &coeff)| (cols[var_idx as usize], coeff))
                .collect();

            let lb = constraint.lb;
            let ub = constraint.ub;

            if lb == f64::NEG_INFINITY {
                pb.add_row(..=ub, &row_entries);
            } else if ub == f64::INFINITY {
                pb.add_row(lb.., &row_entries);
            } else if (lb - ub).abs() < 1e-12 {
                pb.add_row(lb..=ub, &row_entries);
            } else {
                pb.add_row(lb..=ub, &row_entries);
            }
        }

        // Solve
        let model = pb.optimise(Sense::Minimise);
        let solved = model.solve();
        self.solve_count += 1;

        match solved.status() {
            HighsModelStatus::Optimal => {
                let sol = solved.get_solution();
                self.solution = sol.columns().to_vec();
                self.dual_bound = self.solution.iter()
                    .zip(self.objective.iter())
                    .map(|(&y, &c)| y * c)
                    .sum();
                self.status = LpStatus::Optimal;
            }
            HighsModelStatus::Infeasible | HighsModelStatus::ObjectiveBound
            | HighsModelStatus::ObjectiveTarget => {
                self.dual_bound = f64::INFINITY;
                self.status = LpStatus::Infeasible;
            }
            HighsModelStatus::Unbounded => {
                self.dual_bound = f64::NEG_INFINITY;
                self.status = LpStatus::Unbounded;
            }
            _ => {
                self.status = LpStatus::Error;
            }
        }

        self.dual_bound
    }

    pub fn get_solution(&self) -> &[f64] {
        &self.solution
    }

    pub fn get_dual_bound(&self) -> f64 {
        self.dual_bound
    }

    pub fn is_optimal(&self) -> bool {
        self.status == LpStatus::Optimal
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn build_simple_instance() -> (DirectedGraph, NodeId, Vec<NodeId>, Vec<NodeId>) {
        // Simple graph: root(1) -> 2(steiner) -> 3(terminal)
        //               root(1) -> 3(terminal) [expensive direct]
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        // Bidirectional arcs
        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(2, 3, 1.0); // 2
        g.add_arc(3, 2, 1.0); // 3
        g.add_arc(1, 3, 5.0); // 4
        g.add_arc(3, 1, 5.0); // 5

        let root = 1;
        let terminals = vec![3];
        let steiner_nodes = vec![2];
        (g, root, terminals, steiner_nodes)
    }

    #[test]
    fn test_lp_solves_optimal() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);

        // Add a Steiner cut: arcs leaving {1, 2} must sum ≥ 1
        // δ+({1,2}) = {arc 2: 2->3, arc 4: 1->3}
        lp.add_steiner_cut(&[2, 4]);

        let obj = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        assert!(obj >= 1.0 - 1e-6, "LP bound should be at least 1.0, got {}", obj);
        assert!(obj <= 2.0 + 1e-6, "LP bound should be at most 2.0, got {}", obj);
    }

    #[test]
    fn test_lp_flow_conservation() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        lp.add_steiner_cut(&[2, 4]);
        lp.solve();

        let y = lp.get_solution();

        // (3a) No flow into root
        let in_root: f64 = graph.delta_minus(root).iter()
            .map(|&(_, aid)| y[aid as usize])
            .sum();
        assert!(in_root.abs() < 1e-6, "Flow into root should be 0, got {}", in_root);

        // (3b) Flow into terminal 3 = 1
        let in_3: f64 = graph.delta_minus(3).iter()
            .map(|&(_, aid)| y[aid as usize])
            .sum();
        assert!((in_3 - 1.0).abs() < 1e-6, "Flow into terminal 3 should be 1, got {}", in_3);
    }

    #[test]
    fn test_lp_steiner_cut_tightens_bound() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);

        // Solve without cuts
        let bound_no_cuts = lp.solve();

        // Add cuts and resolve
        lp.add_steiner_cut(&[2, 4]);
        let bound_with_cuts = lp.solve();

        assert!(bound_with_cuts >= bound_no_cuts - 1e-9,
            "Adding cuts should not decrease the bound: {} < {}", bound_with_cuts, bound_no_cuts);
    }

    #[test]
    fn test_lp_multi_terminal() {
        // root(1) -> 2 -> 3(term), root(1) -> 4(term)
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(2, 3, 2.0); // 2
        g.add_arc(3, 2, 2.0); // 3
        g.add_arc(1, 4, 3.0); // 4
        g.add_arc(4, 1, 3.0); // 5

        let root = 1;
        let terminals = vec![3, 4];
        let steiner_nodes = vec![2];

        let mut lp = LpRelaxation::from_formulation(&g, root, &terminals, &steiner_nodes);

        // Cut for terminal 3: arcs leaving {1, 2} to {3, 4}
        lp.add_steiner_cut(&[2, 4]); // 2->3, 1->4
        // Cut for terminal 4: arcs leaving {1, 2, 3} to {4}
        lp.add_steiner_cut(&[4]); // 1->4

        let obj = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        // Optimal: 1->2(1) + 2->3(2) + 1->4(3) = 6
        assert!(obj >= 5.0 - 1e-6, "LP bound should be >= 5, got {}", obj);
    }
}
