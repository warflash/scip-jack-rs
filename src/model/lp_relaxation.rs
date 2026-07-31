use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use highs::{RowProblem, Col, Sense, HighsModelStatus, Model as HModel};

/// LP relaxation of the directed cut formulation for the Steiner arborescence problem.
///
/// Uses a **persistent HiGHS model**: the model is built once with structural
/// constraints and then incrementally modified (add rows, change column bounds)
/// without ever being rebuilt from scratch. This avoids O(constraints) rebuild
/// overhead on every LP solve.
pub struct LpRelaxation {
    pub num_vars: u32,
    pub objective: Vec<Cost>,
    pub solution: Vec<f64>,
    pub reduced_costs: Vec<f64>,
    pub dual_bound: f64,
    pub status: LpStatus,
    pub solve_count: u64,
    pub base_constraint_count: usize,

    model: Option<HModel>,
    cols: Vec<Col>,
    current_row_count: usize,
    base_var_lb: Vec<f64>,
    base_var_ub: Vec<f64>,
    pub var_lb: Vec<f64>,
    pub var_ub: Vec<f64>,
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
    /// Builds the persistent HiGHS model with:
    /// - Variables y_a in [0, 1] for each arc
    /// - Objective: min sum c(a) * y_a
    /// - Flow conservation constraints (3a, 3b, 3c)
    /// - Flow balance constraints (4)
    /// - Arc coupling constraints (5)
    /// - Anti-symmetry constraints: y_{uv} + y_{vu} <= 1 for each edge pair
    pub fn from_formulation(graph: &DirectedGraph, root: NodeId, terminals: &[NodeId], steiner_nodes: &[NodeId]) -> Self {
        let num_arcs = graph.num_arcs();
        let objective: Vec<Cost> = graph.arcs.iter().map(|a| a.cost).collect();

        let mut pb = RowProblem::default();
        let cols: Vec<Col> = (0..num_arcs as usize)
            .map(|i| pb.add_column(objective[i], 0.0..=1.0))
            .collect();

        // (3a) y(delta^-(root)) = 0
        let in_root: Vec<(Col, f64)> = graph.delta_minus(root).iter()
            .map(|&(_, arc_id)| (cols[arc_id as usize], 1.0))
            .collect();
        if !in_root.is_empty() {
            pb.add_row(0.0..=0.0, &in_root);
        }

        // (3b) y(delta^-(t)) = 1 for each terminal t != root
        for &t in terminals {
            if t == root { continue; }
            let in_t: Vec<(Col, f64)> = graph.delta_minus(t).iter()
                .map(|&(_, arc_id)| (cols[arc_id as usize], 1.0))
                .collect();
            if !in_t.is_empty() {
                pb.add_row(1.0..=1.0, &in_t);
            }
        }

        // (3c) y(delta^-(v)) <= 1 for each Steiner node v
        for &v in steiner_nodes {
            let in_v: Vec<(Col, f64)> = graph.delta_minus(v).iter()
                .map(|&(_, arc_id)| (cols[arc_id as usize], 1.0))
                .collect();
            if !in_v.is_empty() {
                pb.add_row(0.0..=1.0, &in_v);
            }
        }

        // (4) y(delta^-(v)) <= y(delta^+(v)) for each Steiner node v
        for &v in steiner_nodes {
            let mut row: Vec<(Col, f64)> = Vec::new();
            for &(_, arc_id) in graph.delta_minus(v) {
                row.push((cols[arc_id as usize], 1.0));
            }
            for &(_, arc_id) in graph.delta_plus(v) {
                row.push((cols[arc_id as usize], -1.0));
            }
            if !row.is_empty() {
                pb.add_row(..=0.0, &row);
            }
        }

        // (5) y(delta^-(v)) >= y_a for each a in delta^+(v), for Steiner nodes v
        // For dense graphs (>3000 arcs), these generate O(|S|*degree) rows which
        // makes the LP too large. In that case, omit them initially and rely on
        // the flow balance (4) + no-leaf + separation to enforce the property.
        // Constraint (5) is essential for LP strength - always include.
        {
            for &v in steiner_nodes {
                let in_arcs: Vec<ArcId> = graph.delta_minus(v).iter()
                    .map(|&(_, arc_id)| arc_id)
                    .collect();
                for &(_, out_arc) in graph.delta_plus(v) {
                    let mut row: Vec<(Col, f64)> = Vec::new();
                    for &in_arc in &in_arcs {
                        row.push((cols[in_arc as usize], 1.0));
                    }
                    row.push((cols[out_arc as usize], -1.0));
                    if !row.is_empty() {
                        pb.add_row(0.0.., &row);
                    }
                }
            }
        }

        // Anti-symmetry: y_{2i} + y_{2i+1} <= 1 for each undirected edge pair.
        // In a valid arborescence at most one direction of each edge is used.
        let num_pairs = num_arcs as usize / 2;
        for p in 0..num_pairs {
            let fwd = 2 * p;
            let rev = 2 * p + 1;
            pb.add_row(..=1.0, &[(cols[fwd], 1.0), (cols[rev], 1.0)]);
        }

        // TF singleton cuts (Terminal-Free degree constraints):
        // For dense graphs (> 4000 arcs), omit these (O(|S|*degree) rows).
        // The no-leaf constraint covers the same property, and TF set cut
        // separation handles the non-singleton case dynamically.
        if num_arcs < 4000 {
            for &v in steiner_nodes {
                let in_arcs: Vec<ArcId> = graph.delta_minus(v).iter().map(|&(_, a)| a).collect();
                let out_arcs: Vec<ArcId> = graph.delta_plus(v).iter().map(|&(_, a)| a).collect();
                let all_arcs: Vec<ArcId> = in_arcs.iter().chain(out_arcs.iter()).copied().collect();
                if all_arcs.len() < 4 { continue; }

                let mut incident_edges: Vec<usize> = all_arcs.iter()
                    .map(|&a| (a as usize) / 2)
                    .collect();
                incident_edges.sort();
                incident_edges.dedup();

                for &edge_idx in &incident_edges {
                    let fwd = (2 * edge_idx) as ArcId;
                    let rev = (2 * edge_idx + 1) as ArcId;

                    let mut row: Vec<(Col, f64)> = Vec::new();
                    for &a in &all_arcs {
                        if a == fwd || a == rev {
                            row.push((cols[a as usize], -1.0));
                        } else {
                            row.push((cols[a as usize], 1.0));
                        }
                    }
                    if !row.is_empty() {
                        pb.add_row(0.0.., &row);
                    }
                }
            }
        }

        // FC-BCR: Forest-Closed BCR strengthening (Section 11.1 of research memo)
        //
        // Add activation variables s_v for each node. A tree on k used vertices
        // has exactly k-1 edges; a non-terminal with s_v > 0 must have degree >= 2.
        // These constraints attack fractional solutions that terminal cuts alone
        // cannot see.

        // Create activation variable columns: s_v in [0,1], zero cost
        let all_nodes: Vec<NodeId> = graph.nodes.iter().map(|n| n.id).collect();
        let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
        let max_node_id = all_nodes.iter().copied().max().unwrap_or(0) as usize;

        // Map node ID -> column index for s_v (offset by num_arcs)
        let mut s_cols: Vec<Option<Col>> = vec![None; max_node_id + 1];
        for &nid in &all_nodes {
            let is_terminal = terminal_set.contains(&nid) || nid == root;
            let (lb, ub) = if is_terminal { (1.0, 1.0) } else { (0.0, 1.0) };
            let col = pb.add_column(0.0, lb..=ub);
            s_cols[nid as usize] = Some(col);
        }

        // Counting constraint: sum_edges(y_fwd + y_rev) = sum_nodes(s_v) - 1
        // Rewritten: sum_edges(y_fwd + y_rev) - sum_nodes(s_v) = -1
        {
            let mut row: Vec<(Col, f64)> = Vec::new();
            for p in 0..num_pairs {
                row.push((cols[2 * p], 1.0));
                row.push((cols[2 * p + 1], 1.0));
            }
            for &nid in &all_nodes {
                if let Some(col) = s_cols[nid as usize] {
                    row.push((col, -1.0));
                }
            }
            pb.add_row(-1.0..=-1.0, &row);
        }

        // No-leaf constraint: for each Steiner node v:
        //   x(delta(v)) >= 2 * s_v
        // i.e., sum of all arcs incident to v (in undirected sense) >= 2 * s_v
        // Rewritten: sum_incident_arcs(y_a) - 2*s_v >= 0
        for &v in steiner_nodes {
            if let Some(sv_col) = s_cols[v as usize] {
                let in_arcs: Vec<ArcId> = graph.delta_minus(v).iter().map(|&(_, a)| a).collect();
                let out_arcs: Vec<ArcId> = graph.delta_plus(v).iter().map(|&(_, a)| a).collect();

                let mut row: Vec<(Col, f64)> = Vec::new();
                for &a in &in_arcs {
                    row.push((cols[a as usize], 1.0));
                }
                for &a in &out_arcs {
                    row.push((cols[a as usize], 1.0));
                }
                row.push((sv_col, -2.0));
                if !row.is_empty() {
                    pb.add_row(0.0.., &row);
                }
            }
        }

        // Edge-vertex coupling: for each edge {u,v} (arc pair 2i, 2i+1):
        //   y_{uv} + y_{vu} <= s_u   AND   y_{uv} + y_{vu} <= s_v
        for p in 0..num_pairs {
            let fwd_arc = &graph.arcs[2 * p];
            let u = fwd_arc.tail;
            let v = fwd_arc.head;

            if let Some(su_col) = s_cols[u as usize] {
                // y_{uv} + y_{vu} - s_u <= 0
                pb.add_row(..=0.0, &[
                    (cols[2 * p], 1.0),
                    (cols[2 * p + 1], 1.0),
                    (su_col, -1.0),
                ]);
            }
            if let Some(sv_col) = s_cols[v as usize] {
                // y_{uv} + y_{vu} - s_v <= 0
                pb.add_row(..=0.0, &[
                    (cols[2 * p], 1.0),
                    (cols[2 * p + 1], 1.0),
                    (sv_col, -1.0),
                ]);
            }
        }

        let base_rows = pb.num_rows();

        let mut model = pb.optimise(Sense::Minimise);
        model.set_option("output_flag", false);

        let var_lb = vec![0.0; num_arcs as usize];
        let var_ub = vec![1.0; num_arcs as usize];

        let lp = Self {
            num_vars: num_arcs,
            objective,
            solution: vec![0.0; num_arcs as usize],
            reduced_costs: vec![0.0; num_arcs as usize],
            dual_bound: f64::NEG_INFINITY,
            status: LpStatus::NotSolved,
            solve_count: 0,
            base_constraint_count: base_rows,
            model: Some(model),
            cols,
            current_row_count: base_rows,
            base_var_lb: var_lb.clone(),
            base_var_ub: var_ub.clone(),
            var_lb,
            var_ub,
        };

        lp
    }

    /// Mark current state as the base (after adding global cuts and fixed arcs).
    pub fn snapshot_base(&mut self) {
        self.base_constraint_count = self.current_row_count;
        self.base_var_lb = self.var_lb.clone();
        self.base_var_ub = self.var_ub.clone();
    }

    /// Reset column bounds to the base state for a new B&B node.
    /// All cuts added remain (they are global); only variable fixings are reverted.
    pub fn reset_to_base(&mut self) {
        let model = self.model.as_mut().unwrap();
        for i in 0..self.num_vars as usize {
            let blb = self.base_var_lb[i];
            let bub = self.base_var_ub[i];
            if (self.var_lb[i] - blb).abs() > 1e-12 || (self.var_ub[i] - bub).abs() > 1e-12 {
                model.change_column_bounds(self.cols[i], blb..=bub);
                self.var_lb[i] = blb;
                self.var_ub[i] = bub;
            }
        }
        self.status = LpStatus::NotSolved;
    }

    /// Add a Steiner cut: sum y_a >= 1 for arcs crossing the cut.
    pub fn add_steiner_cut(&mut self, cut_arcs: &[ArcId]) {
        let entries: Vec<(Col, f64)> = cut_arcs.iter()
            .map(|&aid| (self.cols[aid as usize], 1.0))
            .collect();
        let model = self.model.as_mut().unwrap();
        model.add_row(1.0.., entries);
        self.current_row_count += 1;
    }

    /// Add a general cut (constraint) to the LP.
    pub fn add_cut(&mut self, arc_ids: &[ArcId], coefficients: &[f64], rhs: f64) {
        let entries: Vec<(Col, f64)> = arc_ids.iter()
            .zip(coefficients.iter())
            .map(|(&aid, &coeff)| (self.cols[aid as usize], coeff))
            .collect();
        let model = self.model.as_mut().unwrap();
        model.add_row(rhs.., entries);
        self.current_row_count += 1;
    }

    /// Add a cycle inequality: sum (y_{uv} + y_{vu}) <= |C|-1 for arc pairs in cycle C.
    pub fn add_cycle_cut(&mut self, arc_pairs: &[(ArcId, ArcId)]) {
        let rhs = arc_pairs.len() as f64 - 1.0;
        let entries: Vec<(Col, f64)> = arc_pairs.iter()
            .flat_map(|&(fwd, rev)| {
                [(self.cols[fwd as usize], 1.0), (self.cols[rev as usize], 1.0)]
            })
            .collect();
        let model = self.model.as_mut().unwrap();
        model.add_row(..=rhs, entries);
        self.current_row_count += 1;
    }

    /// Fix a variable to a specific value by tightening its bounds.
    pub fn fix_variable(&mut self, arc_id: ArcId, value: f64) {
        let idx = arc_id as usize;
        if idx < self.var_lb.len() {
            self.var_lb[idx] = value;
            self.var_ub[idx] = value;
            let model = self.model.as_mut().unwrap();
            model.change_column_bounds(self.cols[idx], value..=value);
        }
    }

    /// Change variable bounds (for strong branching restore).
    pub fn change_variable_bounds(&mut self, arc_id: ArcId, lb: f64, ub: f64) {
        let idx = arc_id as usize;
        if idx < self.var_lb.len() {
            self.var_lb[idx] = lb;
            self.var_ub[idx] = ub;
            let model = self.model.as_mut().unwrap();
            model.change_column_bounds(self.cols[idx], lb..=ub);
        }
    }

    /// Solve the LP using the persistent HiGHS model.
    ///
    /// The model is NOT rebuilt from scratch; HiGHS re-solves incrementally
    /// using its internal warm-start from the previous basis.
    pub fn solve(&mut self) -> f64 {
        let mut model = self.model.take().unwrap();

        if self.solve_count > 0 && !self.solution.is_empty() && self.solution.len() == model.num_cols() {
            model.set_solution(Some(&self.solution), None, None, None);
        }

        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            model.solve()
        }));

        let solved = match solve_result {
            Ok(s) => s,
            Err(_) => {
                self.status = LpStatus::Error;
                self.dual_bound = f64::INFINITY;
                return f64::INFINITY;
            }
        };

        self.solve_count += 1;

        match solved.status() {
            HighsModelStatus::Optimal => {
                let sol = solved.get_solution();
                self.solution = sol.columns().to_vec();
                self.reduced_costs = sol.dual_columns().to_vec();
                self.dual_bound = self.solution.iter()
                    .take(self.num_vars as usize)
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

        self.model = Some(solved.into());
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
        self.current_row_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn build_simple_instance() -> (DirectedGraph, NodeId, Vec<NodeId>, Vec<NodeId>) {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 1.0);
        g.add_arc(3, 2, 1.0);
        g.add_arc(1, 3, 5.0);
        g.add_arc(3, 1, 5.0);

        let root = 1;
        let terminals = vec![3];
        let steiner_nodes = vec![2];
        (g, root, terminals, steiner_nodes)
    }

    #[test]
    fn test_lp_solves_optimal() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);

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

        let in_root: f64 = graph.delta_minus(root).iter()
            .map(|&(_, aid)| y[aid as usize])
            .sum();
        assert!(in_root.abs() < 1e-6, "Flow into root should be 0, got {}", in_root);

        let in_3: f64 = graph.delta_minus(3).iter()
            .map(|&(_, aid)| y[aid as usize])
            .sum();
        assert!((in_3 - 1.0).abs() < 1e-6, "Flow into terminal 3 should be 1, got {}", in_3);
    }

    #[test]
    fn test_lp_steiner_cut_tightens_bound() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);

        let bound_no_cuts = lp.solve();

        lp.add_steiner_cut(&[2, 4]);
        let bound_with_cuts = lp.solve();

        assert!(bound_with_cuts >= bound_no_cuts - 1e-9,
            "Adding cuts should not decrease the bound: {} < {}", bound_with_cuts, bound_no_cuts);
    }

    #[test]
    fn test_lp_multi_terminal() {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 2.0);
        g.add_arc(3, 2, 2.0);
        g.add_arc(1, 4, 3.0);
        g.add_arc(4, 1, 3.0);

        let root = 1;
        let terminals = vec![3, 4];
        let steiner_nodes = vec![2];

        let mut lp = LpRelaxation::from_formulation(&g, root, &terminals, &steiner_nodes);

        lp.add_steiner_cut(&[2, 4]);
        lp.add_steiner_cut(&[4]);

        let obj = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        assert!(obj >= 5.0 - 1e-6, "LP bound should be >= 5, got {}", obj);
    }
}
