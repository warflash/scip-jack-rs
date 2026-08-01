//! LP relaxation of the directed cut formulation, with a managed global cut pool.
//!
//! # Why the model is described as data
//!
//! Separated cuts are globally valid, so the natural implementation keeps one
//! persistent HiGHS model and appends rows to it. Left alone, that model grows
//! without bound: on SteinLib `c13` the branch-and-cut appended 7,635 cuts to a
//! 1,236-variable problem, reaching 11,821 rows and 176 ms per solve, and 98% of
//! total runtime was spent inside the LP.
//!
//! Cuts therefore need to be *removed* once they stop binding, and the HiGHS
//! wrapper exposes no row deletion. So this type owns a plain-data description of
//! every column and row and treats the HiGHS handle as a cache it can rebuild.
//! Cuts that sit slack for several consecutive solves are aged out of the pool and
//! the model is rebuilt without them. Rebuilds cost one model construction and
//! discard the simplex basis, so they are triggered only when the row count
//! actually exceeds its budget.

use crate::graph::{ArcId, Cost, DirectedGraph, NodeId};
use highs::{Col, HighsModelStatus, Model as HModel, RowProblem, Sense};

/// A row: `lo <= sum coeff * x <= hi`, with infinite bounds allowed.
#[derive(Debug, Clone)]
struct RowData {
    entries: Vec<(u32, f64)>,
    lo: f64,
    hi: f64,
}

#[derive(Debug, Clone)]
struct CutRow {
    row: RowData,
    /// Consecutive solves this cut has been slack for.
    age: u32,
    /// Index into `lazy` when this row came from the lazy structural pool.
    lazy_index: Option<u32>,
}

/// A cut is considered slack when its activity is this far from the binding side.
const SLACK_EPS: f64 = 1e-6;

pub struct LpRelaxation {
    pub num_vars: u32,
    pub objective: Vec<Cost>,
    pub solution: Vec<f64>,
    pub reduced_costs: Vec<f64>,
    pub dual_bound: f64,
    pub status: LpStatus,
    pub solve_count: u64,
    pub base_constraint_count: usize,
    pub solve_time_secs: f64,
    /// Number of model rebuilds triggered by cut-pool pruning.
    pub rebuilds: u64,

    /// Column description: (objective coefficient, lower bound, upper bound).
    col_cost: Vec<f64>,
    col_lb_base: Vec<f64>,
    col_ub_base: Vec<f64>,
    /// Structural rows; never removed.
    structural: Vec<RowData>,
    /// Valid structural rows held back and added only when violated. These are
    /// the two families whose count is proportional to the arc count — the
    /// Steiner continuation rows and the edge-vertex coupling rows. Keeping all
    /// of them resident makes the model an order of magnitude larger than the
    /// number of variables while only a handful are ever binding.
    lazy: Vec<RowData>,
    lazy_resident: Vec<bool>,
    /// Separated cuts, subject to ageing.
    cuts: Vec<CutRow>,
    /// Row budget before pruning is attempted.
    row_budget: usize,

    /// Set by [`LpRelaxation::rebuild`] and cleared by the next solve. A model
    /// with no basis is a cold start, and cold starts want presolve; warm ones do
    /// not, because presolve runs afresh on every `run()` and throws the basis
    /// away.
    cold: bool,
    /// Wall-clock seconds still available to the search, or infinity. A root
    /// model seeded with a few thousand connectivity rows is a genuinely hard
    /// LP — on PACE instance151 one solve ran for 33 seconds inside a 10-second
    /// budget, and the loop only checks the clock between solves, so the backend
    /// needs its own stop.
    ///
    /// HiGHS compares `time_limit` against a timer that *accumulates* across
    /// `run()` calls on the same model, so the option must be set to the total
    /// time the model is allowed to have consumed by the end of this solve, not
    /// to the length of this solve. Setting the latter is worse than setting
    /// nothing: once the accumulated time passes it, every further solve returns
    /// immediately with a non-optimal status, the node is abandoned for want of a
    /// valid bound, and the search stops. On SteinLib e18 that ended the run with
    /// ten of its twenty-two seconds unspent and the dual bound four percent
    /// short of where the previous solve had already been heading.
    pub time_limit_secs: f64,
    /// Last values actually pushed to HiGHS.
    presolve_on: bool,
    armed_limit: f64,

    model: Option<HModel>,
    cols: Vec<Col>,
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

/// Accumulates the model description before it is handed to HiGHS.
struct Builder {
    col_cost: Vec<f64>,
    col_lb: Vec<f64>,
    col_ub: Vec<f64>,
    rows: Vec<RowData>,
    lazy: Vec<RowData>,
}

impl Builder {
    fn new() -> Self {
        Self {
            col_cost: Vec::new(),
            col_lb: Vec::new(),
            col_ub: Vec::new(),
            rows: Vec::new(),
            lazy: Vec::new(),
        }
    }

    fn add_col(&mut self, cost: f64, lb: f64, ub: f64) -> u32 {
        self.col_cost.push(cost);
        self.col_lb.push(lb);
        self.col_ub.push(ub);
        (self.col_cost.len() - 1) as u32
    }

    fn add_row(&mut self, lo: f64, hi: f64, entries: Vec<(u32, f64)>) {
        if entries.is_empty() {
            return;
        }
        self.rows.push(RowData { entries, lo, hi });
    }

    fn add_lazy(&mut self, lo: f64, hi: f64, entries: Vec<(u32, f64)>) {
        if entries.is_empty() {
            return;
        }
        self.lazy.push(RowData { entries, lo, hi });
    }
}

impl LpRelaxation {
    /// Build the rooted directed-cut model.
    ///
    /// Structural rows:
    /// - `y(delta^-(r)) = 0`, `y(delta^-(t)) = 1` for terminals, `y(delta^-(v)) <= 1` else;
    /// - flow balance `y(delta^-(v)) <= y(delta^+(v))` for Steiner nodes;
    /// - continuation `y(delta^-(v)) >= y_a` for every `a` leaving a Steiner node;
    /// - anti-symmetry `y_uv + y_vu <= 1`;
    /// - the FC-BCR block (activation variables, vertex counting, no-leaf,
    ///   edge-vertex coupling) from section 11.1 of the research memo.
    pub fn from_formulation(
        graph: &DirectedGraph,
        root: NodeId,
        terminals: &[NodeId],
        steiner_nodes: &[NodeId],
    ) -> Self {
        let num_arcs = graph.num_arcs();
        let objective: Vec<Cost> = graph.arcs.iter().map(|a| a.cost).collect();
        let num_pairs = num_arcs as usize / 2;

        let mut b = Builder::new();
        for i in 0..num_arcs as usize {
            b.add_col(objective[i], 0.0, 1.0);
        }

        let in_arcs = |v: NodeId| -> Vec<u32> {
            graph.delta_minus(v).iter().map(|&(_, a)| a).collect()
        };
        let out_arcs = |v: NodeId| -> Vec<u32> {
            graph.delta_plus(v).iter().map(|&(_, a)| a).collect()
        };

        // (3a) no arc enters the root.
        b.add_row(0.0, 0.0, in_arcs(root).into_iter().map(|a| (a, 1.0)).collect());

        // (3b) exactly one arc enters each non-root terminal.
        for &t in terminals {
            if t == root {
                continue;
            }
            b.add_row(1.0, 1.0, in_arcs(t).into_iter().map(|a| (a, 1.0)).collect());
        }

        // (3c) at most one arc enters a Steiner node.
        for &v in steiner_nodes {
            b.add_row(0.0, 1.0, in_arcs(v).into_iter().map(|a| (a, 1.0)).collect());
        }

        // (4) flow balance: an entered Steiner node must be left.
        for &v in steiner_nodes {
            let mut row: Vec<(u32, f64)> = in_arcs(v).into_iter().map(|a| (a, 1.0)).collect();
            row.extend(out_arcs(v).into_iter().map(|a| (a, -1.0)));
            b.add_row(f64::NEG_INFINITY, 0.0, row);
        }

        // (5) continuation: an arc may leave a Steiner node only if one enters.
        // One row per arc, each of width `indeg + 1`; separated on demand.
        for &v in steiner_nodes {
            let ins = in_arcs(v);
            for out in out_arcs(v) {
                let mut row: Vec<(u32, f64)> = ins.iter().map(|&a| (a, 1.0)).collect();
                row.push((out, -1.0));
                b.add_lazy(0.0, f64::INFINITY, row);
            }
        }

        // Anti-symmetry: at most one orientation of each edge is used.
        //
        // These are resident, not held back. Holding them back was tried and is
        // measurably worse: on SteinLib e18 the lazy version solved a model with
        // half the rows at 232 ms against the resident model's 170 ms, and got
        // half as many cut rounds in the same budget. They bind often enough that
        // re-admitting them a batch at a time disturbs the basis more than the
        // rows cost to carry.
        for p in 0..num_pairs {
            b.add_row(f64::NEG_INFINITY, 1.0, vec![(2 * p as u32, 1.0), (2 * p as u32 + 1, 1.0)]);
        }

        // FC-BCR block.
        let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
        let max_node_id = graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let mut s_col: Vec<Option<u32>> = vec![None; max_node_id + 1];
        for node in &graph.nodes {
            let fixed = terminal_set.contains(&node.id) || node.id == root;
            let (lb, ub) = if fixed { (1.0, 1.0) } else { (0.0, 1.0) };
            s_col[node.id as usize] = Some(b.add_col(0.0, lb, ub));
        }

        // A tree on k used vertices has exactly k-1 edges. This single dense row
        // carries a large share of the FC-BCR strength: without it the root gaps
        // on c09/c13/c18 widen from 0% to 1.2%/4.8%/3.5%.
        {
            let mut row: Vec<(u32, f64)> = Vec::with_capacity(num_arcs as usize + graph.nodes.len());
            for a in 0..num_arcs {
                row.push((a, 1.0));
            }
            for node in &graph.nodes {
                if let Some(c) = s_col[node.id as usize] {
                    row.push((c, -1.0));
                }
            }
            b.add_row(-1.0, -1.0, row);
        }

        // No-leaf: a used Steiner node has undirected degree at least two. Valid
        // for inclusion-minimal trees, and with non-negative costs some optimum is
        // inclusion-minimal.
        for &v in steiner_nodes {
            if let Some(sv) = s_col[v as usize] {
                let mut row: Vec<(u32, f64)> = in_arcs(v).into_iter().map(|a| (a, 1.0)).collect();
                row.extend(out_arcs(v).into_iter().map(|a| (a, 1.0)));
                row.push((sv, -2.0));
                b.add_row(0.0, f64::INFINITY, row);
            }
        }

        // Edge-vertex coupling: using an edge activates both endpoints.
        // Two rows per edge; separated on demand.
        for p in 0..num_pairs {
            let arc = &graph.arcs[2 * p];
            for endpoint in [arc.tail, arc.head] {
                if let Some(sc) = s_col[endpoint as usize] {
                    b.add_lazy(
                        f64::NEG_INFINITY,
                        0.0,
                        vec![(2 * p as u32, 1.0), (2 * p as u32 + 1, 1.0), (sc, -1.0)],
                    );
                }
            }
        }

        let structural_count = b.rows.len();
        // Budget the *separated* rows against the variable count. Sizing this too
        // tightly evicts useful Steiner cuts that then have to be rediscovered by
        // max-flow, which costs far more than the rows saved.
        // Keep the cut pool proportional to the model. A flat floor of a few
        // thousand rows is no constraint at all on a 400-arc instance, and the
        // pool grows to several times the number of variables before anything is
        // evicted — which is exactly where the LP starts costing milliseconds
        // per solve on a problem that should take microseconds.
        let row_budget = structural_count + (2 * num_arcs as usize).max(1000);
        let lazy_count = b.lazy.len();

        let var_lb = vec![0.0; num_arcs as usize];
        let var_ub = vec![1.0; num_arcs as usize];

        let mut lp = Self {
            num_vars: num_arcs,
            objective,
            solution: vec![0.0; b.col_cost.len()],
            reduced_costs: vec![0.0; b.col_cost.len()],
            dual_bound: f64::NEG_INFINITY,
            status: LpStatus::NotSolved,
            solve_count: 0,
            base_constraint_count: structural_count,
            solve_time_secs: 0.0,
            rebuilds: 0,
            col_cost: b.col_cost,
            col_lb_base: b.col_lb,
            col_ub_base: b.col_ub,
            structural: b.rows,
            lazy: b.lazy,
            lazy_resident: vec![false; lazy_count],
            cuts: Vec::new(),
            row_budget,
            cold: true,
            time_limit_secs: f64::INFINITY,
            presolve_on: false,
            armed_limit: f64::INFINITY,
            model: None,
            cols: Vec::new(),
            base_var_lb: var_lb.clone(),
            base_var_ub: var_ub.clone(),
            var_lb,
            var_ub,
        };
        lp.rebuild();
        lp
    }

    /// Recreate the HiGHS model from the current data description.
    fn rebuild(&mut self) {
        let mut pb = RowProblem::default();
        let cols: Vec<Col> = (0..self.col_cost.len())
            .map(|i| {
                let (lb, ub) = self.current_col_bounds(i);
                pb.add_column(self.col_cost[i], lb..=ub)
            })
            .collect();

        for row in self.structural.iter().chain(self.cuts.iter().map(|c| &c.row)) {
            let entries: Vec<(Col, f64)> =
                row.entries.iter().map(|&(c, v)| (cols[c as usize], v)).collect();
            pb.add_row(row.lo..=row.hi, &entries);
        }

        let mut model = pb.optimise(Sense::Minimise);
        model.set_option("output_flag", false);
        self.cols = cols;
        self.model = Some(model);
        self.rebuilds += 1;
        self.cold = true;
    }

    /// Bounds currently in force for a column, honouring branching fixings.
    fn current_col_bounds(&self, i: usize) -> (f64, f64) {
        if i < self.var_lb.len() {
            (self.var_lb[i], self.var_ub[i])
        } else {
            (self.col_lb_base[i], self.col_ub_base[i])
        }
    }

    /// Mark the current state as the base for per-node bound resets.
    pub fn snapshot_base(&mut self) {
        self.base_constraint_count = self.num_constraints();
        self.base_var_lb = self.var_lb.clone();
        self.base_var_ub = self.var_ub.clone();
    }

    /// Restore column bounds to the base state for a new branch-and-bound node.
    /// Cuts are global and stay in place.
    pub fn reset_to_base(&mut self) {
        let model = self.model.as_mut().unwrap();
        for i in 0..self.num_vars as usize {
            let (blb, bub) = (self.base_var_lb[i], self.base_var_ub[i]);
            if (self.var_lb[i] - blb).abs() > 1e-12 || (self.var_ub[i] - bub).abs() > 1e-12 {
                model.change_column_bounds(self.cols[i], blb..=bub);
                self.var_lb[i] = blb;
                self.var_ub[i] = bub;
            }
        }
        self.status = LpStatus::NotSolved;
    }

    fn push_cut(&mut self, row: RowData) {
        self.push_cut_tagged(row, None);
    }

    fn push_cut_tagged(&mut self, row: RowData, lazy_index: Option<u32>) {
        {
            let entries: Vec<(Col, f64)> =
                row.entries.iter().map(|&(c, v)| (self.cols[c as usize], v)).collect();
            let model = self.model.as_mut().unwrap();
            model.add_row(row.lo..=row.hi, entries);
        }
        self.cuts.push(CutRow { row, age: 0, lazy_index });
    }

    /// Activity of a row at the current solution.
    fn activity(&self, row: &RowData) -> f64 {
        row.entries
            .iter()
            .map(|&(c, v)| v * self.solution.get(c as usize).copied().unwrap_or(0.0))
            .sum()
    }

    /// Add any held-back structural rows the current solution violates.
    ///
    /// These rows are valid for the model, so leaving them out only ever weakens
    /// the relaxation — the dual bound stays a bound throughout. Returns how many
    /// were brought in.
    pub fn separate_structural(&mut self, max_add: usize) -> usize {
        if self.status != LpStatus::Optimal || self.lazy.is_empty() {
            return 0;
        }
        let mut violated: Vec<(f64, u32)> = Vec::new();
        for i in 0..self.lazy.len() {
            if self.lazy_resident[i] {
                continue;
            }
            let row = &self.lazy[i];
            let act = self.activity(row);
            let v = if row.lo.is_finite() && act < row.lo - SLACK_EPS {
                row.lo - act
            } else if row.hi.is_finite() && act > row.hi + SLACK_EPS {
                act - row.hi
            } else {
                continue;
            };
            violated.push((v, i as u32));
        }
        if violated.is_empty() {
            return 0;
        }
        // Most violated first: those move the bound the furthest per row added.
        violated.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
        violated.truncate(max_add);
        for &(_, i) in &violated {
            self.lazy_resident[i as usize] = true;
            let row = self.lazy[i as usize].clone();
            self.push_cut_tagged(row, Some(i));
        }
        violated.len()
    }

    /// Register a Steiner cut in the held-back pool instead of the model.
    ///
    /// Used for the dual-ascent seed, which is thousands of rows wide. Putting
    /// them straight into the model makes the first solve a cold simplex on a
    /// problem several times larger than the structural one — 19 seconds on PACE
    /// instance199, which is the entire budget. Held back, they are pulled in by
    /// [`LpRelaxation::separate_structural`] in geometric batches against a warm
    /// basis, and only the ones the current point actually violates.
    pub fn add_lazy_steiner_cut(&mut self, cut_arcs: &[ArcId]) {
        if cut_arcs.is_empty() {
            return;
        }
        self.lazy.push(RowData {
            entries: cut_arcs.iter().map(|&a| (a, 1.0)).collect(),
            lo: 1.0,
            hi: f64::INFINITY,
        });
        self.lazy_resident.push(false);
    }

    /// Add a Steiner cut `sum_{a in cut} y_a >= 1`.
    pub fn add_steiner_cut(&mut self, cut_arcs: &[ArcId]) {
        let entries = cut_arcs.iter().map(|&a| (a, 1.0)).collect();
        self.push_cut(RowData { entries, lo: 1.0, hi: f64::INFINITY });
    }

    /// Add a general `>= rhs` cut over arc variables.
    pub fn add_cut(&mut self, arc_ids: &[ArcId], coefficients: &[f64], rhs: f64) {
        let entries = arc_ids.iter().zip(coefficients).map(|(&a, &c)| (a, c)).collect();
        self.push_cut(RowData { entries, lo: rhs, hi: f64::INFINITY });
    }

    /// Add a cycle inequality `sum_{e in C} (y_uv + y_vu) <= |C| - 1`.
    pub fn add_cycle_cut(&mut self, arc_pairs: &[(ArcId, ArcId)]) {
        let rhs = arc_pairs.len() as f64 - 1.0;
        let entries = arc_pairs
            .iter()
            .flat_map(|&(f, r)| [(f, 1.0), (r, 1.0)])
            .collect();
        self.push_cut(RowData { entries, lo: f64::NEG_INFINITY, hi: rhs });
    }

    /// Age the cut pool against the latest solution and, if the model has grown
    /// past its budget, drop the stale cuts and rebuild.
    ///
    /// Returns the number of cuts discarded.
    pub fn prune_cuts(&mut self) -> usize {
        if self.status != LpStatus::Optimal {
            return 0;
        }
        for idx in 0..self.cuts.len() {
            let activity = self.activity(&self.cuts[idx].row);
            let row = &self.cuts[idx].row;
            let binding = (row.lo.is_finite() && activity <= row.lo + SLACK_EPS)
                || (row.hi.is_finite() && activity >= row.hi - SLACK_EPS);
            let cut = &mut self.cuts[idx];
            if binding {
                cut.age = 0;
            } else {
                cut.age += 1;
            }
        }

        if self.num_constraints() <= self.row_budget {
            return 0;
        }

        // Structural rows brought in from the lazy pool stay for good. They are
        // part of the relaxation rather than optional strengthening, and evicting
        // them only to re-separate them a few solves later costs both the extra
        // solves and a weaker bound in between.
        let protected = self.structural.len()
            + self.cuts.iter().filter(|c| c.lazy_index.is_some()).count();
        // Prune down to a low-water mark rather than to the budget itself.
        // Evicting only the rows that happen to be over the line leaves the model
        // back over it after the next few separations, so every solve triggers a
        // rebuild and every rebuild throws away the simplex basis: on PACE
        // instance099 that was 163 rebuilds in 299 solves and 12 ms a solve on a
        // 428-variable problem.
        let keep = self.row_budget.saturating_sub(protected) / 2;

        let mut evictable: Vec<(u32, usize)> = self
            .cuts
            .iter()
            .enumerate()
            .filter(|(_, c)| c.lazy_index.is_none() && c.age > 0)
            .map(|(i, c)| (c.age, i))
            .collect();
        if evictable.is_empty() {
            return 0;
        }
        // Oldest first: those have gone longest without binding.
        evictable.sort_by(|a, b| b.0.cmp(&a.0));

        let live = self.cuts.len() - evictable.len();
        let drop_count = evictable.len().saturating_sub(keep.saturating_sub(live.min(keep)));
        if drop_count == 0 {
            return 0;
        }
        let mut doomed = vec![false; self.cuts.len()];
        for &(_, i) in evictable.iter().take(drop_count) {
            doomed[i] = true;
        }
        let mut i = 0;
        self.cuts.retain(|_| {
            let keep_it = !doomed[i];
            i += 1;
            keep_it
        });

        self.rebuild();
        self.status = LpStatus::NotSolved;
        drop_count
    }

    pub fn solve(&mut self) -> f64 {
        let timer = std::time::Instant::now();
        let value = self.solve_inner();
        self.solve_time_secs += timer.elapsed().as_secs_f64();
        value
    }

    fn solve_inner(&mut self) -> f64 {
        // Note: do *not* push the previous primal point back in with
        // `set_solution`. HiGHS keeps its own simplex basis across `solve` calls
        // on the same model, and supplying a primal-only start discards that
        // basis in favour of a crash start — the opposite of a warm start. Doing
        // so cost a factor of six on SteinLib `c13`.
        let mut model = self.model.take().unwrap();
        // Presolve is worth its cost exactly once per model: on the cold solve
        // after a rebuild, where there is no basis to preserve. Afterwards it
        // runs on every `run()` call and discards the basis it should have been
        // reusing, which on `c13` cost a factor of six.
        //
        // Options are pushed only when they actually change. HiGHS treats an
        // option assignment as a model event, and re-asserting the same clock
        // before every solve is not free.
        if self.cold != self.presolve_on {
            model.set_option("presolve", if self.cold { "on" } else { "off" });
            self.presolve_on = self.cold;
        }
        // Re-pushed only when the budget genuinely tightens. HiGHS treats an
        // option assignment as a model event and drops the simplex state, so
        // re-asserting a clock that has barely moved costs the warm start that
        // makes an incremental cut loop affordable at all.
        if self.time_limit_secs.is_finite() {
            let budget = self.solve_time_secs + self.time_limit_secs.max(0.01);
            if budget < self.armed_limit - 1.0 {
                model.set_option("time_limit", budget);
                self.armed_limit = budget;
            }
        }
        self.cold = false;

        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| model.solve()));

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
                self.dual_bound = self
                    .solution
                    .iter()
                    .take(self.num_vars as usize)
                    .zip(self.objective.iter())
                    .map(|(&y, &c)| y * c)
                    .sum();
                self.status = LpStatus::Optimal;
            }
            HighsModelStatus::Infeasible
            | HighsModelStatus::ObjectiveBound
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

    /// Fix a variable by tightening both of its bounds.
    pub fn fix_variable(&mut self, arc_id: ArcId, value: f64) {
        self.change_variable_bounds(arc_id, value, value);
    }

    pub fn change_variable_bounds(&mut self, arc_id: ArcId, lb: f64, ub: f64) {
        let idx = arc_id as usize;
        if idx < self.var_lb.len() {
            self.var_lb[idx] = lb;
            self.var_ub[idx] = ub;
            let model = self.model.as_mut().unwrap();
            model.change_column_bounds(self.cols[idx], lb..=ub);
        }
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
        self.structural.len() + self.cuts.len()
    }

    pub fn num_cuts(&self) -> usize {
        self.cuts.len()
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

        (g, 1, vec![3], vec![2])
    }

    #[test]
    fn test_lp_solves_optimal() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        lp.add_steiner_cut(&[2, 4]);

        let obj = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        assert!(obj >= 1.0 - 1e-6, "LP bound should be at least 1.0, got {obj}");
        assert!(obj <= 2.0 + 1e-6, "LP bound should be at most 2.0, got {obj}");
    }

    #[test]
    fn test_lp_flow_conservation() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        lp.add_steiner_cut(&[2, 4]);
        lp.solve();

        let y = lp.get_solution();
        let in_root: f64 = graph.delta_minus(root).iter().map(|&(_, a)| y[a as usize]).sum();
        assert!(in_root.abs() < 1e-6, "Flow into root should be 0, got {in_root}");
        let in_3: f64 = graph.delta_minus(3).iter().map(|&(_, a)| y[a as usize]).sum();
        assert!((in_3 - 1.0).abs() < 1e-6, "Flow into terminal 3 should be 1, got {in_3}");
    }

    #[test]
    fn test_lp_steiner_cut_tightens_bound() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        let bound_no_cuts = lp.solve();
        lp.add_steiner_cut(&[2, 4]);
        let bound_with_cuts = lp.solve();
        assert!(bound_with_cuts >= bound_no_cuts - 1e-9);
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

        let mut lp = LpRelaxation::from_formulation(&g, 1, &[3, 4], &[2]);
        lp.add_steiner_cut(&[2, 4]);
        lp.add_steiner_cut(&[4]);
        let obj = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        assert!(obj >= 5.0 - 1e-6, "LP bound should be >= 5, got {obj}");
    }

    #[test]
    fn rebuilding_preserves_the_bound_and_the_fixings() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        lp.add_steiner_cut(&[2, 4]);
        lp.fix_variable(4, 0.0); // forbid the direct 1->3 arc
        let before = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);

        lp.rebuild();
        let after = lp.solve();
        assert_eq!(lp.status, LpStatus::Optimal);
        assert!((before - after).abs() < 1e-9, "{before} != {after} after rebuild");
        assert!(lp.var_ub[4] == 0.0, "fixing must survive a rebuild");
    }

    #[test]
    fn pruning_removes_only_persistently_slack_cuts() {
        let (graph, root, terminals, steiner_nodes) = build_simple_instance();
        let mut lp = LpRelaxation::from_formulation(&graph, root, &terminals, &steiner_nodes);
        lp.add_steiner_cut(&[2, 4]);
        // A cut that every feasible point satisfies with room to spare.
        lp.add_cut(&[0, 1, 2, 3, 4, 5], &[1.0; 6], 0.0);
        lp.row_budget = 0; // force pruning to be considered every solve

        let baseline = lp.solve();
        // Eviction ranks by age and prunes down to a low-water mark, so a single
        // round is enough once the slack cut has gone one solve without binding.
        for _ in 0..3 {
            lp.solve();
            lp.prune_cuts();
        }

        assert_eq!(lp.num_cuts(), 1, "the binding Steiner cut must survive");
        let after = lp.solve();
        assert!((baseline - after).abs() < 1e-9, "pruning changed the bound");
    }
}
