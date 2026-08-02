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

/// A lower bound on an LP's optimum together with the reduced costs it was
/// derived from. See [`LpRelaxation::certified_dual_bound`] for the proposition
/// that makes both usable without trusting the backend.
///
/// The pair is produced together and must be used together: `value` and
/// `reduced` come from the same multiplier vector, and the elimination rule
/// `value + reduced[a] > UB` is sound only for a matched pair.
#[derive(Debug, Clone)]
pub struct CertifiedDual {
    /// `L(lambda)`, a valid lower bound on the LP optimum for any feasible
    /// point, whatever the solver reported.
    pub value: f64,
    /// `d = c - A' lambda`, one entry per column of the model.
    pub reduced: Vec<f64>,
}

pub struct LpRelaxation {
    pub num_vars: u32,
    pub objective: Vec<Cost>,
    pub solution: Vec<f64>,
    pub reduced_costs: Vec<f64>,
    /// Row multipliers of the last optimal solve, in the model's row order:
    /// `structural` first, then `cuts`. Only meaningful when
    /// [`LpRelaxation::is_optimal`] holds; see [`LpRelaxation::unit_arc_rows`].
    pub row_duals: Vec<f64>,
    pub dual_bound: f64,
    pub status: LpStatus,
    pub solve_count: u64,
    pub base_constraint_count: usize,
    pub solve_time_secs: f64,
    /// Seconds spent inside `run()` on the *current* HiGHS model. Reset by
    /// [`LpRelaxation::rebuild`], because a fresh model restarts HiGHS's own
    /// accumulated clock and the time limit is stated against that.
    model_solve_secs: f64,
    /// Number of model rebuilds triggered by cut-pool pruning.
    pub rebuilds: u64,
    /// Column index of the activation variable of each vertex id, when the
    /// vertex exists. Exposed so a separator can read `s` off a solution and
    /// write rows over it; see `separation::activation_rank`.
    pub node_col: Vec<Option<u32>>,

    /// Column description: (objective coefficient, lower bound, upper bound).
    col_cost: Vec<f64>,
    col_lb_base: Vec<f64>,
    col_ub_base: Vec<f64>,
    /// Structural rows; never removed.
    structural: Vec<RowData>,
    /// Valid structural rows held back and added only when violated: the
    /// edge-vertex coupling rows, whose count is proportional to the arc count,
    /// and the dual-ascent cut seed. Keeping all of them resident makes the
    /// model an order of magnitude larger than the number of variables while
    /// only a handful are ever binding.
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
    time_limit_secs: f64,
    /// Last values actually pushed to HiGHS.
    presolve_on: bool,
    armed_limit: f64,
    /// A clock the next solve must push before running. See
    /// [`LpRelaxation::arm_time_limit`].
    pending_limit: Option<f64>,
    /// The algorithm the next solve will use. See [`LpMethod`].
    pub method: LpMethod,
    /// The algorithm HiGHS has actually been told about.
    armed_method: Option<LpMethod>,

    model: Option<HModel>,
    cols: Vec<Col>,
    base_var_lb: Vec<f64>,
    base_var_ub: Vec<f64>,
    pub var_lb: Vec<f64>,
    pub var_ub: Vec<f64>,
}

/// Which algorithm HiGHS is asked to use.
///
/// # Why this is a choice and not a constant
///
/// The dual simplex is the right algorithm for an incremental cut loop: rows are
/// appended, the basis stays feasible for the dual, and a re-solve costs a
/// handful of pivots. That is what the branch-and-cut wants and it keeps it.
///
/// It is the wrong algorithm for the models this benchmark's larger instances
/// present, and the reason is visible in their costs. PACE Track 2's
/// instance142 has 118 edges of cost 100,000 among 724, the rest costing 1 to
/// 47; its optimum is `30 * 100,000 + 526`. The relaxation must resolve a
/// 526-unit structure inside a 3,000,000-unit objective, and it is massively
/// degenerate at that scale — many bases of all but identical value. Measured on
/// the root loop with nothing else changed:
///
/// | instance | simplex | interior point |
/// |---|---|---|
/// | 083 | 66 solves, stalls, 3,200,553.1 | 93 solves, **converged**, 3,200,554.0 |
/// | 130 | 28 solves, stalls, 3,600,591.9 | 79 solves, **converged**, 3,600,596.0 |
/// | 142 | 45 solves, stalls, 3,000,522.2 | 82 solves, 3,000,526.0 |
/// | 164 | 39 solves, stalls, 3,100,524.3 | 83 solves, **converged**, 3,100,526.0 |
/// | 070 | 139 solves, converged, 63.0 | 63 solves, converged, 63.0 |
///
/// "Stalls" is literal: a single solve on a 1,248-column model runs for 105
/// seconds without terminating, having been preceded by sixty-five solves
/// averaging a quarter of a second. Every converged interior-point value in that
/// table is *exactly the instance's optimum*.
///
/// # Why the choice is safe whichever way it goes
///
/// Interior point without crossover returns a non-basic point, and its duals are
/// approximately rather than exactly optimal. Nothing here needs them to be
/// either: the bound that gets reported is
/// [`LpRelaxation::certified_dual_bound`], which is a valid lower bound for an
/// *arbitrary* multiplier vector, and the packing extracted from those
/// multipliers is repaired to feasibility by scaling. A worse dual costs
/// strength and never validity, which is the same contract the separators have.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LpMethod {
    /// HiGHS's default: dual simplex, warm-started from the previous basis.
    Simplex,
    /// Interior point with crossover off.
    InteriorPoint,
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
    /// - `y(delta^-(r)) = 0`, `y(delta^-(t)) = 1` for terminals,
    ///   `y(delta^-(v)) = s_v` for the rest;
    /// - flow balance `y(delta^-(v)) <= y(delta^+(v))` for Steiner nodes;
    /// - anti-symmetry `y_uv + y_vu <= 1`;
    /// - the FC-BCR block (activation variables, vertex counting, edge-vertex
    ///   coupling) from section 11.1 of the research memo.
    ///
    /// The continuation and no-leaf rows are *not* here. Both became redundant
    /// when `y(delta^-(v)) = s_v` was strengthened from an inequality to an
    /// equality; the proofs are inline below, at the places they used to sit.
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

        // Activation columns come first, because the in-degree rows below are
        // stated against them.
        let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
        let max_node_id = graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;
        let mut s_col: Vec<Option<u32>> = vec![None; max_node_id + 1];
        for node in &graph.nodes {
            let fixed = terminal_set.contains(&node.id) || node.id == root;
            let (lb, ub) = if fixed { (1.0, 1.0) } else { (0.0, 1.0) };
            s_col[node.id as usize] = Some(b.add_col(0.0, lb, ub));
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

        // (3c) a Steiner node is entered exactly as often as it is active:
        //
        //     y(delta^-(v)) = s_v      for every non-root vertex.
        //
        // Valid because an arborescence gives every non-root vertex it contains
        // exactly one parent and every vertex it omits none, which is precisely
        // what `s_v` records.
        //
        // This replaces `y(delta^-(v)) <= 1`, and the difference is the whole
        // point. With the weak version the model can leave a vertex half active
        // while routing a full unit of flow through it, and `s` becomes a free
        // variable that the objective never sees. With the equality, `s` is
        // determined by `y`.
        //
        // It is also what makes the activation-rank family redundant rather than
        // missing. For a set `U` holding a terminal but not the root,
        //
        //     x(E(U)) = sum_{v in U} y(delta^-(v)) - y(delta^-(U))
        //             = s(U) - y(delta^-(U))
        //             <= s(U) - 1,
        //
        // the last step being the Steiner cut on `U`, which the max-flow
        // separator already produces exactly. So every rank inequality anchored
        // at a terminal follows from this row plus a connectivity row, and the
        // separate rank separator has nothing left to contribute -- which is
        // exactly what it measured before this row existed: it found violated
        // rows by the dozen and moved the bound by nothing, because the rows it
        // found were the ones this equality was failing to imply.
        for &v in steiner_nodes {
            let mut row: Vec<(u32, f64)> = in_arcs(v).into_iter().map(|a| (a, 1.0)).collect();
            if let Some(sv) = s_col[v as usize] {
                row.push((sv, -1.0));
                b.add_row(0.0, 0.0, row);
            } else {
                b.add_row(0.0, 1.0, row);
            }
        }

        // (4) flow balance: an entered Steiner node must be left.
        for &v in steiner_nodes {
            let mut row: Vec<(u32, f64)> = in_arcs(v).into_iter().map(|a| (a, 1.0)).collect();
            row.extend(out_arcs(v).into_iter().map(|a| (a, -1.0)));
            b.add_row(f64::NEG_INFINITY, 0.0, row);
        }

        // The continuation rows `y(delta^-(v)) >= y_a`, one per arc leaving a
        // Steiner node, used to live here. Given (3c) they read `s_v >= y_a`,
        // and the edge-vertex coupling below says `y_uv + y_vu <= s_v` for the
        // underlying edge, which is strictly stronger. So continuation is
        // implied by two rows the model already carries.
        //
        // That the implication survives *lazily* is the part worth stating: if a
        // continuation row is violated at some point then
        // `s_v = y(delta^-(v)) < y_a <= y_uv + y_vu`, so the coupling row for
        // that edge is violated too, and `separate_structural` scans the whole
        // pool every round and admits it. The lazy pool loses `|A|` rows of
        // width `indeg + 1` — on PACE instance189, 14,880 rows scanned per
        // separation round for nothing.

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

        // The no-leaf row `x(delta(v)) >= 2 s_v` used to live here — a used
        // Steiner node has undirected degree at least two, valid for
        // inclusion-minimal trees. It has collapsed into the flow-balance row.
        //
        // `x(delta(v)) = y(delta^-(v)) + y(delta^+(v))`, and (3c) is the
        // *equality* `y(delta^-(v)) = s_v` wherever an activation column exists
        // — which is wherever the no-leaf row was stated at all. So
        //
        //     x(delta(v)) - 2 s_v >= 0
        //       <=>  s_v + y(delta^+(v)) - 2 s_v >= 0
        //       <=>  y(delta^+(v)) >= s_v = y(delta^-(v)),
        //
        // which is row (4) verbatim. The two cut off exactly the same points, so
        // one of them was pure carrying cost: `|V|` dense rows, 4,136 of the
        // 19,776 structural rows on PACE instance189, in every solve at every
        // node. Row (4) is the one kept, because it also covers Steiner nodes
        // that have no activation column, where the argument above does not run.

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
            node_col: s_col.clone(),
            num_vars: num_arcs,
            objective,
            solution: vec![0.0; b.col_cost.len()],
            reduced_costs: vec![0.0; b.col_cost.len()],
            row_duals: Vec::new(),
            dual_bound: f64::NEG_INFINITY,
            status: LpStatus::NotSolved,
            solve_count: 0,
            base_constraint_count: structural_count,
            solve_time_secs: 0.0,
            model_solve_secs: 0.0,
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
            pending_limit: None,
            method: LpMethod::Simplex,
            armed_method: None,
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
        // A fresh HiGHS model carries none of the previous one's options, and its
        // own accumulated clock restarts at zero.
        self.armed_method = None;
        self.armed_limit = f64::INFINITY;
        self.pending_limit = None;
        self.model_solve_secs = 0.0;
        self.presolve_on = false;
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

    /// Add a general `<= hi` row over arbitrary columns, arc or activation.
    ///
    /// Column indices below `num_vars` are arcs; the rest are the activation
    /// columns published by [`LpRelaxation::node_col`].
    pub fn add_upper_cut(&mut self, entries: Vec<(u32, f64)>, hi: f64) {
        if entries.is_empty() {
            return;
        }
        self.push_cut(RowData { entries, lo: f64::NEG_INFINITY, hi });
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

    /// Give the model `secs` more seconds of solving from now.
    ///
    /// # Why this is a method and not a field
    ///
    /// HiGHS's `time_limit` is compared against a clock that **accumulates over
    /// every `run()` on one model**, so the option's value is an absolute
    /// deadline for the model, not a length for the next solve. Two things follow
    /// and both have cost a measurement:
    ///
    /// - it must be re-stated as `already spent + allowance`, and the "already
    ///   spent" is per model, so a pruning rebuild resets it;
    /// - a rule that only ever *lowers* it silently strangles every later solve.
    ///   With the loop granting a doubling sequence of batches, an option armed
    ///   at 0.26 s during the first batch left the third batch's solves 0.06 s
    ///   on a model that had already consumed 0.20 s — every one of them
    ///   returned non-optimal, the loop read that as "this algorithm cannot
    ///   solve this model", and instance083's packing stopped improving after
    ///   four solves.
    ///
    /// So the caller arms it explicitly, once per call, and the option reaches
    /// HiGHS exactly once for that call — which is what keeps the warm start.
    pub fn arm_time_limit(&mut self, secs: f64) {
        if !secs.is_finite() {
            self.pending_limit = None;
            self.time_limit_secs = f64::INFINITY;
            return;
        }
        self.time_limit_secs = secs;
        let limit = self.model_solve_secs + secs.max(0.01);
        if (limit - self.armed_limit).abs() > 1e-9 {
            self.pending_limit = Some(limit);
        }
    }

    pub fn solve(&mut self) -> f64 {
        let timer = std::time::Instant::now();
        let value = self.solve_inner();
        let secs = timer.elapsed().as_secs_f64();
        self.solve_time_secs += secs;
        self.model_solve_secs += secs;
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
        // The algorithm, pushed only when it changes. A rebuild loses the setting
        // along with the model, which `rebuild` records by clearing `armed_method`.
        if self.armed_method != Some(self.method) {
            match self.method {
                LpMethod::Simplex => {
                    model.set_option("solver", "simplex");
                    model.set_option("run_crossover", "on");
                }
                LpMethod::InteriorPoint => {
                    model.set_option("solver", "ipm");
                    // Crossover would hand the point back to the simplex that
                    // could not solve the model in the first place.
                    model.set_option("run_crossover", "off");
                }
            }
            self.armed_method = Some(self.method);
        }
        // The clock, pushed when the caller has armed a new one. HiGHS treats an
        // option assignment as a model event and drops the simplex state, so the
        // limit is stated once per *call* of the loop above rather than once per
        // solve; see [`LpRelaxation::arm_time_limit`].
        if let Some(limit) = self.pending_limit.take() {
            model.set_option("time_limit", limit);
            self.armed_limit = limit;
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
                self.row_duals = sol.dual_rows().to_vec();
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

    /// A lower bound on this LP's optimum, re-derived from the row multipliers
    /// alone, together with the reduced costs that go with it.
    ///
    /// # Why the solver's own objective is not enough
    ///
    /// `get_dual_bound` returns `c'y` at the primal point HiGHS handed back. That
    /// is a lower bound on the *integer* optimum only if the point is optimal for
    /// the LP, which is a claim about the solver's termination and its
    /// tolerances, not about anything this program can check. Worse, the number
    /// is then used twice in ways that must not be wrong: as a reported dual
    /// bound, and inside `obj + rc_a > UB` as the basis of an arc elimination.
    /// A tolerance-sized overshoot in the first is a wrong answer, and in the
    /// second it deletes an arc some optimum needs.
    ///
    /// This computes instead a number that is a lower bound for *any* multiplier
    /// vector whatsoever, so nothing about the solve has to be believed.
    ///
    /// > **Proposition (certified dual bound).** Let the LP be
    /// > `min { c'x : lo <= Ax <= hi, l <= x <= u }` and let `lambda` be an
    /// > arbitrary vector with one entry per row, subject to `lambda_r = 0`
    /// > whenever the bound it would be priced against is infinite. Put
    /// > `d = c - A' lambda` and
    /// >
    /// > ```text
    /// > L(lambda) = sum_r [ lambda_r > 0 ? lambda_r lo_r : lambda_r hi_r ]
    /// >           + sum_j [ d_j     > 0 ? d_j l_j        : d_j u_j        ].
    /// > ```
    /// >
    /// > Then `L(lambda) <= c'x` for every feasible `x`.
    /// >
    /// > *Proof.* `c'x = (d + A'lambda)'x = d'x + lambda'(Ax)`. Term by term,
    /// > `d_j x_j >= min{d_j l_j, d_j u_j}`, which is the bracketed column term
    /// > because `l_j <= x_j <= u_j`; and with `s = Ax` satisfying
    /// > `lo <= s <= hi`, `lambda_r s_r >= min{lambda_r lo_r, lambda_r hi_r}`,
    /// > which is the bracketed row term. Summing gives `c'x >= L(lambda)`. ∎
    ///
    /// The hypotheses are discharged by construction rather than assumed:
    /// a multiplier that would be priced against an infinite bound is **clamped
    /// to zero** — which is the repair the round-off could otherwise hide — and
    /// `d` is recomputed from the clamped vector, so the identity
    /// `c = d + A'lambda` holds exactly as computed.
    ///
    /// Both sign conventions are evaluated and the larger kept. The formula is
    /// valid for any `lambda`, so trying `-lambda` as well costs one pass and
    /// removes the last thing that had to be assumed about the backend: which way
    /// round it signs the duals of a minimisation.
    ///
    /// At an optimal basis `L(lambda)` is the LP optimum by strong duality, so
    /// nothing is given up in exchange for the guarantee. Returns `None` only
    /// when the multiplier vector does not have one entry per row, in which case
    /// there is nothing to certify.
    pub fn certified_dual_bound(&self) -> Option<CertifiedDual> {
        let num_rows = self.structural.len() + self.cuts.len();
        if self.row_duals.len() != num_rows {
            return None;
        }
        let a = self.certified_dual_for_sign(1.0);
        let b = self.certified_dual_for_sign(-1.0);
        match (a, b) {
            (Some(x), Some(y)) => Some(if x.value >= y.value { x } else { y }),
            (Some(x), None) => Some(x),
            (None, Some(y)) => Some(y),
            (None, None) => None,
        }
    }

    fn certified_dual_for_sign(&self, sign: f64) -> Option<CertifiedDual> {
        let rows = || self.structural.iter().chain(self.cuts.iter().map(|c| &c.row));
        let mut lambda: Vec<f64> = self.row_duals.iter().map(|&d| sign * d).collect();
        for (r, row) in rows().enumerate() {
            // A multiplier priced against an infinite bound contributes minus
            // infinity; the repair is to drop the row, which only weakens `L`.
            if (lambda[r] > 0.0 && !row.lo.is_finite()) || (lambda[r] < 0.0 && !row.hi.is_finite()) {
                lambda[r] = 0.0;
            }
        }
        let mut reduced = self.col_cost.clone();
        for (r, row) in rows().enumerate() {
            if lambda[r] == 0.0 {
                continue;
            }
            for &(c, v) in &row.entries {
                reduced[c as usize] -= lambda[r] * v;
            }
        }
        let mut value = 0.0;
        for (r, row) in rows().enumerate() {
            if lambda[r] > 0.0 {
                value += lambda[r] * row.lo;
            } else if lambda[r] < 0.0 {
                value += lambda[r] * row.hi;
            }
        }
        for (j, &d) in reduced.iter().enumerate() {
            let (lb, ub) = self.current_col_bounds(j);
            let bound = if d > 0.0 { lb } else { ub };
            if !bound.is_finite() {
                // Only possible on a column with an infinite bound, which this
                // formulation does not have; refuse rather than return a number
                // whose provenance is not the proposition above.
                if d != 0.0 {
                    return None;
                }
                continue;
            }
            value += d * bound;
        }
        if !value.is_finite() {
            return None;
        }
        Some(CertifiedDual { value, reduced })
    }

    /// Every row of the shape `sum_{a in A} y_a >= 1` over arc columns only,
    /// paired with the multiplier the last optimal solve gave it.
    ///
    /// This is the raw material for a certified cut packing. Two families of the
    /// model have this shape and no others do: the separated Steiner cuts and the
    /// dual-ascent seeds, and the terminal in-degree equalities
    /// `y(delta^-(t)) = 1`, whose row is `delta^-({t})` and whose multiplier is
    /// usable exactly when it is non-negative — an equality row priced downwards
    /// is not a `>=` multiplier and is dropped here.
    ///
    /// The caller is not asked to trust that `A` is a cut of anything.
    /// [`crate::model::lp_packing`] recovers a vertex set from `A` alone and
    /// verifies the packing condition against the arc costs, so a row that is not
    /// a Steiner cut at all can only weaken the resulting bound.
    ///
    /// The model's row order is `structural` then `cuts`, which is the order
    /// [`LpRelaxation::rebuild`] and [`LpRelaxation::push_cut`] both maintain, so
    /// index `i` of `row_duals` names the `i`-th row of that concatenation.
    pub fn unit_arc_rows(&self) -> Vec<(&[(u32, f64)], f64)> {
        if !self.is_optimal() {
            return Vec::new();
        }
        let num_vars = self.num_vars;
        self.structural
            .iter()
            .chain(self.cuts.iter().map(|c| &c.row))
            .zip(self.row_duals.iter().copied())
            .filter(|&(row, dual)| {
                dual > 1e-9
                    && row.lo == 1.0
                    && row.entries.iter().all(|&(c, v)| c < num_vars && v == 1.0)
            })
            .map(|(row, dual)| (row.entries.as_slice(), dual))
            .collect()
    }

    /// Unit-coefficient `>= rhs` rows with `rhs > 1`, and their duals.
    ///
    /// [`LpRelaxation::unit_arc_rows`] deliberately keeps only `rhs == 1`, which
    /// is the shape a single Steiner cut has. A partition inequality has the
    /// same coefficients and a larger right-hand side, and it carries a witness
    /// that lets it be *decomposed* into that many Steiner cuts — see
    /// [`crate::model::lp_packing`]. This is how the caller gets hold of the
    /// multiplier it needs to do that; the caller supplies the witness, since
    /// the model has no idea what a row means.
    pub fn unit_rows_above_one(&self) -> Vec<(&[(u32, f64)], f64, f64)> {
        if !self.is_optimal() {
            return Vec::new();
        }
        let num_vars = self.num_vars;
        self.structural
            .iter()
            .chain(self.cuts.iter().map(|c| &c.row))
            .zip(self.row_duals.iter().copied())
            .filter(|&(row, dual)| {
                dual > 1e-9
                    && row.lo > 1.0
                    && row.lo.is_finite()
                    && row.entries.iter().all(|&(c, v)| c < num_vars && v == 1.0)
            })
            .map(|(row, dual)| (row.entries.as_slice(), row.lo, dual))
            .collect()
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

/// Formulation validity: every Steiner tree must satisfy every row of the model.
///
/// A separator that emits an invalid row is caught by the harnesses in
/// `separation`; nothing was checking the structural rows themselves, and a bad
/// one there is worse -- it is in the model from the first solve, at every node,
/// and it silently raises the dual bound above the optimum.
#[cfg(test)]
mod formulation_validity {
    use super::*;
    use crate::graph::{NodeType, UndirectedGraph};
    use std::collections::{HashSet, VecDeque};

    /// Check the incidence vector of every Steiner tree against every row.
    fn check(g: &UndirectedGraph, terminals: &[NodeId], root: NodeId) -> Vec<String> {
        let dg = DirectedGraph::from_undirected(g);
        let tset: HashSet<NodeId> = terminals.iter().copied().collect();
        let steiner: Vec<NodeId> =
            dg.nodes.iter().map(|n| n.id).filter(|v| !tset.contains(v) && *v != root).collect();
        let lp = LpRelaxation::from_formulation(&dg, root, terminals, &steiner);

        let n = dg.nodes.iter().map(|x| x.id).max().unwrap_or(0) as usize + 1;
        let m = dg.arcs.len() / 2;
        let mut bad = Vec::new();

        for mask in 0u32..(1u32 << m) {
            let mut adj: Vec<Vec<(NodeId, ArcId)>> = vec![Vec::new(); n];
            let mut count = 0usize;
            for p in 0..m {
                if mask >> p & 1 == 1 {
                    let (f, r) = (&dg.arcs[2 * p], &dg.arcs[2 * p + 1]);
                    adj[f.tail as usize].push((f.head, f.id));
                    adj[f.head as usize].push((f.tail, r.id));
                    count += 1;
                }
            }
            let mut seen = vec![false; n];
            let mut point = vec![0.0f64; lp.col_cost.len()];
            let mut used = 0usize;
            let mut queue = VecDeque::new();
            seen[root as usize] = true;
            queue.push_back(root);
            while let Some(x) = queue.pop_front() {
                for &(y, arc) in &adj[x as usize] {
                    if seen[y as usize] {
                        continue;
                    }
                    seen[y as usize] = true;
                    point[arc as usize] = 1.0;
                    used += 1;
                    queue.push_back(y);
                }
            }
            if used != count || !terminals.iter().all(|&t| seen[t as usize]) {
                continue;
            }
            // The no-leaf and flow-balance rows are stated for inclusion-minimal
            // trees, which is legitimate under non-negative costs but means the
            // model does not have to accept a tree with a Steiner leaf. Only
            // pruned trees are in scope here.
            let mut deg = vec![0usize; n];
            for p in 0..m {
                if mask >> p & 1 == 1 {
                    deg[dg.arcs[2 * p].tail as usize] += 1;
                    deg[dg.arcs[2 * p].head as usize] += 1;
                }
            }
            let pruned = (1..n).all(|v| {
                !seen[v] || tset.contains(&(v as NodeId)) || v as NodeId == root || deg[v] >= 2
            });
            if !pruned {
                continue;
            }
            for v in 1..n {
                if seen[v] {
                    if let Some(Some(c)) = lp.node_col.get(v) {
                        point[*c as usize] = 1.0;
                    }
                }
            }

            let rows = lp.structural.iter().chain(lp.lazy.iter());
            for (i, row) in rows.enumerate() {
                let act: f64 = row.entries.iter().map(|&(c, k)| k * point[c as usize]).sum();
                if act < row.lo - 1e-6 || act > row.hi + 1e-6 {
                    bad.push(format!(
                        "row {i} [{}, {}] has activity {act} at a valid tree with {count} edges",
                        row.lo, row.hi
                    ));
                    if bad.len() > 3 {
                        return bad;
                    }
                }
            }
            // Column bounds too: `s` on an unused Steiner vertex must be allowed
            // to be zero, and every fixed column must accept its value.
            for c in 0..lp.col_cost.len() {
                let (lo, hi) = (lp.col_lb_base[c], lp.col_ub_base[c]);
                if point[c] < lo - 1e-6 || point[c] > hi + 1e-6 {
                    bad.push(format!("column {c} value {} outside [{lo}, {hi}]", point[c]));
                    if bad.len() > 3 {
                        return bad;
                    }
                }
            }
        }
        bad
    }

    #[test]
    fn every_steiner_tree_satisfies_every_structural_row() {
        let mut seed = 0x0DDB_A11C_0FFE_E123u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..400 {
            let n = 4 + (rng() % 6) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 2 + (rng() % 3) as u32;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 4 != 0 {
                        g.add_edge(u, v, 1.0 + (rng() % 5) as f64);
                    }
                }
            }
            if g.edges.is_empty() || g.edges.len() > 17 {
                continue;
            }
            let bad = check(&g, &terminals, terminals[0]);
            assert!(bad.is_empty(), "formulation cuts off a valid tree: {:#?}", bad);
        }
    }
}
