//! The bidirected cut relaxation, solved without an LP.
//!
//! # What this replaces, and why an LP was the wrong instrument
//!
//! The root separation loop in [`crate::model::lp_packing`] computes a lower
//! bound by handing a simplex (or an interior point) a model of one to four
//! thousand rows over one to three thousand columns, separating violated Steiner
//! cuts by max flow, and re-solving. The measured cost is 25–500 ms per solve
//! times fifty to a hundred solves, on models that are massively degenerate
//! because a five-hundred-unit structure has to be resolved inside a
//! three-million-unit objective. That is not a constant factor from a five-second
//! budget; it is an algorithm away.
//!
//! This module removes the LP. It solves the *same relaxation* by projected
//! supergradient ascent on a dual whose oracle is a shortest path rather than a
//! max flow, whose iterates are feasible by construction, and whose value is
//! therefore a valid lower bound at every iteration — with no repair step, no
//! separation round, and no solver to trust.
//!
//! # The reformulation
//!
//! Write `BCR` for the bidirected cut relaxation rooted at `r`,
//!
//! ```text
//! min c'x  s.t.  x(delta^-(W)) >= 1  for every W with r not in W, W meets T,
//!                x >= 0.
//! ```
//!
//! (The upper bounds `x <= 1` are redundant: if `x` is feasible then so is
//! `min(x,1)`, because a cut that loses value under the truncation contains an
//! arc with `x_a > 1`, whose truncated value alone is already 1.)
//!
//! **Step 1 — cuts become flows.** By max-flow/min-cut, `x(delta^-(W)) >= 1` for
//! every `W` separating `r` from `t` says exactly that `x`, read as a capacity,
//! supports one unit of flow from `r` to `t`. So `BCR` is
//!
//! ```text
//! min c'x  s.t.  f^t is a unit r->t flow and f^t <= x, for every t in T\{r},
//!                x, f >= 0,
//! ```
//!
//! a *compact* linear program: `|T|` flows sharing one capacity vector.
//!
//! **Step 2 — its dual is a packing of shortest paths.** Let `lambda^t_a >= 0`
//! price the coupling `f^t_a <= x_a` and `pi^t_v` the flow conservation of
//! commodity `t`. The `x_a` column gives `sum_t lambda^t_a <= c_a`; the `f^t_a`
//! column for `a = (u,v)` gives `pi^t_u - pi^t_v <= lambda^t_a`, whose best
//! solution for fixed `lambda` is the shortest-path distance. Hence
//!
//! > **Proposition (flow dual).**
//! >
//! > ```text
//! > BCR* = max  sum_{t in T\{r}} d_{lambda^t}(r, t)
//! >        s.t. lambda >= 0,  sum_{t} lambda^t_a <= c_a  for every arc a,
//! > ```
//! >
//! > where `d_w(r,t)` is the shortest-path distance from `r` to `t` under
//! > non-negative arc lengths `w`.
//!
//! **Step 3 — and every feasible `lambda` is already a certificate.** The
//! inequality that matters does not need LP duality at all, and is proved here
//! from scratch so that nothing about the derivation above has to be believed:
//!
//! > **Proposition (weak duality, elementary).** Let `A` be the arc set of any
//! > arborescence rooted at `r` that reaches every terminal, and let
//! > `lambda >= 0` satisfy `sum_t lambda^t_a <= c_a` for every arc `a`. Then
//! >
//! > ```text
//! > sum_{t} d_{lambda^t}(r, t)  <=  c(A).
//! > ```
//! >
//! > *Proof.* For each terminal `t` let `P_t subseteq A` be the unique directed
//! > `r`->`t` path in `A`. Then `d_{lambda^t}(r,t) <= lambda^t(P_t)`, and since
//! > `P_t subseteq A` and `lambda >= 0`,
//! >
//! > ```text
//! > sum_t d_{lambda^t}(r,t) <= sum_t lambda^t(P_t)
//! >                         <= sum_t sum_{a in A} lambda^t_a
//! >                          = sum_{a in A} sum_t lambda^t_a
//! >                         <= sum_{a in A} c_a = c(A).   ∎
//! > ```
//!
//! Every optimal Steiner tree is realisable as such an arborescence, so the
//! displayed quantity is a lower bound on the instance. **No iterate of the
//! ascent below is ever infeasible, so no iterate can report an invalid bound**,
//! and the value is recomputed from the multipliers by `|T|` fresh Dijkstras
//! before it is reported ([`FlowDual::finish`]).
//!
//! # Why this is cheap where the LP is not
//!
//! The oracle is `|T|` Dijkstras on non-negative lengths — exact, no tolerance,
//! no basis, no warm start to lose. On PACE instance083 (`|R| = 32`,
//! `|A| = 1,248`) one full oracle call costs well under a millisecond, against
//! 25–500 ms for one LP solve of the same relaxation. **Separation disappears**:
//! the `lambda` formulation already carries every cut, so there is nothing to
//! find and nothing to install, and the row count that made the LP degenerate
//! never exists.
//!
//! # The ascent
//!
//! `F(lambda) = sum_t d_{lambda^t}(r,t)` is concave — each term is a minimum of
//! linear functions — and the feasible set
//! `Lambda = { lambda >= 0 : sum_t lambda^t_a <= c_a }` is a product, over arcs,
//! of scaled simplices. Two facts make projected supergradient ascent the right
//! method rather than merely an available one:
//!
//! - **The supergradient is a flow.** If `f^t` is any unit `r`->`t` flow
//!   supported on the shortest-path DAG of `lambda^t`, then for every `mu`,
//!   `d_{mu^t}(r,t) <= mu^t . f^t = d_{lambda^t}(r,t) + (mu^t - lambda^t) . f^t`,
//!   so `f` is a supergradient of `F` at `lambda`. Taking the *whole DAG* rather
//!   than one shortest path — the flow that splits evenly at every branching — is
//!   still a supergradient, and it is markedly more stable, because a single path
//!   makes the iterate oscillate between parallel routes of equal length.
//! - **The projection decomposes.** `Pi_Lambda` acts on each arc independently,
//!   and on one arc it is the Euclidean projection onto
//!   `{ z >= 0 : sum_k z_k <= c_a }` — either `z^+` itself, or the projection of
//!   `z` onto the simplex of radius `c_a`, computed exactly by the standard sort
//!   and threshold. Only arcs whose column is over capacity need touching, and a
//!   zero coordinate stays zero under that projection, so a step projects a
//!   handful of short lists rather than the whole vector.
//!
//! # The step, and the one thing that had to be measured before it was right
//!
//! Polyak's step `s = gamma (target - F) / ||g||^2` is exactly right when
//! `target` is the optimum of the *dual being ascended*, and it converges only
//! to a neighbourhood of radius `target - BCR*` when the target overshoots. The
//! first version aimed at the incumbent, which on this benchmark is usually the
//! instance's optimum — and `OPT - BCR*` is not zero. On PACE instance083 that
//! rule stalled at `3,200,530` against a root LP of `3,200,554`, and the 24 units
//! were **the overshoot, not the relaxation**: the target was 24 above the
//! quantity being maximised, so 24 is exactly the radius the iteration cannot
//! enter. Withholding the incumbent was worse still — the step diverged on the
//! first move and never recovered, because the iterate is not reset when the
//! target proves unreachable.
//!
//! What is used instead is the classical *adaptive level* rule, which needs no
//! valid target at all:
//!
//! ```text
//! aim   = min(UB, F_best + Delta)
//! s     = gamma (aim - F(lambda)) / ||g||^2
//! ```
//!
//! with `Delta` halved, and the iterate **restored to the best one seen**,
//! whenever a window of iterations passes without improving `F_best`. Halving a
//! level gap is scale free — it is a fraction of the gap the method has already
//! shown it cannot close, not a fraction of anything measured in cost units —
//! and the restart is what stops a too-large step from being paid for forever.
//! `Delta` starts at `UB - F(seed)` when an incumbent is available and at a
//! fraction of the seed otherwise, and the run ends when `Delta` is negligible
//! against the bound, which is the method's own convergence signal.
//!
//! # Initialisation, and why the method starts above the ascent
//!
//! Wong's dual ascent is already a feasible point of this dual, and identifying
//! it as one costs nothing. Each ascent step raises one set `W` by `delta` on
//! behalf of one terminal `t`; putting `lambda^t_a += delta` for
//! `a in delta^-(W)` yields a `lambda` whose arc loads are exactly the ascent's,
//! hence feasible, and whose `d_{lambda^t}(r,t)` is at least the total raised for
//! `t`, because every `r`->`t` path crosses every set raised for `t`. So
//! `F(lambda_0) >= ascent bound`, and the ascent's own maximality — which forbids
//! any *combinatorial* improvement — is no obstacle here, because a supergradient
//! step lowers some coordinates in order to raise others.
//!
//! # What comes out
//!
//! Three objects, all derived from one feasible `lambda`:
//!
//! 1. the **bound** `F(lambda)`, recomputed from the multipliers;
//! 2. a **cut packing** ([`FlowDual::packing`]), by integrating the level sets of
//!    each `d_{lambda^t}`, which is what the goal-directed search consumes;
//! 3. an **arc pricing** `(L, d)` with `d_a = c_a - sum_t lambda^t_a >= 0` and
//!    `c(A) >= L + d(A)` for every arborescence `A`.
//!
//! # The packing, and why the level sets of a distance function are one
//!
//! > **Proposition (level-set packing).** Fix a commodity `t`, write
//! > `d(v) = d_{lambda^t}(r,v)` and `D = d(t)`. For `0 <= theta < D` put
//! > `W_theta = { v : d(v) > theta }`. Then `r not in W_theta`, `t in W_theta`,
//! > and the family `{ (d theta, W_theta) }` — the level sets carrying Lebesgue
//! > weight — satisfies, for every arc `a = (u,v)`,
//! >
//! > ```text
//! > measure { theta in [0, D) : a enters W_theta }  <=  lambda^t_a,
//! > ```
//! >
//! > with total weight `D`.
//! >
//! > *Proof.* `d(r) = 0 <= theta` and `d(t) = D > theta`. An arc `a = (u,v)`
//! > enters `W_theta` exactly when `d(u) <= theta < d(v)`, a set of measure
//! > `(d(v) - d(u))^+ <= lambda^t_a` by the triangle inequality for shortest
//! > distances. ∎
//!
//! Summing over commodities gives arc load at most `sum_t lambda^t_a <= c_a`, so
//! the union of the `|T|` chains is a single feasible packing of value
//! `sum_t D_t = F(lambda)`. In practice each chain is truncated to a budget by
//! keeping its heaviest sets; **a sub-family of a packing is a packing**, so the
//! truncation costs strength and never validity, and the reported *bound* is
//! never the packing's value but `F(lambda)` itself.

use std::collections::BinaryHeap;
use std::time::Instant;

use crate::graph::algorithms::{dual_ascent_cuts, ArcIndex};
use crate::graph::{ArcId, Cost, NodeId};
use crate::model::lp_packing::CertifiedPacking;

/// Arc entries the seeding ascent may record. A truncated record yields a weaker
/// starting point and never an infeasible one.
const SEED_CUT_NNZ: usize = 4_000_000;

/// Why a [`FlowDual`] could not be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowDualRefusal {
    /// Fewer than two terminals: there is no dual to ascend.
    Trivial,
    /// The multiplier vector exceeds the caller's memory budget. A refusal, not a
    /// truncation: a truncated multiplier vector would still be feasible, but the
    /// caller asked for a method and not for a worse one, and refusing an attempt
    /// can never change the answer of a completed one.
    TooLarge { entries: usize, budget: usize },
}

/// Tuning the ascent. Every field is a property of the *method*, not of an
/// instance family; the defaults are the classical ones.
#[derive(Debug, Clone, Copy)]
pub struct FlowDualOptions {
    /// Polyak's `gamma`, halved on a stalled window.
    pub step_gamma: Cost,
    /// Momentum weight `beta` in `d_k = g_k + beta d_{k-1}`; `0` gives the plain
    /// supergradient direction and costs one fewer `|T| |A|` array.
    ///
    /// The Camerini–Fratta–Maffioli deflection rule was implemented here first
    /// and is **dead on this dual**, provably: CFM sets
    /// `beta = gamma max(0, -<d_{k-1}, g_k>) / ||d_{k-1}||^2`, and every
    /// supergradient of `F` is a *flow*, hence non-negative, so
    /// `<d_{k-1}, g_k> >= 0` at every iteration and `beta` is identically zero.
    /// Measured: the CFM and the plain runs agreed to the last digit on
    /// instances 070, 083 and 142 at every window. Plain momentum is not dead —
    /// it is worth one to two units of bound on 083 and 142 at `beta = 0.6` —
    /// and that is what this field now is.
    pub deflection: Cost,
    /// Iterations without an improved best value before the level gap is first
    /// halved. The window **doubles** at every halving: a level gap half the size
    /// takes proportionally longer to close, so spending a fixed number of
    /// iterations at every level either abandons the large gaps too late or the
    /// small ones too early. Doubling makes the total spent at the levels above
    /// the useful one at most twice the useful part, the windows being a
    /// geometric series — the same argument §79 makes for the separation batch.
    pub stall_window: u32,
    /// When no incumbent is supplied, the target is `F_best * (1 + this)`.
    pub blind_target_slack: Cost,
    /// Multipliers admitted, `|T\{r}| * |A|`. `0` means unlimited.
    pub entry_budget: usize,
    /// Restore the best iterate when the level gap is halved.
    pub restart_on_stall: bool,
}

impl Default for FlowDualOptions {
    fn default() -> Self {
        Self {
            step_gamma: 2.0,
            deflection: 0.6,
            stall_window: 32,
            blind_target_slack: 0.05,
            entry_budget: 0,
            restart_on_stall: false,
        }
    }
}

/// One run's measurements. Every field is observed, none is assumed.
#[derive(Debug, Clone, Copy, Default)]
pub struct FlowDualStats {
    pub iterations: u64,
    pub oracle_calls: u64,
    pub oracle_secs: f64,
    pub step_secs: f64,
    pub projected_arcs: u64,
    /// Iterations since the best value last improved when the run ended.
    pub stalled_for: u32,
    /// The level gap when the run ended.
    pub gamma: Cost,
    /// Times the level gap was halved and the iterate restored.
    pub restarts: u64,
    /// Value of the seed, before any step.
    pub seed_value: Cost,
}

/// Why an ascent stopped. A stop is a measurement, never a change of answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowDualStop {
    /// The bound met the cutoff: the instance is proved from the dual alone.
    Proved,
    /// The step length collapsed, or the supergradient vanished, or a commodity
    /// became unreachable. This is the method's own convergence signal.
    Converged,
    /// The deadline arrived.
    Deadline,
    /// The iteration budget ran out.
    Iterations,
}

/// Projected supergradient ascent on the flow dual of the bidirected cut
/// relaxation. See the module documentation for the mathematics.
pub struct FlowDual {
    root: NodeId,
    /// `T \ {root}`, in the order the multiplier blocks are laid out.
    sinks: Vec<NodeId>,
    n: usize,
    m: usize,
    cost: Vec<Cost>,

    /// Multipliers, commodity-major: `lam[k * m + a]`.
    lam: Vec<Cost>,
    /// Supergradient, same layout.
    grad: Vec<Cost>,
    /// Momentum direction, same layout. Empty when momentum is off.
    dir: Vec<Cost>,
    /// The best iterate, kept so that everything reported is re-derived from a
    /// multiplier vector rather than from a running total.
    best_lam: Vec<Cost>,
    /// `sum_k lam[k*m+a]`, recomputed from `lam` after every step.
    load: Vec<Cost>,

    value: Cost,
    best_value: Cost,
    /// `d_{lambda^k}` at the finished iterate, `k*n + v`. Filled by `finish`.
    best_dist: Vec<Cost>,
    best_load: Vec<Cost>,
    finished: bool,

    opts: FlowDualOptions,
    /// Polyak's target, when the caller wants one that differs from the value it
    /// would stop at. Defaults to the cutoff.
    target: Option<Cost>,
    /// The adaptive level gap `Delta`.
    delta: Cost,
    /// The current stall window, doubled at every halving of `delta`.
    window: u32,
    gamma: Cost,
    stats: FlowDualStats,
    stalled: u32,

    // Scratch, allocated once.
    dist: Vec<Cost>,
    settled: Vec<u32>,
    parent: Vec<ArcId>,
    order: Vec<NodeId>,
    amount: Vec<Cost>,
    over: Vec<ArcId>,
    sorted: Vec<Cost>,
    heap: BinaryHeap<std::cmp::Reverse<(u64, NodeId)>>,
}

impl FlowDual {
    /// Build and seed from Wong's dual ascent at `root`.
    pub fn new(
        idx: &ArcIndex,
        root: NodeId,
        terminals: &[NodeId],
        opts: FlowDualOptions,
    ) -> Result<Self, FlowDualRefusal> {
        let sinks: Vec<NodeId> = terminals.iter().copied().filter(|&t| t != root).collect();
        if sinks.is_empty() {
            return Err(FlowDualRefusal::Trivial);
        }
        let m = idx.num_arcs();
        let n = idx.num_nodes();
        let k = sinks.len();
        let entries = k.saturating_mul(m);
        if opts.entry_budget > 0 && entries > opts.entry_budget {
            return Err(FlowDualRefusal::TooLarge { entries, budget: opts.entry_budget });
        }

        let cost: Vec<Cost> = (0..m).map(|a| idx.cost(a as ArcId)).collect();
        let mut this = Self {
            root,
            sinks,
            n,
            m,
            cost,
            lam: vec![0.0; entries],
            grad: vec![0.0; entries],
            dir: if opts.deflection > 0.0 { vec![0.0; entries] } else { Vec::new() },
            best_lam: vec![0.0; entries],
            load: vec![0.0; m],
            value: Cost::NEG_INFINITY,
            best_value: Cost::NEG_INFINITY,
            best_dist: Vec::new(),
            best_load: vec![0.0; m],
            finished: false,
            opts,
            target: None,
            delta: Cost::NAN,
            window: opts.stall_window.max(1),
            gamma: opts.step_gamma,
            stats: FlowDualStats { gamma: opts.step_gamma, ..Default::default() },
            stalled: 0,
            dist: vec![Cost::INFINITY; n],
            settled: vec![u32::MAX; n],
            parent: vec![u32::MAX; n],
            order: Vec::with_capacity(n),
            amount: vec![0.0; n],
            over: Vec::new(),
            sorted: vec![0.0; k],
            heap: BinaryHeap::new(),
        };
        this.seed_from_ascent(idx, terminals);
        project_all(&mut this.lam, &this.cost, &mut this.load, m, k);
        this.best_lam.copy_from_slice(&this.lam);
        Ok(this)
    }

    /// Identify Wong's ascent as a point of this dual.
    ///
    /// Each step raises `W(t)` by `delta`; the arcs of `delta^-(W(t))` are
    /// recorded, so `lambda^t += delta * 1[delta^-(W(t))]` reproduces the
    /// ascent's arc loads exactly, one commodity at a time.
    fn seed_from_ascent(&mut self, idx: &ArcIndex, terminals: &[NodeId]) {
        let active = vec![true; self.m];
        let asc = dual_ascent_cuts(idx, self.root, terminals, &active, SEED_CUT_NNZ);
        let mut slot = vec![usize::MAX; self.n];
        for (k, &t) in self.sinks.iter().enumerate() {
            slot[t as usize] = k;
        }
        for (step, cut) in asc.steps.iter().zip(asc.cuts.iter()) {
            let k = slot[step.terminal as usize];
            if k == usize::MAX {
                continue;
            }
            let base = k * self.m;
            for &a in cut {
                self.lam[base + a as usize] += step.delta;
            }
        }
    }

    pub fn num_commodities(&self) -> usize {
        self.sinks.len()
    }

    pub fn root(&self) -> NodeId {
        self.root
    }

    /// The best value the ascent has reached. Valid, but [`Self::finish`] is what
    /// re-derives it from the multipliers.
    pub fn bound(&self) -> Cost {
        self.best_value
    }

    /// Aim Polyak's step at `t` rather than at the cutoff.
    ///
    /// Separating the two lets a probe run past the point where the instance is
    /// proved, and lets the solver aim at an incumbent it does not intend to stop
    /// at. It changes the *rate*, never the validity: the bound is `F(lambda)`
    /// whatever step produced `lambda`.
    pub fn set_target(&mut self, t: Option<Cost>) {
        self.target = t;
    }

    pub fn stats(&self) -> FlowDualStats {
        self.stats
    }

    /// Re-derive everything reportable from the best multiplier vector.
    ///
    /// Repairs `best_lam` into `Lambda` by recomputing every arc's column sum from
    /// scratch, then runs `|T|` fresh full Dijkstras and returns their total. The
    /// returned number does not read any running total this module maintains, so
    /// a fault in the incremental bookkeeping cannot inflate it.
    ///
    /// Returns `NEG_INFINITY` if some terminal is unreachable, which means the
    /// instance is disconnected on the arcs supplied.
    pub fn finish(&mut self, idx: &ArcIndex) -> Cost {
        let (m, k, n) = (self.m, self.sinks.len(), self.n);
        project_all(&mut self.best_lam, &self.cost, &mut self.best_load, m, k);
        if self.best_dist.len() != k * n {
            self.best_dist = vec![Cost::INFINITY; k * n];
        }
        let mut total = 0.0;
        for kk in 0..k {
            dijkstra_into(
                idx,
                self.root,
                n,
                &self.best_lam,
                kk * m,
                None,
                &mut self.dist,
                &mut self.settled,
                &mut self.parent,
                &mut self.order,
                &mut self.heap,
            );
            let d = self.dist[self.sinks[kk] as usize];
            if !d.is_finite() {
                self.finished = false;
                return Cost::NEG_INFINITY;
            }
            total += d;
            self.best_dist[kk * n..(kk + 1) * n].copy_from_slice(&self.dist);
        }
        self.best_value = total;
        self.finished = true;
        total
    }

    /// The arc pricing implied by the finished iterate.
    ///
    /// Returns `(L, d)` with `d_a = c_a - sum_k lambda^k_a >= 0` and, for every
    /// arborescence `A` rooted at `root` that reaches the terminals,
    /// `c(A) >= L + sum_{a in A} d_a`. The proof is one line of the module's
    /// weak-duality proposition: `c(A) = d(A) + sum_{a in A} load(a)` and
    /// `sum_{a in A} load(a) >= sum_k lambda^k(P_k) >= L`.
    ///
    /// Call [`Self::finish`] first; the pricing is stated against the multipliers
    /// the bound was re-derived from.
    pub fn pricing(&self) -> (Cost, Vec<Cost>) {
        let d: Vec<Cost> =
            (0..self.m).map(|a| (self.cost[a] - self.best_load[a]).max(0.0)).collect();
        (self.best_value.max(0.0), d)
    }

    /// Run until one of the stopping conditions fires.
    ///
    /// `cutoff` is the incumbent: the ascent stops as soon as the bound reaches
    /// it, because the instance is then proved, and the value is also Polyak's
    /// target. Pass `Cost::INFINITY` when no incumbent is available.
    ///
    /// `check_every` is how many iterations run between clock reads; the clock may
    /// refuse to start another iteration and may never alter one that ran.
    pub fn ascend(
        &mut self,
        idx: &ArcIndex,
        cutoff: Cost,
        deadline: Instant,
        max_iters: u64,
        check_every: u64,
    ) -> FlowDualStop {
        let mut done = 0u64;
        let every = check_every.max(1);
        loop {
            if done >= max_iters {
                return FlowDualStop::Iterations;
            }
            if done % every == 0 && Instant::now() >= deadline {
                return FlowDualStop::Deadline;
            }
            if let Some(stop) = self.step(idx, cutoff) {
                return stop;
            }
            done += 1;
        }
    }

    /// One oracle call and one projected step. `Some(stop)` ends the ascent.
    fn step(&mut self, idx: &ArcIndex, cutoff: Cost) -> Option<FlowDualStop> {
        let (m, n) = (self.m, self.n);
        let k = self.sinks.len();

        let t0 = Instant::now();
        let mut value = 0.0;
        for kk in 0..k {
            let base = kk * m;
            let target = self.sinks[kk];
            dijkstra_into(
                idx,
                self.root,
                n,
                &self.lam,
                base,
                Some(target),
                &mut self.dist,
                &mut self.settled,
                &mut self.parent,
                &mut self.order,
                &mut self.heap,
            );
            let d = self.dist[target as usize];
            if !d.is_finite() {
                return Some(FlowDualStop::Converged);
            }
            value += d;
            build_flow(
                idx,
                self.root,
                &self.lam,
                base,
                target,
                &self.dist,
                &self.settled,
                &self.parent,
                &self.order,
                &mut self.amount,
                &mut self.grad,
            );
        }
        self.stats.oracle_calls += k as u64;
        self.stats.oracle_secs += t0.elapsed().as_secs_f64();
        self.value = value;
        if self.stats.iterations == 0 {
            self.stats.seed_value = value;
        }

        let ub = self.target.unwrap_or(cutoff);
        if self.delta.is_nan() {
            // The first level gap: what the incumbent leaves open, or a fraction
            // of the seed when there is no incumbent.
            self.delta = if ub.is_finite() && ub > value {
                ub - value
            } else {
                self.opts.blind_target_slack * value.abs().max(1.0)
            };
            self.stats.gamma = self.delta;
        }

        let mut restarted = false;
        if value > self.best_value {
            self.best_value = value;
            self.best_lam.copy_from_slice(&self.lam);
            self.stalled = 0;
        } else {
            self.stalled += 1;
            if self.stalled >= self.window {
                self.stalled = 0;
                self.delta *= 0.5;
                self.window = self.window.saturating_mul(2);
                self.stats.restarts += 1;
                // Restore the best iterate: a level gap that has been shown
                // unreachable was paid for by a step that moved `lambda` away
                // from the point that earned `best_value`, and continuing from
                // the worse point re-pays that cost at every later iteration.
                if self.opts.restart_on_stall {
                    self.lam.copy_from_slice(&self.best_lam);
                    for d in self.dir.iter_mut() {
                        *d = 0.0;
                    }
                    restarted = true;
                }
            }
        }
        self.stats.stalled_for = self.stalled;
        self.stats.gamma = self.delta;
        if self.best_value >= cutoff {
            return Some(FlowDualStop::Proved);
        }
        if !(self.delta > 1e-9 * self.best_value.abs().max(1.0)) {
            return Some(FlowDualStop::Converged);
        }

        // ---- direction: the supergradient, optionally deflected (CFM).
        let t1 = Instant::now();
        let mut norm2 = 0.0;
        if self.opts.deflection > 0.0 {
            let mut inner = 0.0;
            let mut prev2 = 0.0;
            for i in 0..self.grad.len() {
                inner += self.dir[i] * self.grad[i];
                prev2 += self.dir[i] * self.dir[i];
            }
            let _ = (inner, prev2);
            let beta = self.opts.deflection;
            for i in 0..self.grad.len() {
                let d = self.grad[i] + beta * self.dir[i];
                self.dir[i] = d;
                norm2 += d * d;
            }
        } else {
            for &g in self.grad.iter() {
                norm2 += g * g;
            }
        }
        if !(norm2 > 0.0) {
            return Some(FlowDualStop::Converged);
        }

        let mut aim = self.best_value + self.delta;
        if ub.is_finite() {
            aim = aim.min(ub);
        }
        let s = self.gamma * (aim - value) / norm2;
        if !(s > 0.0) || !s.is_finite() {
            return Some(FlowDualStop::Converged);
        }
        let _ = restarted;

        if self.opts.deflection > 0.0 {
            for i in 0..self.lam.len() {
                self.lam[i] += s * self.dir[i];
            }
        } else {
            for i in 0..self.lam.len() {
                self.lam[i] += s * self.grad[i];
            }
        }
        for g in self.grad.iter_mut() {
            *g = 0.0;
        }
        self.project_step();
        self.stats.step_secs += t1.elapsed().as_secs_f64();
        self.stats.iterations += 1;
        None
    }

    /// `Pi_Lambda` applied to the current iterate.
    ///
    /// The clamp to non-negativity is unconditional; the simplex projection runs
    /// only on arcs whose column sum exceeds the arc's cost, which is exactly the
    /// set on which `Pi_Lambda` is not the identity. A zero coordinate stays zero
    /// under the projection (`max(0 - theta, 0) = 0` for `theta >= 0`), so only
    /// the non-zero coordinates enter the sort.
    fn project_step(&mut self) {
        let (m, k) = (self.m, self.sinks.len());
        for x in self.load.iter_mut() {
            *x = 0.0;
        }
        for kk in 0..k {
            let base = kk * m;
            for a in 0..m {
                let v = &mut self.lam[base + a];
                if !(*v > 0.0) {
                    *v = 0.0;
                }
                self.load[a] += *v;
            }
        }
        self.over.clear();
        for a in 0..m {
            if self.load[a] > self.cost[a] {
                self.over.push(a as ArcId);
            }
        }
        self.stats.projected_arcs += self.over.len() as u64;
        for j in 0..self.over.len() {
            let a = self.over[j] as usize;
            let cap = self.cost[a];
            let mut z = 0usize;
            for kk in 0..k {
                let v = self.lam[kk * m + a];
                if v > 0.0 {
                    self.sorted[z] = v;
                    z += 1;
                }
            }
            if z == 0 {
                self.load[a] = 0.0;
                continue;
            }
            let theta = simplex_threshold(&mut self.sorted[..z], cap);
            let mut s = 0.0;
            for kk in 0..k {
                let v = &mut self.lam[kk * m + a];
                if *v > 0.0 {
                    *v = (*v - theta).max(0.0);
                    s += *v;
                }
            }
            self.load[a] = s;
        }
    }

    /// The level-set packing of the finished iterate.
    ///
    /// `max_nnz` caps the total number of vertex entries and `max_sets` the number
    /// of sets; the heaviest sets are kept first, and dropping the rest costs
    /// strength and never validity. Call [`Self::finish`] first.
    pub fn packing(&self, max_nnz: usize, max_sets: usize) -> CertifiedPacking {
        let mut out = CertifiedPacking::default();
        if !self.finished {
            return out;
        }
        let n = self.n;
        // (weight, commodity, threshold, size), heaviest first.
        let mut cand: Vec<(Cost, u32, Cost, u32)> = Vec::new();
        let mut vals: Vec<Cost> = Vec::with_capacity(n);
        let mut finite: Vec<Cost> = Vec::with_capacity(n);
        for kk in 0..self.sinks.len() {
            let d = &self.best_dist[kk * n..(kk + 1) * n];
            let big = d[self.sinks[kk] as usize];
            if !(big > 0.0) || !big.is_finite() {
                continue;
            }
            finite.clear();
            vals.clear();
            for &x in d.iter() {
                if x.is_finite() {
                    finite.push(x);
                    if x > 0.0 && x <= big {
                        vals.push(x);
                    }
                }
            }
            finite.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            vals.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
            vals.dedup();
            let mut prev = 0.0;
            for &v in vals.iter() {
                let w = v - prev;
                prev = v;
                if w > 0.0 {
                    let below = finite.partition_point(|&x| x < v);
                    cand.push((w, kk as u32, v, (finite.len() - below) as u32));
                }
            }
        }
        cand.sort_unstable_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
        let mut used = 0usize;
        let mut value = 0.0;
        for &(w, kk, thr, size) in cand.iter() {
            if out.sets.len() >= max_sets {
                break;
            }
            if size == 0 || used + size as usize > max_nnz {
                continue;
            }
            let d = &self.best_dist[kk as usize * n..(kk as usize + 1) * n];
            let members: Vec<NodeId> = (0..n as NodeId)
                .filter(|&v| {
                    let x = d[v as usize];
                    x.is_finite() && x >= thr
                })
                .collect();
            if members.is_empty() {
                continue;
            }
            used += members.len();
            value += w;
            out.sets.push((w, members));
        }
        out.value = value;
        out
    }
}

/// Force a multiplier vector into `Lambda` and re-derive `load` from it.
///
/// Every column is clamped non-negative; a column whose sum exceeds the arc's
/// cost is scaled down. This is the "repaired by scaling rather than trusted"
/// standard: after it returns, `sum_k lambda^k_a <= c_a` holds for every arc as
/// *recomputed*, whatever the caller did beforehand.
fn project_all(lam: &mut [Cost], cost: &[Cost], load: &mut [Cost], m: usize, k: usize) {
    for a in 0..m {
        let mut s = 0.0;
        for kk in 0..k {
            let v = &mut lam[kk * m + a];
            if !(*v > 0.0) {
                *v = 0.0;
            }
            s += *v;
        }
        if s > cost[a] {
            if s > 0.0 {
                let f = cost[a] / s;
                let mut s2 = 0.0;
                for kk in 0..k {
                    lam[kk * m + a] *= f;
                    s2 += lam[kk * m + a];
                }
                s = s2.min(cost[a]);
            } else {
                s = cost[a];
            }
        }
        load[a] = s;
    }
}

/// The threshold `theta >= 0` with `sum_i max(z_i - theta, 0) = cap`.
///
/// Standard: sort descending, take the largest `rho` with
/// `z_(rho) - (S_rho - cap)/rho > 0`. `z` is consumed (sorted in place).
fn simplex_threshold(z: &mut [Cost], cap: Cost) -> Cost {
    z.sort_unstable_by(|a, b| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));
    let mut sum = 0.0;
    let mut theta = 0.0;
    for i in 0..z.len() {
        sum += z[i];
        let t = (sum - cap) / (i as Cost + 1.0);
        if z[i] - t > 0.0 {
            theta = t;
        } else {
            break;
        }
    }
    theta.max(0.0)
}

/// Dijkstra from `root` under lengths `lam[base + a]`.
///
/// Leaves `dist`, `settled` (settle index, `u32::MAX` if unsettled), `parent` (the
/// settling in-arc) and `order` (the settle sequence) in place. Stops early once
/// `target` is settled; every vertex the shortest-path DAG to `target` can use is
/// settled by then, because such a vertex has a strictly smaller distance or was
/// settled earlier at the same distance.
#[allow(clippy::too_many_arguments)]
fn dijkstra_into(
    idx: &ArcIndex,
    root: NodeId,
    n: usize,
    lam: &[Cost],
    base: usize,
    target: Option<NodeId>,
    dist: &mut [Cost],
    settled: &mut [u32],
    parent: &mut [ArcId],
    order: &mut Vec<NodeId>,
    heap: &mut BinaryHeap<std::cmp::Reverse<(u64, NodeId)>>,
) {
    order.clear();
    heap.clear();
    for v in 0..n {
        dist[v] = Cost::INFINITY;
        settled[v] = u32::MAX;
        parent[v] = u32::MAX;
    }
    dist[root as usize] = 0.0;
    heap.push(std::cmp::Reverse((0u64, root)));
    while let Some(std::cmp::Reverse((db, v))) = heap.pop() {
        if settled[v as usize] != u32::MAX {
            continue;
        }
        let dv = f64::from_bits(db);
        settled[v as usize] = order.len() as u32;
        order.push(v);
        if Some(v) == target {
            return;
        }
        for &a in idx.outgoing(v) {
            let u = idx.head(a) as usize;
            if settled[u] != u32::MAX {
                continue;
            }
            let nd = dv + lam[base + a as usize];
            if nd < dist[u] {
                dist[u] = nd;
                parent[u] = a;
                heap.push(std::cmp::Reverse((nd.to_bits(), u as NodeId)));
            }
        }
    }
}

/// A unit `root -> target` flow on the shortest-path DAG, added into `grad`.
///
/// The DAG is the set of tight arcs `(u,v)` with `dist[u] + lambda_a = dist[v]`
/// and `u` settled before `v`; that restriction keeps it acyclic even when
/// zero-length arcs join equidistant vertices, and it always contains the
/// settling arc, so every vertex carrying flow has somewhere to send it.
#[allow(clippy::too_many_arguments)]
fn build_flow(
    idx: &ArcIndex,
    root: NodeId,
    lam: &[Cost],
    base: usize,
    target: NodeId,
    dist: &[Cost],
    settled: &[u32],
    parent: &[ArcId],
    order: &[NodeId],
    amount: &mut [Cost],
    grad: &mut [Cost],
) {
    for &v in order.iter() {
        amount[v as usize] = 0.0;
    }
    amount[target as usize] = 1.0;
    for i in (0..order.len()).rev() {
        let v = order[i];
        if v == root {
            continue;
        }
        let amt = amount[v as usize];
        if !(amt > 0.0) {
            continue;
        }
        amount[v as usize] = 0.0;
        let dv = dist[v as usize];
        let iv = settled[v as usize];
        let tol = 1e-9 * (1.0 + dv.abs());
        let mut count = 0usize;
        for &a in idx.incoming(v) {
            let u = idx.tail(a) as usize;
            let su = settled[u];
            if su == u32::MAX || su >= iv {
                continue;
            }
            if (dist[u] + lam[base + a as usize] - dv).abs() <= tol {
                count += 1;
            }
        }
        if count == 0 {
            // Cannot happen: the settling arc is tight and its tail settled
            // earlier. Kept as a guard so a numerical surprise degrades the
            // direction rather than losing the unit of flow.
            let a = parent[v as usize];
            if a == u32::MAX {
                continue;
            }
            grad[base + a as usize] += amt;
            amount[idx.tail(a) as usize] += amt;
            continue;
        }
        let share = amt / count as Cost;
        for &a in idx.incoming(v) {
            let u = idx.tail(a) as usize;
            let su = settled[u];
            if su == u32::MAX || su >= iv {
                continue;
            }
            if (dist[u] + lam[base + a as usize] - dv).abs() <= tol {
                grad[base + a as usize] += share;
                amount[u] += share;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::{dreyfus_wagner, dual_ascent_masked};
    use crate::graph::{DirectedGraph, NodeType, UndirectedGraph};
    use std::time::Duration;

    fn rng_from(mut seed: u64) -> impl FnMut() -> u64 {
        move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }
    }

    /// Small connected instances. `unit` makes every cost 1, which is the regime
    /// with the largest bidirected-cut integrality gap and therefore the one that
    /// can catch a bound claiming too much.
    fn random_instance(
        rng: &mut impl FnMut() -> u64,
        max_n: u32,
        unit: bool,
    ) -> (UndirectedGraph, Vec<NodeId>) {
        let n = 4 + (rng() % max_n as u64) as u32;
        let mut g = UndirectedGraph::new(n);
        let k = 2 + (rng() % 4) as u32;
        let mut terminals = Vec::new();
        for v in 1..=n {
            let t = v <= k.min(n);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            if t {
                terminals.push(v);
            }
        }
        // A spanning path guarantees connectivity; the rest is random.
        for v in 2..=n {
            let c = if unit { 1.0 } else { 1.0 + (rng() % 9) as f64 };
            g.add_edge(v - 1, v, c);
        }
        for u in 1..=n {
            for v in (u + 2)..=n {
                if rng() % 3 == 0 {
                    let c = if unit { 1.0 } else { 1.0 + (rng() % 9) as f64 };
                    g.add_edge(u, v, c);
                }
            }
        }
        (g, terminals)
    }

    /// The property the module exists for: *every* iterate is a valid bound.
    ///
    /// Checked at many iteration counts, not only at convergence, because the
    /// claim is that no repair step is needed and therefore that a run stopped by
    /// a clock is as sound as one stopped by convergence.
    #[test]
    fn every_iterate_is_a_valid_lower_bound() {
        let mut rng = rng_from(0xC0FFEE);
        let mut checked = 0;
        for case in 0..240 {
            let (ug, terminals) = random_instance(&mut rng, 8, case % 3 == 0);
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let opt = match dreyfus_wagner(&ug, &terminals) {
                Some(r) => r.optimal_cost,
                None => continue,
            };
            for iters in [0u64, 1, 2, 5, 13, 40, 200] {
                let mut fd = match FlowDual::new(
                    &idx,
                    terminals[0],
                    &terminals,
                    FlowDualOptions::default(),
                ) {
                    Ok(f) => f,
                    Err(_) => continue,
                };
                fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(30), iters, 1);
                let v = fd.finish(&idx);
                assert!(
                    v <= opt + 1e-6,
                    "case {case} iters {iters}: bound {v} exceeds optimum {opt}"
                );
                let p = fd.packing(1 << 20, 1 << 16);
                assert!(
                    p.verify(&idx, terminals[0], 1e-6),
                    "case {case} iters {iters}: level-set packing violates (PACK)"
                );
                assert!(p.value <= v + 1e-6, "packing {} above the bound {v}", p.value);
                checked += 1;
            }
        }
        assert!(checked > 500, "the gate never reached the code under test");
    }

    /// The seed is Wong's ascent, read as a point of this dual.
    #[test]
    fn the_seed_is_at_least_the_dual_ascent() {
        let mut rng = rng_from(0x5EED);
        let mut reached = 0;
        for case in 0..200 {
            let (ug, terminals) = random_instance(&mut rng, 9, case % 4 == 0);
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let active = vec![true; idx.num_arcs()];
            let asc = dual_ascent_masked(&idx, terminals[0], &terminals, &active).lower_bound;
            let mut fd =
                match FlowDual::new(&idx, terminals[0], &terminals, FlowDualOptions::default()) {
                    Ok(f) => f,
                    Err(_) => continue,
                };
            let v = fd.finish(&idx);
            assert!(
                v >= asc - 1e-6,
                "case {case}: seed {v} below the ascent it was built from, {asc}"
            );
            reached += 1;
        }
        assert!(reached > 100);
    }

    /// A run reproduces its value. Nothing in the method may depend on timing,
    /// hash order, or any other incidental of a container.
    #[test]
    fn a_run_reproduces_its_value() {
        let mut rng = rng_from(0x51EED);
        for _ in 0..60 {
            let (ug, terminals) = random_instance(&mut rng, 10, false);
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let run = || {
                let mut fd =
                    FlowDual::new(&idx, terminals[0], &terminals, FlowDualOptions::default())
                        .ok()?;
                fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(30), 60, 1);
                Some(fd.finish(&idx))
            };
            let (a, b) = (run(), run());
            assert_eq!(a.map(|x| x.to_bits()), b.map(|x| x.to_bits()));
        }
    }

    /// The pricing proposition, checked against *every* tree, exhaustively.
    ///
    /// `c(A) >= L + sum_{a in A} d_a` is claimed for every arborescence rooted at
    /// `root` that reaches the terminals. The gate enumerates every acyclic edge
    /// subset whose root component holds all terminals, orients it away from the
    /// root, and checks the inequality — so it tests the proposition itself and
    /// not one witness of it.
    #[test]
    fn the_pricing_bounds_every_arborescence() {
        let mut rng = rng_from(0x9917);
        let mut trees = 0u64;
        for case in 0..160 {
            let (ug, terminals) = random_instance(&mut rng, 5, case % 3 == 0);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                ug.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            if edges.len() > 15 {
                continue;
            }
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let root = terminals[0];
            let mut fd =
                match FlowDual::new(&idx, root, &terminals, FlowDualOptions::default()) {
                    Ok(f) => f,
                    Err(_) => continue,
                };
            fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(30), 60, 1);
            fd.finish(&idx);
            let (l, d) = fd.pricing();
            // arc cost -> the two arc ids of each edge
            let arc_of = |u: NodeId, v: NodeId| -> Option<ArcId> {
                (0..idx.num_arcs() as ArcId).find(|&a| idx.tail(a) == u && idx.head(a) == v)
            };

            let n = idx.num_nodes();
            for mask in 0u32..(1u32 << edges.len()) {
                let mut parent: Vec<usize> = (0..n).collect();
                fn find(p: &mut Vec<usize>, x: usize) -> usize {
                    let mut x = x;
                    while p[x] != x {
                        p[x] = p[p[x]];
                        x = p[x];
                    }
                    x
                }
                let mut acyclic = true;
                let mut chosen: Vec<(NodeId, NodeId)> = Vec::new();
                for (i, &(u, v, _)) in edges.iter().enumerate() {
                    if mask >> i & 1 == 0 {
                        continue;
                    }
                    let (a, b) = (find(&mut parent, u as usize), find(&mut parent, v as usize));
                    if a == b {
                        acyclic = false;
                        break;
                    }
                    parent[a] = b;
                    chosen.push((u, v));
                }
                if !acyclic {
                    continue;
                }
                let r = find(&mut parent, root as usize);
                if terminals.iter().any(|&t| find(&mut parent, t as usize) != r) {
                    continue;
                }
                // Orient away from the root; vertices outside the root component
                // are not part of the arborescence.
                let mut adj: Vec<Vec<NodeId>> = vec![Vec::new(); n];
                for &(u, v) in chosen.iter() {
                    adj[u as usize].push(v);
                    adj[v as usize].push(u);
                }
                let mut seen = vec![false; n];
                seen[root as usize] = true;
                let mut stack = vec![root];
                let (mut csum, mut dsum) = (0.0, 0.0);
                while let Some(x) = stack.pop() {
                    for &h in adj[x as usize].iter() {
                        if seen[h as usize] {
                            continue;
                        }
                        seen[h as usize] = true;
                        let a = arc_of(x, h).expect("arc missing");
                        csum += idx.cost(a);
                        dsum += d[a as usize];
                        stack.push(h);
                    }
                }
                assert!(
                    csum + 1e-6 >= l + dsum,
                    "case {case} mask {mask}: c(A)={csum} below L={l} + d(A)={dsum}"
                );
                trees += 1;
            }
        }
        assert!(trees > 10_000, "the gate enumerated only {trees} arborescences");
    }

    /// The bidirected cut relaxation's optimum, computed by writing *every* cut
    /// down, against what the ascent converges to.
    ///
    /// This is the gate the round's item 1 asks for — "on every instance where
    /// `LP*` is known exactly, the method's converged value must equal it" — run
    /// exhaustively on graphs small enough that `LP*` can be obtained by
    /// enumeration rather than by separation. Both halves are checked: the ascent
    /// never exceeds `BCR*` (validity, to floating tolerance) and it reaches it
    /// (convergence, to a relative tolerance the test reports).
    #[test]
    fn the_converged_value_is_the_bidirected_cut_optimum() {
        use highs::{RowProblem, Sense};
        let mut rng = rng_from(0xB0CD);
        let mut cases = 0;
        let mut worst: f64 = 0.0;
        for case in 0..90 {
            let (ug, terminals) = random_instance(&mut rng, 4, case % 3 == 0);
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let root = terminals[0];
            let nodes: Vec<NodeId> = ug.nodes.iter().map(|n| n.id).collect();
            let others: Vec<NodeId> = nodes.iter().copied().filter(|&v| v != root).collect();
            if others.len() > 12 {
                continue;
            }

            // BCR, every cut written down.
            let mut pb = RowProblem::default();
            let cols: Vec<_> = (0..idx.num_arcs())
                .map(|a| pb.add_column(idx.cost(a as ArcId), 0.0..))
                .collect();
            let mut rows = 0;
            for take in 1u32..(1u32 << others.len()) {
                let w: Vec<NodeId> =
                    others.iter().enumerate().filter(|(i, _)| take >> i & 1 == 1).map(|(_, &v)| v).collect();
                if !terminals.iter().any(|t| w.contains(t)) {
                    continue;
                }
                let inside: Vec<bool> = {
                    let mut m = vec![false; idx.num_nodes()];
                    for &v in &w {
                        m[v as usize] = true;
                    }
                    m
                };
                let entries: Vec<(_, f64)> = (0..idx.num_arcs() as ArcId)
                    .filter(|&a| inside[idx.head(a) as usize] && !inside[idx.tail(a) as usize])
                    .map(|a| (cols[a as usize], 1.0))
                    .collect();
                if entries.is_empty() {
                    continue;
                }
                pb.add_row(1.0.., &entries);
                rows += 1;
            }
            if rows == 0 {
                continue;
            }
            let mut model = pb.optimise(Sense::Minimise);
            model.set_option("output_flag", false);
            let solved = model.solve();
            if solved.status() != highs::HighsModelStatus::Optimal {
                continue;
            }
            let sol = solved.get_solution();
            let bcr: f64 = sol
                .columns()
                .iter()
                .enumerate()
                .map(|(a, &x)| x * idx.cost(a as ArcId))
                .sum();

            let mut fd = match FlowDual::new(&idx, root, &terminals, FlowDualOptions::default()) {
                Ok(f) => f,
                Err(_) => continue,
            };
            fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(60), 4000, 64);
            let v = fd.finish(&idx);
            assert!(v <= bcr + 1e-6, "case {case}: ascent {v} exceeds BCR* {bcr}");
            let rel = if bcr > 0.0 { (bcr - v) / bcr } else { 0.0 };
            worst = worst.max(rel);
            assert!(
                rel <= 2e-3,
                "case {case}: ascent stalled at {v} against BCR* {bcr} (relative {rel:.2e})"
            );
            cases += 1;
        }
        assert!(cases > 40, "the gate reached only {cases} instances");
        eprintln!("worst relative shortfall against BCR*: {worst:.3e} over {cases} instances");
    }

    /// The cutoff transformation, exhaustively, and the two halves of it that
    /// are *not* an equivalence.
    ///
    /// The fourteenth round's item 2 proposes: "solving the instance under costs
    /// `c` with cutoff `UB` is equivalent to finding a tree of `d`-cost at most
    /// `UB - L` in the graph weighted by `d`". Half of that is true and is what
    /// the search may use; the other half is false and the gate below is what
    /// says so.
    ///
    /// > **Proposition (cutoff transformation).** Let `(L, d)` be the pricing of
    /// > a feasible `lambda`. For every arborescence `A` rooted at `root` that
    /// > reaches the terminals,
    /// >
    /// > ```text
    /// > (i)   c(A) = d(A) + sum_{a in A} load(a)   and   c(A) >= L + d(A);
    /// > (ii)  c(A) <= UB  =>  d(A) <= UB - L;
    /// > (iii) the converse of (ii) fails.
    /// > ```
    /// >
    /// > *Proof.* (i) is the definition of `d` plus the weak-duality proposition.
    /// > (ii) is (i) rearranged. (iii) is exhibited below: `sum_{a in A} load(a)`
    /// > is not constant over arborescences, so a tree can be cheap in `d` and
    /// > dear in `c`. ∎
    ///
    /// So the `d`-graph with budget `UB - L` is a **relaxation** of the cutoff
    /// problem — every tree the original admits survives it — and searching there
    /// cannot lose an optimum, but a `d`-optimal tree need not be `c`-optimal and
    /// the two problems do **not** have the same optimal solution sets. The
    /// equivalence holds only in the limit the next gate tests.
    #[test]
    fn the_d_graph_budget_never_excludes_a_cheap_tree() {
        let mut rng = rng_from(0x2AA2);
        let (mut trees, mut converse_fails) = (0u64, 0u64);
        for case in 0..160 {
            let (ug, terminals) = random_instance(&mut rng, 5, case % 3 == 0);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                ug.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            if edges.len() > 15 {
                continue;
            }
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let root = terminals[0];
            let Ok(mut fd) = FlowDual::new(&idx, root, &terminals, FlowDualOptions::default())
            else {
                continue;
            };
            fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(30), 400, 1);
            fd.finish(&idx);
            let (l, d) = fd.pricing();
            let opt = dreyfus_wagner(&ug, &terminals).map(|r| r.optimal_cost);
            // Three cutoffs: tight, loose, and the optimum itself.
            for slack in [0.0, 1.0, 7.0] {
                let Some(o) = opt else { continue };
                let ub = o + slack;
                for (csum, dsum) in enumerate_arborescences(&idx, &edges, &terminals, root, &d) {
                    trees += 1;
                    if csum <= ub + 1e-9 {
                        assert!(
                            dsum <= ub - l + 1e-6,
                            "case {case}: a tree of c-cost {csum} <= {ub} has d-cost {dsum} \
                             above the residual budget {}",
                            ub - l
                        );
                    } else if dsum <= ub - l + 1e-9 {
                        // The converse: cheap in `d`, dear in `c`.
                        converse_fails += 1;
                    }
                }
            }
        }
        assert!(trees > 10_000, "the gate enumerated only {trees} arborescences");
        assert!(
            converse_fails > 0,
            "the converse never failed in {trees} trees: the transformation would be an \
             equivalence and the module documentation says it is not"
        );
    }

    /// A dual worth the optimum puts every optimal tree in the zero-price
    /// subgraph.
    ///
    /// > **Corollary.** If `L = OPT` then every optimal arborescence `A` has
    /// > `d(A) = 0`.
    /// >
    /// > *Proof.* `OPT = c(A) >= L + d(A) = OPT + d(A)` and `d >= 0`. ∎
    ///
    /// This is the statement item 2 is really after, and it is what makes the
    /// residual budget the whole difficulty: at a tight dual the problem becomes
    /// "find a tree of price zero". The converse is false and the gate does not
    /// assert it — a zero-price tree need not be optimal, because
    /// `sum_{a in A} load(a)` may exceed `L`.
    #[test]
    fn a_tight_dual_puts_every_optimal_tree_in_the_zero_price_subgraph() {
        let mut rng = rng_from(0x77EE);
        let mut tight = 0u64;
        for case in 0..200 {
            let (ug, terminals) = random_instance(&mut rng, 5, case % 3 == 0);
            let edges: Vec<(NodeId, NodeId, Cost)> =
                ug.edges.iter().map(|e| (e.src, e.dst, e.cost)).collect();
            if edges.len() > 15 {
                continue;
            }
            let dg = DirectedGraph::from_undirected(&ug);
            let idx = ArcIndex::new(&dg);
            let root = terminals[0];
            let Some(dw) = dreyfus_wagner(&ug, &terminals) else { continue };
            let Ok(mut fd) = FlowDual::new(&idx, root, &terminals, FlowDualOptions::default())
            else {
                continue;
            };
            fd.ascend(&idx, Cost::INFINITY, Instant::now() + Duration::from_secs(30), 2000, 8);
            let l = fd.finish(&idx);
            if l < dw.optimal_cost - 1e-6 {
                continue;
            }
            tight += 1;
            let (_, d) = fd.pricing();
            for (csum, dsum) in enumerate_arborescences(&idx, &edges, &terminals, root, &d) {
                if csum <= dw.optimal_cost + 1e-9 {
                    assert!(
                        dsum <= 1e-6,
                        "case {case}: an optimal tree has price {dsum} under a tight dual"
                    );
                }
            }
        }
        assert!(tight > 20, "the ascent reached the optimum on only {tight} instances");
    }

    /// Every arborescence rooted at `root` that reaches the terminals, as
    /// `(c-cost, d-cost)`.
    fn enumerate_arborescences(
        idx: &ArcIndex,
        edges: &[(NodeId, NodeId, Cost)],
        terminals: &[NodeId],
        root: NodeId,
        d: &[Cost],
    ) -> Vec<(Cost, Cost)> {
        let n = idx.num_nodes();
        let arc_of = |u: NodeId, v: NodeId| -> Option<ArcId> {
            (0..idx.num_arcs() as ArcId).find(|&a| idx.tail(a) == u && idx.head(a) == v)
        };
        let mut out = Vec::new();
        for mask in 0u32..(1u32 << edges.len()) {
            let mut parent: Vec<usize> = (0..n).collect();
            fn find(p: &mut Vec<usize>, x: usize) -> usize {
                let mut x = x;
                while p[x] != x {
                    p[x] = p[p[x]];
                    x = p[x];
                }
                x
            }
            let mut acyclic = true;
            let mut chosen: Vec<(NodeId, NodeId)> = Vec::new();
            for (i, &(u, v, _)) in edges.iter().enumerate() {
                if mask >> i & 1 == 0 {
                    continue;
                }
                let (a, b) = (find(&mut parent, u as usize), find(&mut parent, v as usize));
                if a == b {
                    acyclic = false;
                    break;
                }
                parent[a] = b;
                chosen.push((u, v));
            }
            if !acyclic {
                continue;
            }
            let r = find(&mut parent, root as usize);
            if terminals.iter().any(|&t| find(&mut parent, t as usize) != r) {
                continue;
            }
            let mut adj: Vec<Vec<NodeId>> = vec![Vec::new(); n];
            for &(u, v) in chosen.iter() {
                adj[u as usize].push(v);
                adj[v as usize].push(u);
            }
            let mut seen = vec![false; n];
            seen[root as usize] = true;
            let mut stack = vec![root];
            let (mut csum, mut dsum) = (0.0, 0.0);
            while let Some(x) = stack.pop() {
                for &h in adj[x as usize].iter() {
                    if seen[h as usize] {
                        continue;
                    }
                    seen[h as usize] = true;
                    let a = arc_of(x, h).expect("arc missing");
                    csum += idx.cost(a);
                    dsum += d[a as usize];
                    stack.push(h);
                }
            }
            out.push((csum, dsum));
        }
        out
    }
}
