# SCIP-Jack: mathematical research and implementation status

Status: 2026-08-01

This memo is the mathematical companion to the repository. It records the
current implementation rather than the intended end state, and separates
valid lower bounds and reductions from engineering heuristics and unfinished
variant support.

## Executive summary

The repository now contains a credible exact-solver core for the classical
Steiner Tree Problem in Graphs (STP):

```text
Steiner instance
    -> safe classical reductions
    -> primal heuristics + Wong-style dual ascent
    -> reduced-cost elimination
    -> Dreyfus-Wagner DP or persistent-LP branch-and-cut
    -> incumbent verification and bound/status reporting
```

The core is materially beyond the original scaffold. It has a persistent LP,
global cut storage, flow/cycle/partition/terminal-free cut separation,
strong branching near the root, pseudo-cost feedback, replayable dual-ascent
checks, and several tested reductions.

It is still not a complete SCIP-Jack reimplementation and it does not yet
produce a formal machine-checkable proof. The main reasons are:

1. LP and certificate arithmetic is based on `f64` and HiGHS floating-point
   solves.
2. The active verifier checks a directed acyclic connected solution, but does
   not yet explicitly check that its undirected projection is a simple tree.
3. Several separation routines are deliberately bounded or heuristic in how
   many candidates they inspect; they are not complete separation oracles for
   every named inequality family.
4. Variant transformations are library scaffolding, not an end-to-end
   dispatch path. RSMTP is still a placeholder, and artificial-node allocation
   is not safe for one-based input IDs.
5. The reduction and certificate information is not exported as a durable
   proof log, and the solver has no exactness policy that rejects every
   uncertified operation before it can influence pruning.

The correct current claim is therefore: **a tested numerical exact solver for
many classical STP instances, with an active research program toward a
proof-carrying and broader variant solver**.

## 1. Mathematical problem and active model

For an undirected graph `G = (V, E)` with nonnegative edge costs `c` and
terminals `R`, STP asks for a minimum-cost connected subgraph spanning `R`.
Because costs are nonnegative, an optimum can be chosen as an inclusion-minimal
tree.

The active solver replaces every undirected edge `{u,v}` by arcs `(u,v)` and
`(v,u)`, chooses a terminal root `r`, and uses arc variables `y_a`. Its base
LP is a rooted directed-cut/arborescence relaxation:

```text
minimize       sum(c_a y_a)
subject to     y(delta+(W)) >= 1
               for root-containing W with a terminal outside W,
               y(delta-(r)) = 0,
               y(delta-(t)) = 1       for non-root terminals t,
               y(delta-(v)) <= 1      for Steiner nodes v,
               y(delta-(v)) <= y(delta+(v))
               y(delta-(v)) >= y_a   for every arc a leaving v,
               y_uv + y_vu <= 1,
               0 <= y_a <= 1.
```

The exponentially many directed cuts are added by separation rather than
enumerated. `src/model/lp_relaxation.rs` also contains the current
forest-closed strengthening block:

- continuous vertex-activation variables `s_v`, fixed to one for terminals and
  the root;
- `sum(y) = sum(s) - 1`, expressing the edge/vertex count of a tree;
- no-leaf inequalities for used Steiner vertices;
- edge/vertex coupling; and
- dynamically separated undirected cycle inequalities.

For an undirected edge, the model uses `x_e = y_uv + y_vu` in the strengthening
cuts. This makes the LP more tree-aware than a plain directed cut model, while
the branch-and-bound variables remain directed arcs.

### What is mathematically sound in the active design

- A max-flow/min-cut result with value below one is a valid violated directed
  reachability cut.
- The cycle inequality `x(C) <= |C| - 1` is valid for every simple undirected
  cycle.
- The terminal-free inequality `x(delta(S)) >= 2 x_e` is valid for a
  terminal-free set `S` and an internal edge `e` when solutions are restricted
  to inclusion-minimal nonnegative-cost trees.
- A partition inequality requiring at least `k - 1` crossing edges is valid
  when the partition has a root part and `k - 1` other terminal-containing
  parts.
- Wong-style dual ascent raises valid directed cut rows without allowing an
  arc's reduced cost to become negative. The lower bound is a feasible dual
  value for that fixed-root cut relaxation.
- A reduction can be composed with the next reduction when each pass preserves
  the optimum of the graph it receives. Contractions are accounted for through
  an objective offset.

These statements are validity arguments for the mathematical objects. They do
not make a floating-point execution a formal proof by themselves.

## 2. Repository audit: current implementation

### Implemented and active on the classical STP path

| Area | Current state | Evidence in the repository |
| --- | --- | --- |
| Input | SteinLib-style `.stp` reader for graph, terminals, optional root, coordinates, prizes, degree metadata, and hop metadata | `src/io/stp_reader.rs` |
| Classical reductions | Degree, bridge/block structure, nearest-vertex contraction, bottleneck Steiner distance, and star-domination vertex tests; deadline-aware loop; objective offsets | `src/preprocessing/` |
| Primal construction | Shortest-path growth, LP-guided support rebuilding, MST pruning, key-path exchange, iterated local search, and recombination | `src/heuristics/` |
| Dual ascent | Multi-root sampling, replayable ascent steps, reduced costs, dual-bound lifting for integral costs, and node-level ascent | `src/graph/algorithms/dual_ascent.rs`, `src/root_reduce.rs` |
| Reduced-cost fixing | Root and node fixings for arcs/nodes below an incumbent cutoff | `src/graph/algorithms/dual_ascent.rs`, `src/root_reduce.rs`, `src/branch_and_bound/solver.rs` |
| Small-instance exact method | Dreyfus-Wagner DP selected by an estimated `3^k n` plus graph-search work budget | `src/graph/algorithms/dreyfus_wagner.rs`, `src/solver.rs` |
| LP backend | HiGHS model built once per search; base snapshot/reset for nodes; incremental fixings; simplex basis reuse; lazy structural rows; global cut signatures and ageing | `src/model/lp_relaxation.rs` |
| Directed connectivity cuts | Flow/min-cut separation, including nested/back cuts and forced separation of integral disconnected points | `src/separation/flow_cuts.rs`, `src/graph/algorithms/max_flow.rs` |
| Tree-strengthening cuts | Simple-cycle, terminal-partition, and terminal-free-set separators | `src/separation/cycle_cuts.rs`, `partition.rs`, `tf_cuts.rs` |
| Search | Best-estimate node selection, arc branching, strong branching for shallow nodes, pseudo-cost updates, time/node limits, and incomplete-search handling | `src/branch_and_bound/` |
| Incumbent gate | Arc validity, cost recomputation, root reachability, terminal coverage, directed acyclicity, and duplicate-arc checks | `src/model/verifier.rs` |
| Statistics | Nodes, cuts, LP solves, primal/dual bounds, gaps, LP time, and status are wired into `SolveResult`/`SolverStats` | `src/solver.rs`, `src/branch_and_bound/solver.rs` |

### Present but incomplete or not active by default

| Area | Current limitation |
| --- | --- |
| Generic Gomory/MIR cuts | There are no active Gomory or MIR separators. The old ad-hoc row-rounding versions were removed because they were not tableau-based validity-preserving cuts. |
| Legacy cut formulation | `src/model/cut_formulation.rs` contains an older helper whose private max-flow method is still a TODO. It is not used by the active `LpRelaxation` pipeline. |
| Cut separation completeness | Flow cuts are the core connectivity oracle. Cycle, partition, and terminal-free separation inspect bounded candidate sets and stop after configured batches; this is practical strengthening, not a complete oracle for every inequality. The partition separator in particular needs an explicit partition witness/certificate before it can support a formal proof claim. |
| Exact arithmetic | Costs, LP values, reduced costs, tolerances, and certificates use `f64`. Integral-cost bound lifting is useful but does not replace exact or interval-certified arithmetic. |
| Certificate output | Dual-ascent steps can be independently replayed in memory, but the CLI emits no proof log, cut certificate, reduction certificate, or transformed-instance mapping. |
| Solution verification | The verifier checks directed acyclicity, not an explicit undirected-cycle test or an explicit in-degree-one condition for every used Steiner vertex. It also does not restore/check transformation objective offsets. |
| Branching symmetry | Branching is on directed arcs, so the anti-parallel representation still exposes orientation symmetry. Undirected-edge branching or a symmetry-breaking disjunction is not implemented. |
| Parallel search | The code has no parallel branch-and-bound or parallel separation portfolio. |
| Modern reductions | Implication/conflict, alternative-based, extended, and component-based reductions from the modern literature are not implemented. |

## 3. Top-level control flow and proof meaning

`src/solver.rs` is the actual entry point for solving an instance. It performs:

1. optional classical preprocessing;
2. an affordable-work check for Dreyfus-Wagner;
3. one or two rounds of `root_reduce::tighten`, combining primal heuristics,
   multi-root dual ascent, reduced-cost elimination, and more preprocessing;
4. exact DP on the reduced graph when still affordable; otherwise
   branch-and-cut; and
5. objective-offset restoration and final status recomputation.

`AscendAndPrune` is a real proof route for the numerical model when a valid
incumbent meets a valid dual bound after reductions. It is not merely a
heuristic label. However, the proof is currently represented by floating-point
values and internal data structures, not by a proof artifact that an external
checker can replay from the original input.

`BranchAndCutSolver` keeps one LP object for the search context. At a node it
restores the base state, applies node fixings, runs cheap dual ascent, solves
the LP, separates cuts, and either prunes, accepts a verified integral tree, or
branches. Cuts found by the current implementation are treated as globally
valid and deduplicated by their arc signature.

The solver is careful not to call an abandoned node pruned. If a time or node
limit interrupts unfinished work, the open node remains in the queue and the
result cannot claim optimality merely because the queue was temporarily empty.

### Bound invariant

For the current numerical execution, the intended invariant is:

```text
dual_bound <= optimum <= verified_primal_bound
```

The top-level solver clamps inconsistent merged bounds in the safe direction
and recomputes `Optimal` from the reported numbers. This protects reporting,
but it cannot repair an invalid cut, reduction, transformation, or floating-
point decision. The long-term design should retain the reason and certificate
for every bound-changing event instead of relying on the final clamp.

## 4. Reductions and dual ascent

### Classical preprocessing

`src/preprocessing/mod.rs` runs the following passes until no change, subject to
the deadline:

1. degree reductions and forced-edge contractions;
2. block and cut-vertex structure;
3. nearest-vertex contractions, including degree-one terminals;
4. bottleneck Steiner-distance edge deletion; and
5. bounded star-domination tests for nonterminal vertices.

The bottleneck test now supports terminal chains. It computes shortest-path
distances, terminal-metric bottleneck values, and conservative nearest-terminal
candidate lists. For large terminal sets it falls back to the single-terminal
case to avoid a dense matrix. Restricting candidates weakens the test but does
not invalidate it. Randomized brute-force tests check that the implemented
reduction does not change small-instance optima.

The reductions in the repository are not the full reduction system from
SCIP-Jack or from Rehfeldt and Koch. In particular, the removed implications
pass should not be described as currently available.

### Dual ascent

`dual_ascent_masked` implements a Wong-inspired ascent on directed terminal-cut
rows. Each step records a terminal and multiplier. `verify_certificate` rebuilds
the zero-reduced-cost set, reconstructs the cut, checks that the root is not in
the set, checks the cut is nonempty, checks the multiplier does not exceed the
current cut minimum, and checks that the final lower bound equals the sum of
steps.

The branch-and-cut root additionally seeds the LP with a bounded collection of
the ascent's own cut rows. This makes the LP's initial dual bound at least as
strong as the retained ascent packing, instead of asking the LP to rediscover
all those rows through separation.

Reduced-cost fixing is applied only against a known incumbent cutoff. Root
fixings are derived for one root, and the root-reduction code avoids unioning
oppositely oriented arc fixings from different roots. That distinction is
important: an undirected tree may orient the same edge differently from two
different roots.

The missing next step is a durable `LowerBoundCertificate` interface covering
dual ascent, LP bounds, min-cut rows, DP bounds, and reduction offsets. Each
operation that can delete an edge or prune a node should be replayable by an
independent checker.

## 5. Variant support audit

The parser recognizes these labels:

```text
STP, SAP, RSMTP, NWSTP, PCSTP, RPCSTP, MWCSP, DCSTP, HCSTP
```

Library transformation functions exist for NWSTP, PCSTP, RPCSTP, MWCSP, and a
placeholder RSMTP entry point. They are not wired into `solve_file` or the CLI;
the top-level path reads the generic instance and solves it as classical STP.

Known blockers:

- `transform_rsmtp` identifies coordinate values but still returns an empty
  instance instead of constructing a Hanan grid.
- Several transformations use `instance.num_nodes` as an artificial root ID.
  With one-based input IDs, this collides with the last original node. A checked
  allocator above the maximum actual input ID is required.
- The PCSTP transformation returns a `has_root_constraint` flag, but there is
  no active model/dispatch path that consumes and enforces the special root
  constraint.
- No end-to-end tests currently prove feasibility, objective-offset
  restoration, solution projection, and certificate preservation for the
  transformed variants.
- DCSTP and HCSTP are parsed as problem types but have no complete solver
  transformations or constraint implementation.

The variants should therefore be described as research scaffolding, not as
supported solver modes.

## 6. Test and benchmark evidence

At the audit date, `cargo test --all-targets` completed successfully with:

```text
93 library tests passed
6 integration tests passed
16 SteinLib checks passed
5 longer tests ignored
```

The ignored tests are the full B/C/D/E series runs and the longer proof-
certificate test. They are useful for local certification work but are not part
of the default quick suite.

The test suite currently covers, among other things:

- max-flow/min-cut behavior and flow-cut validity;
- Dijkstra and Dreyfus-Wagner results;
- dual-ascent replay, tampered-certificate rejection, and small random-graph
  lower-bound checks;
- reduction preservation by randomized/brute-force checks;
- cut-separator validity on emitted cuts;
- verifier rejection of disconnected, cyclic, or cost-inconsistent solutions;
- root-level optimality without branching;
- reference SteinLib optima, dual-bound validity, statistics wiring, and
  solution verification on selected B/C/D instances; and
- protection against false optimality reports under a tight time budget.

Passing tests are evidence for the tested cases and invariants. They are not a
proof that every floating-point LP state, every candidate separator, or every
transformation is mathematically correct.

## 7. Highest-value research work

### P0: make the exactness boundary explicit

1. Add an `ExactnessPolicy` and a result status that distinguishes numerical
   optimality, certified optimality, feasible-only results, and unknown.
2. Strengthen the incumbent verifier with undirected projection checks:
   simple-tree acyclicity, degree/in-degree conditions, orientation
   consistency, and exact recomputed cost.
3. Store proof records for dual-ascent steps, accepted cuts, reductions,
   contractions, objective offsets, and every pruning event.
4. Introduce exact or outward-rounded arithmetic at the certificate boundary.
   The LP can remain fast floating point initially if every bound used for
   pruning is independently reconstructed or interval-checked.
5. Remove, finish, or clearly quarantine the legacy `CutFormulation` helper so
   the repository has one unambiguous production model.

### P1: finish the classical solver architecture

1. Add global/local cut provenance and a true certificate-aware cut pool.
2. Replace arc branching with an undirected-edge disjunction where it preserves
   the directed formulation's projection and improves symmetry.
3. Make partition and terminal-free separation more principled and expose
   completeness/heuristic limits in their APIs.
4. Replace bounded Edmonds-Karp-style searches in the remaining separators with
   reusable Dinic or push-relabel workspaces where profiling justifies it.
5. Add independent lower-bound cross-checks against DP or enumeration on small
   graphs, including after reductions and objective-offset restoration.

### P2: integrate the literature that matters most

1. Implement implication/conflict and alternative-based reductions with explicit
   preservation proofs.
2. Add extended reductions only when their witnesses can be recorded and
   checked cheaply enough to use during search.
3. Add component-based bounds or a component-pricing route for instances where
   the directed-cut LP remains weak.
4. Use parameter-aware dispatch: Dreyfus-Wagner for small terminal sets and
   specialized treewidth/multiway-cut methods when those parameters are small.
5. Add a portfolio interface so a bound or primal solution from one method has a
   common verified representation when handed to another method.

### P3: complete variants safely

1. Implement a checked transformed-instance type with source maps and objective
   offsets.
2. Finish the Hanan-grid RSMTP construction and test 2D/3D coordinate cases.
3. Wire `ProblemType` dispatch through the transformation API.
4. Enforce PCSTP/MWCSP root/prize constraints in the target model and project
   solutions back to the source problem.
5. Add end-to-end optimal-value cross-checks for every supported transformation
   on tiny graphs.

## 8. Research questions that remain genuinely open

These are not merely missing code:

- What relaxation or certificate class gives the best practical trade-off
  between the current forest-closed directed model and hypergraphic/component
  formulations?
- Which fractional motifs dominate the remaining hard nodes after the current
  reductions and cycle/terminal-free closure?
- Can a useful non-laminar cut-packing certificate be found that is stronger
  than the current terminal-cut ascent while remaining cheaply checkable?
- When should a component oracle replace generic branch-and-cut, and how should
  its lower bound be certified against the original graph?
- How can modern approximation-gap structure guide exact separation without
  confusing an approximation argument with a valid integer-programming cut?

The exact BCR integrality gap, the full relationship with hypergraphic
relaxations, and a general parameterized algorithm for all relevant variants
remain research problems. The repository can investigate them experimentally,
but should not claim to have solved them.

## 9. Literature map

The local paper collection is indexed in `papers/PAPER_INDEX.md`. The most
direct references for this code are:

- Gamrath, Koch, Maher, Rehfeldt, and Shinano, *SCIP-Jack - A solver for STP
  and variants with parallelization extensions*;
- Gamrath, Koch, Rehfeldt, and Shinano, *SCIP-Jack - A massively parallel STP
  solver*;
- Wong, *A Dual Ascent Approach for Steiner Tree Problems on a Directed Graph*;
- Goemans and Myung, *A Catalog of Steiner Tree Formulations*;
- Dreyfus and Wagner, *The Steiner Problem in Graphs*;
- Rehfeldt and Koch, *Implications, conflicts, and reductions for Steiner
  trees*; and
- Ljubic, *Solving Steiner Trees - Recent Advances, Challenges, and
  Perspectives*.

The recent BCR integrality-gap papers in the collection are useful for
understanding fractional structure, but they do not by themselves provide a
drop-in exact integer formulation or a proof system for this repository.

## 10. Recommended implementation order

The practical order is:

```text
verifier and proof boundary
    -> checked transformations and offsets
    -> complete classical separation/reduction provenance
    -> stronger reductions and component bounds
    -> parameter-aware and variant-specific dispatch
```

The key principle is to keep every heuristic inside the exactness firewall:
heuristics may propose an incumbent, an ordering, or a candidate cut, but a
pruning decision must depend only on a verified feasible solution and a valid
lower-bound/reduction certificate.
