# SCIP-Jack: mathematical research memo

Status: 2026-07-31

This memo records the mathematical and algorithmic research direction for the Rust project in this repository. It is deliberately more critical than a normal implementation note: a fast solver and a mathematically certified solver are related, but they are not the same artifact.

## Executive conclusion

The project has the right high-level starting point for the classical Steiner tree problem in graphs (STP): bidirect the undirected graph, use a rooted directed arborescence-style model, and separate connectivity cuts by max-flow/min-cut. That is a legitimate branch-and-cut foundation.

It is not yet a 100%-correct SCIP-Jack reimplementation, nor can it currently claim a machine-checkable mathematical proof. The main blockers are:

1. The LP is rebuilt at every node and does not yet have the persistent cut pool, inherited cuts, or warm starts that make SCIP-Jack strong in practice.
2. The current Gomory and MIR separators are heuristic row transformations, not valid tableau-based Gomory/MIR separators. They must be disabled in an exact mode until they are replaced by certified separators.
3. Reliability branching and pseudo-cost data structures exist, but the branch-and-bound loop does not yet implement the complete strong-branching/pseudo-cost feedback cycle.
4. The solver uses `f64` for costs, LP coefficients, bounds, and certificates. This is acceptable for engineering, but not by itself for a mathematical proof.
5. Variant transformations and problem dispatch are incomplete. In particular, artificial-node identifiers can collide with one-based input identifiers, and RSMTP is still a placeholder.
6. Several of the strongest ideas in the modern Steiner-tree literature are not yet integrated: dual ascent, reduced-cost fixing, implication/conflict reductions, alternative-based reductions, extended reductions, component-based formulations, and parameterized exact algorithms.

The highest-value strategy is therefore an **exactness firewall**: keep a certified core containing only constraints, cuts, reductions, and bounds with explicit proofs; allow heuristic accelerators only when they return a verified primal solution or a verified lower bound and never let an uncertified operation prune the search tree.

## 1. Mathematical object being solved

For an undirected graph `G = (V, E)`, nonnegative edge costs `c`, and terminals `R`, STP asks for a minimum-cost connected subgraph spanning `R`. With nonnegative costs, an optimum can be taken to be a tree.

The standard directed construction replaces every undirected edge `{u,v}` by two arcs `(u,v)` and `(v,u)`, chooses a terminal `r` as root, and uses binary arc variables `y_a`. A typical directed cut relaxation is

```text
minimize        sum(c_a y_a) over a in A
subject to      y(delta+(U)) >= 1
                for every U with r not in U and U contains a terminal,
                0 <= y_a <= 1.
```

For integral variables, an arborescence-style formulation adds root indegree, terminal indegree, and Steiner-node predecessor/continuation constraints. The repository contains this family of constraints in `src/model/lp_relaxation.rs`; `src/separation/flow_cuts.rs` separates the exponentially many reachability inequalities by computing a minimum `r`-to-terminal cut in the fractional arc-capacity vector.

The separation theorem is simple and important:

```text
there is a violated cut for terminal t
    iff min-cut_y(r,t) < 1.
```

This is a valid polynomial-time separation oracle for the directed cut family. It is one of the parts of the current design that is mathematically sound, subject to correct max-flow implementation and numerical tolerances.

### What an exact result means

For a solver result to be a proof, it should be possible to retain:

```text
primal certificate: a feasible Steiner tree of cost UB
dual/lower-bound certificate: a verified lower bound LB
proof condition: LB = UB
```

At minimum, every pruning event must be justified by one of:

- a verified infeasibility certificate;
- a valid lower bound at least the incumbent cost;
- a valid reduction that preserves at least one optimum;
- an integral feasible solution whose cost is no better than the incumbent.

Floating-point tolerances can guide the computation, but they are not a proof system. The eventual exact mode should store rational or interval-certified values for every bound that can prune.

## 2. Repository audit

The audit baseline was 82 passing tests and 3 ignored tests. The project is a compact prototype, not yet the full SCIP-Jack architecture.

### Correct or promising foundations

- `src/model/lp_relaxation.rs`: rooted directed model with terminal indegree and Steiner continuation constraints.
- `src/separation/flow_cuts.rs`: one min-cut separation problem per non-root terminal.
- `src/graph/algorithms/max_flow.rs`: a working Edmonds-Karp-style implementation suitable as a reference oracle for small graphs.
- `src/branch_and_bound/solver.rs`: a recognizable branch-and-cut loop with a primal heuristic, LP bound, cut rounds, and branching.
- `src/preprocessing/distance.rs` and degree reductions: useful foundations for certified preprocessing.

### Correctness risks

#### Uncertified generic cuts

The current `src/separation/gomory.rs` and `src/separation/mir.rs` do not receive a simplex tableau, basis, or a mathematically valid aggregation certificate from HiGHS. They inspect arbitrary model rows and manufacture rounded coefficients. That is not enough to call a cut Gomory or MIR-valid.

A concrete failure mode is the valid binary row

```text
2 x1 + 3 x2 >= 4,    x1,x2 in {0,1}.
```

Using the current fractional scaling idea with `k = 3` produces the proposed inequality

```text
(1/6) x1 >= 1/3,
```

which is violated by the feasible binary point `(x1,x2) = (1,1)`. Therefore these separators must not be allowed to prune in exact mode. They should either be removed, replaced by a real tableau-based implementation, or treated as suggestions that are re-verified against a known valid inequality family.

#### Bounds and numerical proof

`Cost` is `f64`, and LP values, gaps, cut coefficients, and solution costs are also floating point. This creates risks involving near-integrality, equality tests, duplicate cuts, negative zero, NaN/Infinity propagation, and incorrect pruning at a tolerance boundary.

Recommended architecture:

```text
fast mode: f64 for speed, no claim of formal certification
certified mode: exact/rational input normalization or outward intervals
proof log: every accepted cut, reduction, bound, and incumbent verification
```

The certified mode does not need to solve every LP with an exact simplex implementation on day one. It can reconstruct or interval-check the final lower bound and re-check every pruning inequality with exact arithmetic.

#### Branching is incomplete

The code contains pseudo-cost arrays and a reliability-branching selection policy, but the solver does not yet update pseudo-costs from child-bound changes. Strong branching is represented by fractionality-based candidate selection rather than solving temporary child LPs. This means the implementation is not yet the reliability branching described by the literature.

Branching on directed arcs also exposes the bidirected symmetry. A stronger design branches on an undirected edge variable `z_e = y_{uv} + y_{vu}` and then handles orientation only when needed, or uses a symmetry-breaking disjunction that preserves the projection to the undirected problem.

#### Rebuilding the LP

The LP is constructed from scratch for each node. This loses:

- the global cut pool;
- ancestor cuts that remain valid in descendants;
- basis information and warm starts;
- dual multipliers useful for reduction and branching;
- reliable per-node LP statistics.

The `cuts_added` and `lp_solves` result fields are currently initialized or reported as zero rather than being fully wired through the solve loop. This makes performance diagnosis impossible and should be fixed before algorithmic comparisons.

#### Preprocessing and transformations

- The bottleneck code computes ordinary minimax path values. A true bottleneck Steiner-distance reduction needs the precise terminal-aware definition and a proof that the edge test preserves an optimum; it should remain disabled until that proof and tests are in place.
- `src/transformations/rsmtp_to_stp.rs` still contains a Hanan-grid TODO.
- PCSTP/MWCSP/RPCSTP transformations use `instance.num_nodes` as an artificial root identifier, which collides with the last one-based node identifier. Artificial IDs must come from a checked allocator outside the input ID range.
- The executable currently follows the basic STP path rather than dispatching all parsed problem types through their mathematically correct transformations.

## 3. Is the literature being mixed correctly?

The papers are complementary, but they answer different questions and should not be merged as if they described one relaxation.

| Research layer | Main contribution | How it should enter SCIP-Jack |
| --- | --- | --- |
| Formulations and polyhedra | Directed cut/BCR, undirected cut, flow, and equivalent formulations | Define the certified base LP and identify which inequalities are valid in its projection |
| Exact solver engineering | Branch-and-cut, reductions, parallel MIP infrastructure | Persistent model, global cuts, node processing, symmetry handling, statistics |
| Implications/conflicts/reductions | Strong preprocessing and alternative-based tests | Certified reductions before and during search, with dominance proofs |
| Dual ascent | Fast lower bounds, reduced costs, primal guidance | Root and node bounds, reduced-cost fixing, heuristic edge ranking |
| Dynamic programming/FPT | Exact algorithms parameterized by terminals, treewidth, or separators | Dispatch small-parameter instances away from generic branch-and-cut |
| Approximation and BCR gap theory | Integrality-gap structure and component algorithms | Guide which relaxation to strengthen; do not mistake approximation proofs for exact cuts |
| Variant transformations | PCSTP, RPCSTP, MWCSP, node-weighted, rectilinear variants | Separate transformation correctness from the core STP certificate |

The practical synthesis should be a portfolio solver with a common certificate interface, not a single monolithic model.

## 4. Literature map

### Direct SCIP-Jack and exact-solver foundations

- Gamrath, Koch, Maher, Rehfeldt, Shinano, *SCIP-Jack - A solver for STP and variants with parallelization extensions*. The repository copy is `papers/GamrathKochMaherRehfeldtShinano.pdf`. It is the closest engineering reference for the target solver family.
- Gamrath, Koch, Rehfeldt, Shinano, *SCIP-Jack - A massively parallel STP solver*, ZIB Report 14-35. The repository copy is `papers/ZR14-35.pdf`.
- Rehfeldt and Koch, *Implications, conflicts, and reductions for Steiner trees* (Mathematical Programming, 2023). This is the most important modern paper for strengthening exact preprocessing and node reductions. It reports a combination of implications, conflicts, and reductions that improves exact branch-and-cut performance.
- Ljubić, *Solving Steiner Trees - Recent Advances, Challenges, and Perspectives* (Networks, 2021). This is the best survey in the collected set for connecting formulations, approximation, exact methods, and variants.

### Formulations and lower bounds

- Goemans and Myung, *A Catalog of Steiner Tree Formulations* (Networks, 1993). Use it to keep the directed-cut, bidirected-cut, flow, and vertex-weighted formulations conceptually separate and to verify projection claims.
- Wong, *A Dual Ascent Approach for Steiner Tree Problems on a Directed Graph* (Mathematical Programming, 1984). This is the classic dual-ascent lower-bound and primal-guidance reference. The publisher/author mirrors were inaccessible during collection; metadata and the DOI are recorded in the paper index.

### Exact algorithms and parameterized structure

- Dreyfus and Wagner, *The Steiner Problem in Graphs* (Networks, 1971). The terminal-subset dynamic program is the baseline exact algorithm for small terminal sets.
- Hougardy, Silvanus, and Vygen, *Dijkstra meets Steiner: a fast exact goal-oriented Steiner tree algorithm* (2014). It improves practical DP with goal direction, pruning, and future-cost information.
- Bonnet and Sikora, *The PACE 2018 Parameterized Algorithms and Computational Experiments Challenge: The Third Iteration* (2019). It documents the treewidth/small-parameter ecosystem around modern Steiner algorithms.
- Jansen and Swennenhuis, *Steiner Tree Parameterized by Multiway Cut and Even Less* (2024). It suggests a useful dispatch parameter: a small terminal-separating multiway cut can be more informative than the raw number of terminals.

### Polyhedral strength and open approximation theory

- Byrka, Grandoni, and Traub, *The Bidirected Cut Relaxation for Steiner Tree has Integrality Gap Smaller than 2* (FOCS 2024 / arXiv 2407.19905). It proves a strict improvement over the long-standing factor-2 upper bound for BCR.
- Paschmanns and Traub, *The Bidirected Cut Relaxation for Steiner Tree: Better Integrality Gap Bounds and the Limits of Moat Growing* (2026 preprint, arXiv 2602.19879). It further improves the bound and studies where moat-growing arguments stop working.

These papers do not immediately give a stronger exact integer formulation. Their value for SCIP-Jack is diagnostic: they identify fractional structures that a strong relaxation or component pricing scheme must address.

### Prize-collecting and related variants

- Rehfeldt and Koch, *Reduction-based exact solution of prize-collecting Steiner tree problems* (ZIB Report 18-55, arXiv 1811.09068). Use this as the variant-specific reduction reference for PCSTP and related problems; the downloaded file is the 2018 preprint/report version of the later publication.

## 5. Highest-impact improvements

### P0: restore a defensible exact core

1. Add an `ExactnessPolicy` that rejects uncertified Gomory/MIR cuts and all uncertified reductions.
2. Replace the ad hoc separators with either valid named inequality families or a real solver-tableau interface. If HiGHS cannot expose a suitable tableau/certificate, do not call arbitrary row rounding Gomory/MIR.
3. Make all transformations total and type-safe. Allocate artificial nodes from `max_input_id + 1` with checked arithmetic, preserve a source-to-transformed mapping, and verify the objective offset.
4. Add independent verification of every returned tree: connectivity, terminal coverage, acyclicity after undirected projection, arc orientation consistency, and exact/recomputed cost.
5. Separate numerical status from proof status. A result should say `OptimalNumerically`, `OptimalCertified`, `Feasible`, `InfeasibleCertified`, or `Unknown`.

### P1: obtain the performance of a real branch-and-cut solver

1. Keep one LP object per search context and add child fixings incrementally. Maintain global and local cut pools.
2. Reuse bases/warm starts where supported by the LP backend.
3. Replace Edmonds-Karp with Dinic or push-relabel. Run terminal separations in parallel, cap the number of cuts per round, and prefer cuts with large violation or high efficacy.
4. Record LP solves, separation time, cut counts, child-bound changes, and per-family efficacy. Without these measurements, optimization is guesswork.
5. Implement real strong branching on a small candidate set, update pseudo-costs from measured child bound improvements, and use reliability thresholds only after those statistics exist.
6. Add dual-ascent lower bounds and use their reduced costs for edge fixing and heuristic ordering. Every fixing needs a bound proof of the form `LB_without_e + reduced_cost(e) > UB` or the appropriate variant-specific inequality.

### P2: add the reductions that the modern literature says matter

Implement and test, in this order:

- shortest-path and terminal-distance reductions;
- degree-1 and degree-2 reductions with explicit terminal cases;
- bottleneck/terminal-aware reductions only after formal proof and exhaustive small-graph testing;
- implication graphs and conflict propagation;
- bound-based reductions using dual ascent or LP reduced costs;
- alternative-based reductions that compare the best solution with and without an edge or node;
- extended reductions that reason about several possible replacement structures;
- connected-component and articulation decompositions.

Each reduction should expose a proof object or a small local certificate that an independent verifier can replay.

### P3: use the right exact algorithm for the instance

Build a dispatcher based on cheap structural probes:

```text
small |R|              -> Dreyfus-Wagner / Dijkstra-Steiner DP
small treewidth        -> treewidth-based DP
small terminal cut     -> multiway-cut parameterized algorithm
quasi-bipartite graph  -> component-based/BCR-specialized path
large general graph    -> persistent branch-and-cut + reductions
prize-collecting       -> dedicated PCSTP/RPCSTP framework
rectilinear geometry   -> validated Hanan-grid construction
```

The dispatch decision itself must be conservative: a specialized solver may return a certified bound or defer back to the generic engine, but it must not silently change the problem.

## 6. Novel research directions for this use case

These are proposed combinations or engineering-theory interfaces rather than claims that the literature has already solved them.

### A. A proof-carrying cut and reduction pipeline

Represent every operation as a typed certificate:

```text
CutCertificate { family, support, coefficients, rhs, proof_data }
ReductionCertificate { rule, affected_edges, local_witness, dominance_argument }
BoundCertificate { method, dual_variables_or_interval, objective_lower_bound }
```

The fast solver can generate candidates, while an independent checker validates them before they can change the incumbent or prune. This makes experimental inequalities safe to test and turns mathematical correctness into a software boundary rather than a convention.

### B. A common lower-bound currency

Dual ascent, LP dual solutions, min-cut capacities, and DP bounds currently live in separate modules. Normalize them into one `LowerBoundCertificate` interface with a composable operation:

```text
LB_total = max(LB_LP, LB_dual_ascent, LB_DP, LB_component, ...)
```

The max is safe when every component is a lower bound for the same normalized problem. This permits cheap bounds at every node and expensive bounds only when the gap justifies them.

### C. Adaptive formulation switching

Instead of choosing one relaxation globally, use a portfolio at the root and at selected nodes. Compare the dual bounds and the separation cost of:

- directed cut/BCR;
- undirected cut;
- flow or multicommodity formulations;
- component/partition-based restricted masters.

Keep only models whose lower-bound gain per unit time is positive. The exactness firewall makes switching safe: the model may change, but the certificate interface and objective normalization cannot.

### D. Component pricing with an exact small-terminal oracle

Use a restricted master over full Steiner components and price promising components with Dreyfus-Wagner or Dijkstra-Steiner on terminal subsets. A component formulation can attack the fractional structures highlighted by BCR-gap research while the DP oracle stays exact for bounded subset size. The open engineering problem is choosing a pricing order and stopping rule that gives a useful bound before enumerating too many components.

### E. Canonical cut signatures and cut-pool compression

Many terminal separations rediscover equivalent or nearly equivalent cuts across nodes. Canonicalize each cut by its source-side bitset, terminal class, and normalized support; store dominance relations and ancestor provenance. A research question is whether an efficiently maintained uncrossing/laminarization policy can reduce the cut pool without weakening the LP too much. This should be tested empirically first and promoted to a theorem only for the specific cut family and canonical-mincut rule used.

### F. Exactness-aware numerical reconstruction

Run the fast LP in double precision, then reconstruct a rational lower bound from the final LP basis/dual data when possible, or compute an outward interval around the objective and all cut slacks. If the interval cannot prove the required comparison, mark the node unresolved and re-solve with higher precision or a different formulation. This gives a practical path from HiGHS-based speed to a meaningful proof mode without requiring every node to use arbitrary precision.

### G. Symmetry-aware branching on undirected edges

Treat the two anti-parallel arcs of each original edge as one structural object. Branch first on `z_e = y_uv + y_vu`, then on orientation only if the LP needs it. Combine this with root selection symmetry: solve a few root choices at the root or select the root using terminal eccentricity/dual information, but preserve a certificate that all choices represent the same undirected optimum.

## 7. What remains unsolved

The most important open questions for this repository are:

1. Which combination of BCR/directed cuts, component inequalities, and modern reductions gives the best certified bound per second on the actual benchmark families?
2. Can dual ascent and LP duals be combined without double-counting or invalidly adding lower bounds?
3. What is the practical integrality gap of the current directed model after reductions, and which fractional motifs dominate its hard nodes?
4. Can a persistent LP with a global cut pool be made memory-safe in Rust while retaining reproducible proof logs?
5. What is the right exact arithmetic boundary: rational input scaling, interval LP verification, rational reconstruction, or an exact secondary checker?
6. Can the Dreyfus-Wagner, treewidth, and multiway-cut algorithms be integrated as certified subsolvers rather than separate executables?
7. Which SCIP-Jack reductions are independent, which dominate one another, and which become invalid after PCSTP/RPCSTP transformations?
8. What is the correct, fully specified RSMTP-to-STP transformation for the supported geometric dimensions, including coordinate duplicates, degeneracies, and objective preservation?
9. Can a benchmark harness produce adversarial instances specifically targeting each reduction, cut family, branching rule, and numerical tolerance?

## 8. Recommended implementation sequence

```text
Phase 1  Exactness firewall, variant ID allocator, solution verifier,
         disable uncertified generic cuts, wire statistics.

Phase 2  Persistent LP, inherited/global cut pools, warm starts,
         Dinic/push-relabel separation, real strong/reliability branching.

Phase 3  Dual ascent, reduced-cost fixing, certified implications,
         conflicts, alternative reductions, decomposition.

Phase 4  DP/treewidth/multiway-cut dispatcher and component pricing.

Phase 5  Rational/interval proof logs, independent checker, adversarial
         benchmark lab, and publication-quality reproducibility.
```

The project should not call itself mathematically proven until Phase 1 is complete and the proof checker can reject a deliberately corrupted cut, reduction, bound, or objective offset.

## 9. Collected papers

The PDF files and converted raw text are indexed in [`papers/PAPER_INDEX.md`](papers/PAPER_INDEX.md). The raw text is in UTF-8 text files under `papers/extracted/`, with page separators and the source filename preserved. The original PDFs are under `papers/downloads/`, except for the two papers already present at the top level of `papers/`.
