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
6. An initial Wong-inspired dual-ascent and root-level reduced-cost fixing implementation now exists, but it is not yet proof-carrying or node-aware. The remaining missing ideas include implication/conflict reductions, alternative-based reductions, extended reductions, component-based formulations, and parameterized exact algorithms.

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

## 10. Second-pass gap analysis

This section separates three different meanings of “open”: an open theorem in the literature, an implementation omission that the literature already tells us how to attack, and a solver-specific correctness gap that can be closed without new theory.

### 10.1 Open problems explicitly identified by the papers

#### The BCR integrality gap is still not characterized

The old survey described a better-than-2 upper bound for the directed/bidirected cut relaxation as open. That part has since been partially resolved: Byrka, Grandoni, and Traub prove 1.9988, and Paschmanns and Traub improve the bound to 1.898. The latter paper also proves that the broad class of moat-growing dual certificates cannot certify a bound below 12/7.

This is a real mathematical frontier, not a missing code feature. The useful consequence for this project is a change of attack: do not spend effort trying to obtain the next improvement by merely tuning moat growth. The likely routes are a non-moat dual, a hybrid with the hypergraphic relaxation, or a structural theorem restricting the remaining bad instances.

#### Hypergraphic formulations are stronger but not yet a practical generic kernel

The survey explicitly calls for advanced implementations and decomposition techniques for hypergraphic formulations. The hypergraphic LP paper gives an important structural fact: although the formulation has exponentially many variables, basic solutions have sparse support, and partition/hypergraphic formulations have deep equivalences with directed-cut formulations.

The practical gap is branch-and-price-and-cut. A restricted primal master is not automatically a lower bound for the original STP, because omitting components can make a minimization problem artificially expensive. Certification must instead come from a feasible dual together with an exact pricing/separation proof for all omitted components. For small terminal subsets, Dreyfus-Wagner or Dijkstra-Steiner can provide that pricing proof; for general instances, this remains a difficult research problem.

#### The flow-formulation hierarchies have not been fully compared

The survey identifies an unfinished comparison between common-flow models and the path-length `MCF-lambda` hierarchy. The papers already show that neither family dominates the other in full generality. This is a good computational-mathematics target: enumerate small graphs, compute exact STP values and each LP value, and search for minimal separating examples. The resulting motifs can then guide a solver portfolio instead of forcing a false single-model choice.

#### Weighted Cut&Count remains a specialized parameterized gap

The PACE report notes that submissions largely avoided Cut&Count on edge-weighted instances and calls for practical or theoretical weighted versions. This is relevant to a treewidth-based dispatcher, but not to the main general-graph branch-and-cut engine. Rank-based dynamic programming is the more immediate deterministic path; weighted Cut&Count is a separate research project.

#### Exact reduction power for directed and variant models is less mature

The survey points out that the Steiner arborescence problem, especially with negative arc weights, has fewer advanced reduction techniques than undirected STP. This matters directly for PCSTP/RPCSTP/MWCSP transformations: a reduction valid in the original undirected instance is not automatically valid after adding artificial nodes, prizes, or negative transformed costs. The reduction library must carry a model-specific proof, not just a graph-level flag.

### 10.2 Gaps that look genuinely attackable here

#### A. Implement the stronger special distance, not just the weak bottleneck path

The current bottleneck reduction computes a path bottleneck through one original terminal. Rehfeldt and Koch define the bottleneck Steiner distance using the additive shortest-path metric on `T` together with the two edge endpoints:

```text
D = complete metric graph on T union {u,v}
s(u,v) = bottleneck distance from u to v in D
delete {u,v} if s(u,v) < c({u,v})
```

The current code is a valid but weaker test. Implementing `s(u,v)` is a concrete, theorem-backed improvement. A practical implementation can use shortest-path distances plus bottleneck queries on the metric closure, with caching over terminal subsets and edge endpoints. The first proof obligation is not difficult: any metric-closure path expands to a walk in the original graph, and the replacement argument from the paper preserves terminal connectivity.

The 2023 paper goes further and explicitly says that two criteria based on the implied bottleneck distance were not implemented. Those are an especially good target because the mathematical statements and proof strategy already exist; the work is faithful formalization, efficient data structures, and exhaustive small-instance validation.

#### B. Turn implications and conflicts into a certified cut system

The paper derives conflict sets from reduction ancestry and says they can generate IP cuts. The natural implementation is:

```text
pair conflict {e,f}:       x_e + x_f <= 1
conflict clique Q:         sum(x_e for e in Q) <= 1
implication e -> f:        x_e <= x_f
```

The subtlety is that some reduction statements preserve at least one optimum rather than every feasible integer solution. Therefore the solver should normalize the model with a lexicographic “minimum-cost, then minimum-support, acyclic” objective or attach the reduction certificate to the transformed instance. Once that boundary is explicit, conflict propagation becomes both safe and useful for branching.

#### C. Add a lower-bound certificate independent of the LP backend

This is the most promising near-term mathematical addition. Let `C_i` be any valid root-terminal cut, so every feasible directed solution satisfies

```text
sum(y_a for a in C_i) >= 1.
```

For nonnegative multipliers `lambda_i` satisfying

```text
sum(lambda_i for i with a in C_i) <= c_a       for every arc a,
```

we obtain the independently checkable lower bound

```text
LB = sum(lambda_i) <= sum(c_a y_a).
```

The proof is one line: multiply each cut inequality by `lambda_i`, sum, and dominate the resulting coefficient of every `y_a` by `c_a`. This is a valid dual packing certificate even if HiGHS is treated as an untrusted floating-point oracle. It can be stored with rational `lambda_i` and replayed exactly.

This does not replace the full LP bound, but it gives the project a reliable proof mode immediately. It also suggests a new separation objective: choose a small, high-value, low-overlap cut family rather than indiscriminately adding every violated cut.

#### D. Build a finite polyhedral microscope

For graphs with perhaps up to 8-10 vertices, enumerate connected graphs, terminal sets, and small integer edge costs. Compute:

1. the exact Steiner optimum by exhaustive tree/subgraph enumeration;
2. the current directed-cut LP;
3. common-flow and path-hierarchy LPs;
4. selected hypergraphic/partition bounds;
5. the cut-packing certificate value.

Canonicalize graphs up to isomorphism and store the smallest counterexample for every conjectured dominance relation. This will answer concrete questions that the papers leave broad: which constraints close the current model’s gap, which motifs defeat each hierarchy, and whether the solver’s hard benchmark instances are actually exhibiting known fractional obstructions. It is realistic to complete this experimentally and use it to formulate new theorems.

#### E. Finish the extended-reduction search rather than stopping at depth-first extension

The 2023 paper states that its implementation extends only from farthest leaves in a depth-first manner, while full backtracking is stronger but more expensive. That is an explicit accuracy/performance tradeoff. A solver-specific improvement is best-first extension with a proof budget:

```text
priority = lower bound on the cheapest completion of the partial extension
expand only while the proof can still beat the incumbent
memoize (contracted boundary, terminal pattern, ancestor-conflict state)
```

This keeps the reduction theorem unchanged while improving the amount of the search tree that can be ruled out. It is safer and more promising than inventing an unproved new reduction rule.

#### F. Use root choice correctly

The survey reports that the DCUT/MCF LP quality is invariant under the choice of root. Therefore root selection is not a route to a stronger mathematical bound for the current relaxation. It can still change separation order, cache behavior, branching symmetry, and primal heuristics. Root selection should be optimized for runtime and certificate sparsity, not evaluated as if it strengthens the LP polyhedron.

### 10.3 A concrete new theorem/program for this repository

The first research result I would try to establish is:

> **Cut-packing certificate theorem.** For every finite family of valid directed terminal cuts and every nonnegative rational packing of those cuts whose arc load does not exceed the arc cost, the packed value is a certified lower bound on STP.

The theorem itself is elementary; the novelty is turning it into a reusable certificate layer and combining it with implication/conflict-generated cuts. The program would be:

1. generate flow cuts;
2. solve a small rational cut-packing problem;
3. verify the arc-load inequalities exactly;
4. use the packed bound for pruning and for reduced-cost-style edge fixing;
5. compare its value and cost against HiGHS dual bounds on SteinLib/DIMACS instances.

If the gap is large, add valid conflict and partition cuts and repeat. This produces a measurable research curve before attempting a major hypergraphic pricing engine.

### 10.4 What I would not claim solved yet

I would not claim that the exact BCR gap, the full HYP-vs-DCUT relationship, or a general weighted Cut&Count algorithm has been solved by reasoning alone. Those require new proofs and likely new ideas beyond the current codebase. What we can solve now is the bridge between their results and a certifiable solver: implement the omitted reductions, add proof-carrying cut packing, mine minimal fractional obstructions, and use those obstructions to select or design stronger relaxations.

### 10.5 Audit of the new dual-ascent and verifier work

The current branch now contains `src/graph/algorithms/dual_ascent.rs`, root-level reduced-cost fixing, and an independent verifier. This materially advances the project, but three mathematical boundaries remain.

1. The dual-ascent routine is plausibly a valid ascent on directed terminal-cut inequalities when all arc costs are nonnegative: every raised set contains the root and excludes the currently processed terminal, and the residual-cost invariant is maintained. However, the result stores only the final residual costs and the scalar lower bound, not the actual cut sets and multipliers. It therefore cannot yet be independently replayed as a certificate. Store `(cut_set, terminal, multiplier)` records and check nonnegative multipliers, exact arc loads, and `sum(multiplier) = LB`.
2. Reduced-cost fixing is mathematically valid under that certificate. If `load_a` is the packed dual load on arc `a`, then any integer solution using `a` satisfies `c(y) >= LB + c_a - load_a`. Hence `LB + reduced_cost_a > UB` safely excludes `a`. The implementation should verify this inequality with the same exact/interval policy used for pruning, and should label the routine “Wong-inspired dual ascent” until equivalence with the exact algorithm in the 1984 paper is demonstrated.
3. The new independent verifier is not yet the solver’s incumbent firewall. The branch-and-bound solver still uses its older connectivity-only check before accepting heuristic solutions. Also, the new verifier checks directed acyclicity, whereas the original STP certificate should check the undirected projection for acyclicity, root indegree, non-root indegree constraints, orientation consistency, and objective-offset restoration after transformations. These are small but important proof gaps.

For example, the selected arcs `1->2`, `1->3`, `2->4`, `3->4` with terminal `4` form a directed acyclic graph and make the terminal reachable, but their undirected projection contains the cycle `1-2-4-3-1`. The verifier also does not reject the two selected arcs entering terminal `4`. A four-edge adversarial regression test of this form should be added before the verifier is called an exactness firewall.

The dual-ascent code also runs only at the root. The next mathematically safe extension is to rerun or warm-start the ascent after branch fixings, while retaining the root certificate as a global bound and recording each node certificate separately.

As a sanity check, I reimplemented the ascent invariant independently and tested it on 19,363 exhaustive connected unweighted cases up to five vertices plus 5,000 random weighted cases up to seven vertices. No lower bound exceeded the brute-force optimum and no tested reduced-cost fixing eliminated an optimal rooted orientation. This is evidence for the invariant, not a substitute for the missing replayable certificate.

The current integration suite also exposes a separate blocker: `cargo test --all-targets` reaches 45 passing unit tests, but `test_b07_fast` fails inside HiGHS with `invalid problem: Error` before producing a result. That does not disprove the dual-ascent bound, but it means the model-construction path is not yet robust enough for a correctness claim. The first checks should be for empty separation rows, self-loops created by degree-2 contraction, duplicate column indices in a row, and disconnected terminals after preprocessing. These should become explicit pre-solve assertions rather than backend-dependent failures.

## 11. Original mathematical research program

This is the part of the memo that is deliberately not a literature summary. The current proposal is mathematically non-optimal in a precise sense: it asks a rooted directed-cut relaxation to describe a tree, but directed cuts only describe terminal reachability.

They do not, by themselves, price the graphic-matroid fact that the optimum has no cycles, the multiway fact that \(k\) terminal regions need \(k-1\) connections, or the minimality fact that a terminal-free branch needs two exits. The lower-bound certificate proposed earlier also prices only elementary cuts.

The following constructions are the research direction I would lead. The validity proofs below are self-contained. Claims of global novelty are intentionally separated from claims that are already theorems: the constructions are new as a combined SCIP-Jack research program, while some of their ingredients are classical polyhedral facts.

### 11.1 Forest-closed BCR: make the relaxation describe a tree

Introduce one undirected variable \(x_e\) for each original edge \(e=\{u,v\}\), linked to the bidirected variables by

\[
x_e = y_{uv}+y_{vu}, \qquad 0\le x_e\le 1.
\]

The upper bound \(x_e\le 1\) is valid for the optimization problem with nonnegative costs: every optimal Steiner solution can be oriented with at most one direction of each original edge. Add the following valid tree closure:

\[
x(F)\le r_G(F) \qquad \text{for every }F\subseteq E,
\]

where \(r_G\) is the graphic-matroid rank function. The simple, cheaply separable first layer is the cycle closure

\[
x(C)\le |C|-1 \qquad \text{for every simple cycle }C.
\]

For every partition \(\mathcal P\) of \(V\) whose parts all contain a terminal, add the terminal-partition inequality

\[
x(\delta(\mathcal P))\ge |\mathcal P|-1.
\]

Finally introduce activation variables \(s_v\) for used vertices and add the minimal-tree perspective

\[
s_t=1 \ (t\in R),\qquad 0\le s_v\le 1,\qquad x_e\le s_u,\ x_e\le s_v,
\]

\[
\sum_{e\in E}x_e=\sum_{v\in V}s_v-1,
\qquad
x(\delta(v))\ge 2s_v\quad(v\notin R).
\]

The last inequality says that a selected nonterminal cannot be a leaf. It is valid for at least one optimum because a nonterminal leaf can be deleted without disconnecting a terminal and without increasing a nonnegative objective.

Call the resulting relaxation \(\mathrm{FC\text{-}BCR}\), for forest-closed BCR. It is not a claim that all these rows are new; partition and forest inequalities have a long polyhedral history. The new point is to make them a first-class closure around the bidirected formulation and to carry their dual prices into reductions and proof certificates.

The exactness argument is short. Given an optimal undirected Steiner tree, orient it away from the chosen root, set \(x\) to its edge incidence vector, set \(s\) to its used-vertex incidence vector, and all rows above hold. Therefore minimizing over \(\mathrm{FC\text{-}BCR}\) still gives a lower bound, while the optimum integer value is unchanged. The relaxation can be strictly stronger than a cut-only model because a fractional solution may satisfy every one-terminal cut while violating a cycle, a multiway partition, or the no-terminal-leaf closure.

Cycle separation is especially attractive. A cycle row is violated exactly when

\[
\sum_{e\in C}(1-x_e)<1.
\]

Thus a minimum-weight cycle problem with edge lengths \(1-x_e\) separates this first layer exactly. Full graphic-rank separation can be added later; it should not be a prerequisite for obtaining the first mathematically justified strengthening.

### 11.2 A new lower-bound object: matroid-corrected cut packing

The existing cut-packing certificate is sound but incomplete: it cannot exploit the fact that a tree is not allowed to use all edges of a cycle. The following is the certificate I would make the central lower-bound object.

Let \(a_C^\top x\ge 1\) be valid terminal-cut rows, \(p_P^\top x\ge b_P\) be valid partition or terminal-structure rows, and \(b_F^\top x\le r_F\) be selected forest-rank rows. Choose nonnegative multipliers \(\alpha_C,\beta_P,\gamma_F\) satisfying the edgewise domination condition

For the bidirected model, either keep the linking variables \(x\), or lift an undirected coefficient equally to the two arcs of its original edge. The certificate is then checked in the same variable space as the objective.

\[
\sum_C\alpha_C a_C
+\sum_P\beta_P p_P
-\sum_F\gamma_F b_F
\ \le\ c.
\]

Then every feasible tree vector \(x\) obeys

\[
c^\top x
\ge
\sum_C\alpha_C
+\sum_P\beta_P b_P
-\sum_F\gamma_F r_F.
\tag{MC}
\]

Proof:

\[
c^\top x
\ge
\left(\sum_C\alpha_C a_C
+\sum_P\beta_P p_P
-\sum_F\gamma_F b_F
\right)^\top x
\]

\[
\ge
\sum_C\alpha_C
+\sum_P\beta_P b_P
-\sum_F\gamma_F r_F.
\]

The first inequality uses the edgewise domination and \(x\ge 0\). The second uses the lower rows and the upper forest rows. This is a complete proof, not a heuristic interpretation of LP dual multipliers.

I call (MC) the **matroid-corrected cut-packing certificate**. The previous cut-packing certificate is the special case \(\beta=\gamma=0\). The new term \(-\gamma_F r_F\) is important: it allows the cut load to exceed the raw edge cost on a set that cannot be fully selected because of a forest rank constraint, while charging the certificate for that privilege. With only cycle rows this becomes a practical cycle-corrected certificate.

Define the certified slack

\[
\rho_e
=c_e-
\left(
\sum_C\alpha_C a_{C,e}
+\sum_P\beta_P p_{P,e}
-\sum_F\gamma_F b_{F,e}
\right)\ge 0.
\]

The same derivation gives the edge-fixing theorem

\[
x_e=1
\quad\Longrightarrow\quad
c^\top x\ge \mathrm{LB}_{\mathrm{MC}}+\rho_e.
\]

Consequently, if

\[
\mathrm{LB}_{\mathrm{MC}}+\rho_e>\mathrm{UB},
\]

then \(e\) can be fixed to zero. This is the mathematically correct generalization of reduced-cost fixing for a certificate that includes tree structure. It is materially stronger than using a scalar dual-ascent bound plus the raw cost of an edge.

The research question is not whether (MC) is valid; it is. The research question is how to choose a small, high-value support:

1. generate violated terminal cuts;
2. generate violated \(k\)-partition rows for small \(k\);
3. find short cycles or violated rank sets in the fractional support;
4. solve the multiplier problem over this finite certificate pool using rational coefficients;
5. add new rows only when they improve the certificate value per unit separation cost.

This turns “dual ascent versus LP dual” into one common mathematical object. It also prevents double-counting: two bounds are not added merely because they came from different algorithms; they are jointly validated by one coefficientwise inequality.

### 11.3 A solver-specific valid inequality that removes terminal-free dead branches

The minimal-tree argument yields a concrete inequality family that is not present in the current proposal. Let \(S\subseteq V\setminus R\) and let \(e\in E(S)\). For every inclusion-minimal Steiner tree \(T\),

\[
x_T(\delta(S))\ge 2x_{T,e}.
\tag{TF}
\]

To prove (TF), consider the connected component \(Q\) of \(T[S]\) containing \(e\). It contains no terminal. If \(Q\) had zero boundary edges, \(T\) would be disconnected. If it had one boundary edge, \(Q\) would be a terminal-free pendant subtree and could be removed while preserving terminal connectivity. Both cases contradict the definition of an inclusion-minimal optimum. Therefore \(Q\), and hence \(S\), has at least two boundary edges whenever \(e\) is selected.

For \(S=\{v\}\), the same proof gives the singleton row \(x(\delta(v))\ge 2s_v\). For larger \(S\), (TF) forbids a fractional or integral selected edge from hiding inside a terminal-free region with only one escape edge.

The rows can be separated exactly. For a fixed nonterminal edge \(e=\{u,v\}\), contract \(u\) and \(v\), make the terminals the sink side, and compute a minimum \(u\)-to-\(R\) cut with capacities \(x\). If its value is less than \(2x_e\), the corresponding source side is a violated (TF) row. Thus this is a genuine polynomial-time separation oracle, not an exponential reduction search.

This family is a good example of the distinction between “a tree is connected” and “a tree is a minimal connected object.” It attacks a failure mode that ordinary terminal cuts cannot see. Its scope must be restricted to nonnegative-cost STP or another model for which an inclusion-minimal optimum is guaranteed; it must not be copied blindly into a negative-cost arborescence transformation.

### 11.4 Replacing laminar moat duals with a non-moat certificate grammar

The recent BCR-gap papers make a sharp negative statement: a broad moat-growing class cannot certify below \(12/7\), even though the best general BCR upper bound is now \(1.898\). The conclusion for this project is not “improve moat-growing.” It is “change the dual language.”

The numerical frontier is from [Byrka--Grandoni--Traub](https://arxiv.org/abs/2407.19905) and [Paschmanns--Traub](https://arxiv.org/abs/2602.19879). The latter explicitly isolates the moat-growing barrier; the construction below is intended to leave that restricted proof class.

The proposed language is a **crossing-support dual grammar**:

1. a laminar cut-packing core for the easy regions;
2. a bounded number of crossing cut packets around a fractional obstruction;
3. terminal-partition rows for multiway mergers;
4. cycle/rank corrections for shared physical edges.

The dual support is allowed to be non-laminar by construction. When two growing terminal regions want to charge the same corridor, the certificate does not silently merge them. It records either a crossing cut packet or a partition row, and if the corridor is cycle-supported it records a rank correction. The resulting feasibility is checked by (MC), so the construction never relies on a geometric intuition about moats.

The concrete conjecture to test is:

> **Bounded-crossing obstruction conjecture.** After cycle closure and terminal-free boundary closure, every minimal fractional obstruction to a useful BCR lower bound either violates a small terminal partition inequality or admits a certificate whose cut-support crossing graph has bounded local width.

This is not claimed as a theorem. It is a falsifiable route to a theorem: enumerate minimal fractional extreme points on small graphs, compute their crossing graphs, and look for the smallest obstruction that defeats every \(k\)-partition plus cycle certificate. If the conjecture survives, the next proof target is a decomposition theorem saying that the remaining obstruction can be covered by a finite family of crossing packets. If it fails, the counterexample is more valuable than an average benchmark because it identifies the next missing facet type.

This is the route I would use to attack the authors' laminarity limitation. A universal exact BCR gap bound is still open, but the solver does not need to wait for that theorem: it can optimize over a certificate class that is strictly richer than moat growth and verify every resulting bound.

### 11.5 A mathematically safe bridge to the hypergraphic relaxation

Simply switching to a restricted hypergraphic master is not a lower-bound method. Omitting component variables from a minimization problem can increase the restricted optimum. The missing mathematical bridge is an omitted-column certificate.

This builds on the structural relation between partition/hypergraphic relaxations and BCR established by [Chakrabarty--Könemann--Pritchard](https://arxiv.org/abs/0910.0281); the proposed contribution is the certificate for safely using only a partial component system.

Let \(K\) be a full component spanning terminal set \(Q_K\), with cost \(c_K\). In the partition master, a partition \(\mathcal P\) receives contribution

\[
\eta_{\mathcal P}(K)
=\left|\{P\in\mathcal P:P\cap Q_K\ne\varnothing\}\right|-1.
\]

For dual partition multipliers \(\beta_{\mathcal P}\ge 0\), the component's dual price is

\[
\Phi_\beta(Q_K)
=\sum_{\mathcal P}\beta_{\mathcal P}\eta_{\mathcal P}(K).
\]

Suppose an oracle supplies a certified lower envelope \(\underline c(Q)\) satisfying

\[
\underline c(Q)\le c_K
\quad\text{for every full component }K\text{ on }Q.
\]

Then the restricted master is dual-feasible for every omitted component as soon as

\[
\underline c(Q)\ge \Phi_\beta(Q)
\quad\text{for every omitted terminal set }Q.
\tag{OP}
\]

Indeed, \(c_K-\Phi_\beta(Q_K)\ge \underline c(Q_K)-\Phi_\beta(Q_K)\ge0\). This is the exact missing proof condition.

The new algorithmic idea is to make \(\underline c\) heterogeneous:

1. exact Dreyfus-Wagner/Dijkstra-Steiner costs for small terminal subsets;
2. the forest-closed cut certificate for medium subsets;
3. a cheap metric or cut-packing lower bound for large subsets.

The dual then asks only for terminal sets where the lower envelope fails to dominate \(\Phi_\beta\). Exact pricing is performed on those sets; all other omitted components are certified away by (OP). This is a principled component-pricing scheme, not an unsafe “generate a few components and hope the restricted optimum is a bound.”

The open part is proving that the lower-envelope separation can be kept tractable on general instances. The bounded-terminal version is an immediate research target and directly connects the exact DP literature to the hypergraphic gap literature.

### 11.6 A general exchange-potential abstraction for stronger reductions

The implied bottleneck distance of Rehfeldt and Koch is powerful because it does more than compare two paths: it credits a local alternative that can be exchanged into an optimum. The next mathematical step is to abstract the credit rather than hard-code one bottleneck formula.

Call \(\pi(v,F)\ge0\) a local exchange potential if a separately checkable witness proves:

\[
\text{whenever an inclusion-minimal Steiner tree }S\text{ uses }v\text{ but omits }F,
\]

\[
\text{there is a Steiner tree }S'\text{ using an edge of }F
\text{ with }c(S')+\pi(v,F)\le c(S).
\tag{EP}
\]

The witness may be a single alternative edge, a small exact DP, or a packing of mutually compatible exchanges. Given (EP), define the cost of a replacement walk as its actual edge cost minus the exchange potentials whose witness sets are disjoint and therefore cannot be charged twice. Conditional on proving that compatibility/no-double-counting property, the usual remove-edge, reconnect-components, and exchange-at-intermediate-vertices proof yields:

\[
\text{if the potential-adjusted bottleneck distance between the endpoints of }e
\text{ is less than }c(e),
\]

\[
\text{then some optimum avoids }e.
\]

The proof obligation is explicit: every negative credit must have an exchange witness and a no-double-counting condition. Arbitrary LP reduced costs do not satisfy (EP) merely because they are nonnegative. They become useful only after being converted into local exchange witnesses.

This suggests a new **exchange packing oracle**. For a small neighborhood around \(v\), enumerate alternative connections, solve a packing problem for compatible swaps, and use its dual as \(\pi(v,F)\). The scalar maximum used in the existing implied-profit construction is then the one-witness special case. A multi-witness potential could strictly dominate it on graphs where several alternatives are jointly available but no single alternative is strong enough.

This is a real mathematical research target: prove a sufficient compatibility condition for exchange witnesses, then prove that the resulting potential-adjusted bottleneck distance dominates the current implied distance. The proof is local and therefore much more approachable than the global BCR integrality-gap problem.

### 11.7 Multi-root coupling: use root invariance as a strengthening, not a branching heuristic

The value of the basic BCR is invariant under the selected root, so changing the root alone cannot strengthen that relaxation. A different construction is to couple several root copies through one common undirected vector \(x\).

For a small root set \(Q\subseteq R\), introduce \(y^q\) for each \(q\in Q\) and impose

\[
y^q_{uv}+y^q_{vu}=x_{\{u,v\}}\qquad(q\in Q),
\]

with the rooted cut and arborescence constraints for every \(q\). Every tree is feasible: orient the same tree away from each root separately. The common \(x\) means the fractional solution must admit all these orientations simultaneously. The resulting projection is at least as strong as a single-root extended formulation; strictness is a testable question, not an assumption.

This is the STP analogue of the multi-root direction mentioned in the recent BCR literature for Steiner forest. The useful conjecture is modest:

> Two or three roots chosen from the terminal core may remove fractional orientation artifacts that survive one-root BCR, especially after forest closure.

The finite polyhedral microscope should decide whether this is a genuine strengthening or merely a more expensive representation of existing rows. Either result is useful: a strict example gives a new relaxation; a redundancy proof prevents wasted effort.

### 11.8 What can be claimed as solved, and what remains an open theorem

The following claims are now mathematically justified within this memo:

1. Forest, partition, activation, and terminal-free boundary rows preserve the optimum value of nonnegative-cost STP because every optimum has a minimal-tree representative.
2. The matroid-corrected certificate (MC) is a valid lower bound, and its certified slacks give a valid edge-fixing rule.
3. Terminal-free boundary rows have an exact min-cut separation oracle.
4. A restricted hypergraphic master is a lower bound only after the omitted-price condition (OP) is certified.

The following are not solved and should not be presented as solved:

1. the exact integrality gap of BCR;
2. a universal bound for the crossing-support grammar;
3. a complete polynomial-time separation oracle for the full forest-closed relaxation;
4. general full-component pricing;
5. a proof that the exchange-packing potential strictly dominates the implied bottleneck distance on all instances.

That distinction is the central research discipline. We can contribute new theorems and useful strict strengthenings without pretending that a 2026 open integrality-gap problem has disappeared.

### 11.9 The mathematical work order

The order I recommend for the research team is:

1. Prove and formalize \(\mathrm{FC\text{-}BCR}\), including the exact domain where the minimal-tree rows are valid.
2. Implement the mixed certificate LP over cuts, partitions, cycle rows, and terminal-free boundary rows; require exact replay of (MC).
3. Build the finite obstruction catalogue and record the smallest graph defeating each closure.
4. Test the bounded-crossing obstruction conjecture on those minimal examples.
5. Build the omitted-component envelope and prove pricing certificates for bounded terminal subsets.
6. Only then attempt a non-moat BCR-gap proof using the obstruction catalogue and crossing grammar.
7. Generalize reductions through exchange potentials, with a formal witness checker before any new credit is trusted.

The important shift is that the solver is no longer treated as “BCR plus papers.” It becomes an experimental laboratory for new polyhedral closures and proof systems. The first concrete mathematical deliverable is not another heuristic: it is a strictly stronger, independently certifiable relaxation and a counterexample-driven program for discovering the next missing inequality.
