# Benchmark optimality and certification guide for agents

This document is the execution contract for improving benchmark truthfulness in this repository. It is about distinguishing a known reference value from a mathematically certified optimum. It is not permission to change benchmark numbers simply because the current solver obtains a different result.

The central rule is:

> For one fixed instance, a result may be called 'Optimal' only when a verified feasible primal solution and an independently verified lower bound meet at the same value.

The research context and mathematical rationale are in [SCIP_JACK_MATH_RESEARCH.md](SCIP_JACK_MATH_RESEARCH.md).

## 1. Vocabulary agents must use

Do not use the word “optimal” for every good benchmark result. Use these meanings:

1. 'ReferenceOptimum': an externally published value believed or documented to be the exact optimum for a specific instance.
2. 'BestKnown': the best feasible value currently available, without a matching proof.
3. 'Target': a value used for regression or approximation testing.
4. 'SolverClaimedOptimal': the solver terminated with its internal 'Optimal' status.
5. 'CertifiedOptimal': a verified feasible solution and a verified lower-bound certificate agree.

Only 'CertifiedOptimal' is a mathematical claim made by this repository.

For a fixed instance \(I=(G,R,c)\),

\[
\operatorname{OPT}(I)=\min\{c(T):T\text{ is a feasible Steiner tree of }I\}.
\]

If an external reference value \(C\) is correct and the instance is unchanged, no feasible tree can have cost below \(C\). A solver result below \(C\) is not an improvement; it is evidence of a changed model, a parser/transformation error, an invalid solution, an objective-offset error, or an incorrect reference.

## 2. Current repository problems to correct

The SteinLib values are stored in [tests/steinlib_benchmark.rs](tests/steinlib_benchmark.rs), in 'B_OPTIMA'. They are reference values for the particular SteinLib B01--B18 files, not universal mathematical limits.

The current tests are not exact-optimality tests:

1. 'is_proved_optimal()' requires only solver status plus a primal difference below '1.0'.
2. The ordinary benchmark tests accept a primal result up to approximately 5% above the reference value.
3. 'is_feasible()' checks that the result is not below the reference; it does not establish that it is close enough by itself.
4. 'test_dual_bounds_valid' checks only that the dual bound does not exceed the reference value. It does not require the dual bound to reach the reference.
5. 'proof_optimality_certificate' is ignored and still relies on floating-point values and solver-reported status.
6. 'tests/test_b01.stp' is a separate nine-node custom instance with value 9. It must not be confused with SteinLib 'tests/B/b01.stp', whose reference value is 82.

Agents must preserve the reference values unless they find an independently documented error in the instance or source. If a solver obtains a lower value, stop and investigate; do not update the reference table automatically.

## 3. Required benchmark metadata

Every benchmark record must identify the exact mathematical object being tested. At minimum, record:

~~~text
instance_id
source_family
file_path
file_sha256
problem_variant
node_count
edge_count
terminal_count
objective_offset
edge_cost_domain
reference_kind
reference_value
reference_source
certificate_status
~~~

For the current B-series, the edge costs and reference values are integral. Prefer an integer type for these values. Do not represent exact benchmark truth as 'f64' unless the checker also stores an exact integer or rational representation.

The instance hash is important. A reference value is attached to the bytes and semantics of one instance, not merely to a filename such as 'b01'.

## 4. Primal certificate requirements

Before a feasible value is used in an optimality claim, independently reconstruct the selected undirected edge set and verify:

1. every selected edge exists in the original instance;
2. no edge is selected twice;
3. every terminal is present and all terminals are connected;
4. the undirected selected support is acyclic, or redundant edges are removed before cost certification;
5. all selected vertices and edges are within the original instance after preprocessing;
6. the cost is recomputed from the original edge table, not trusted from a solver objective field;
7. every preprocessing or transformation offset is restored exactly once;
8. the selected directed arcs project to the claimed undirected tree consistently.

The primal certificate should contain the selected edge IDs and the exact recomputed cost. A floating-point objective copied from the LP backend is not a certificate.

For nonnegative edge costs, a connected feasible subgraph can be reduced to a tree without increasing cost. The checker should either receive a tree directly or perform this reduction explicitly and record what was removed.

## 5. Lower-bound certificate requirements

The lower bound must be independently checkable. Acceptable certificate families include:

1. an exhausted branch-and-bound tree in which every leaf has a verified bound at least the incumbent;
2. a feasible dual solution of the exact LP relaxation;
3. a replayable cut-packing certificate;
4. a replayable matroid-corrected certificate from the research program;
5. an exact dynamic-programming or exhaustive-enumeration certificate for small instances.

A scalar 'dual_bound' returned by the same untrusted floating-point solve is evidence, not a certificate.

For a cut-packing certificate, the checker must verify every multiplier, every cut, every arc/edge load, nonnegativity, and the claimed objective lower bound. For the matroid-corrected certificate described in the research memo, it must additionally verify:

\[
\sum_C\alpha_C a_C+
\sum_P\beta_P p_P-
\sum_F\gamma_F b_F\le c
\]

coefficient by coefficient, followed by

\[
\mathrm{LB}=
\sum_C\alpha_C+
\sum_P\beta_P b_P-
\sum_F\gamma_F r_F.
\]

If the coefficients are integral, scale the certificate to integers. Otherwise use rational arithmetic or outward intervals that prove the inequality in the safe direction.

## 6. Exact optimality contract

For a benchmark instance with reference value \(C\), the strict certification path is:

~~~text
read and hash the instance
normalize the problem variant
solve or load a primal certificate
verify the primal independently
recompute its exact cost P
solve or load a lower-bound certificate
verify the certificate independently
obtain exact/interval lower bound L
restore objective offsets
accept CertifiedOptimal only if P = L = C
~~~

With rational or integer costs, use exact equality. With arbitrary real input, use an interval proof:

\[
\underline{P}\le\operatorname{OPT}(I)\le\overline{P},
\qquad
\underline{L}\le\operatorname{OPT}(I),
\]

and certify only when the intervals force the same value. A tolerance may be used to decide when to rerun at higher precision; it must not be used to turn an unresolved gap into an optimality claim.

## 7. Test suite redesign

Separate approximation tests from certification tests.

### Approximation/regression tests

These may use the existing 5% threshold, but their names must say what they test:

~~~text
test_b01_within_reference_tolerance
test_b05_heuristic_quality
test_b07_finds_feasible_solution
~~~

They must not contain '_optimal' unless they prove optimality.

### Reference consistency tests

Add tests that:

1. verify every reference value is present exactly once;
2. verify the instance file exists;
3. verify node/edge/terminal counts against metadata;
4. verify the file hash if the repository pins the source files;
5. fail if a returned feasible value is below the reference value without an explicit reference-audit mode.

### Strict certification tests

Add a separate test path such as:

~~~text
test_b01_certified_optimal
test_b_series_certificate_regression
~~~

These tests must require:

~~~text
verified primal == verified lower bound
verified primal == reference value
certificate_status == CertifiedOptimal
~~~

Keep long-running certification tests ignored only when necessary, but make their output explicit. An ignored test is not evidence that the repository currently proves the benchmark.

### Adversarial tests

Include deliberately corrupted cases:

1. a disconnected set of selected arcs;
2. a directed acyclic support whose undirected projection contains a cycle;
3. two antiparallel arcs representing one undirected edge;
4. an objective offset applied zero times and twice;
5. a claimed lower bound larger than the exact optimum;
6. a primal solution one unit below the reference;
7. a duplicate or modified benchmark file with the same filename.

Each case must be rejected by the independent checker.

## 8. Status and reporting format

Benchmark output should distinguish at least:

~~~text
reference_value
best_feasible_value
verified_lower_bound
primal_certificate_valid
lower_bound_certificate_valid
objective_offset
optimality_status
runtime_seconds
nodes
lp_solves
~~~

Use statuses such as:

~~~text
ReferenceOnly
Feasible
BestKnown
CertifiedOptimal
CertificateInvalid
ModelMismatch
Unresolved
~~~

Do not print 'OPTIMAL' based only on a solver enum. Print 'OPTIMAL (CERTIFIED)' only after the independent contract succeeds. If a reference value is known but no local certificate exists, print 'REFERENCE OPTIMUM', not 'OPTIMAL (PROVEN HERE)'.

## 9. Agent implementation sequence

### Phase 1: inventory and naming

1. Locate every use of 'optimal', 'optimum', 'OPTIMAL', and 'B_OPTIMA'.
2. Separate reference values from solver claims.
3. Rename custom 'test_b01' identifiers so they cannot be confused with SteinLib B01.
4. Add benchmark metadata and exact integer reference storage.

### Phase 2: independent primal checker

1. Define a canonical undirected edge representation.
2. Recompute cost from the original instance.
3. Check terminal connectivity and undirected acyclicity.
4. Check preprocessing mappings and objective offsets.
5. Add the adversarial invalid-solution tests.

### Phase 3: independent lower-bound checker

1. Define a certificate file/data structure.
2. Implement exact replay for cut-packing certificates.
3. Add rational or interval comparisons.
4. Record certificate provenance at the node or root that generated it.
5. Reject missing, NaN, infinite, or inconsistent certificate values.

### Phase 4: benchmark contract

1. Change approximate tests to accurate names.
2. Add strict certification tests.
3. Make reference-underflow results fail loudly.
4. Make objective-offset mismatches fail loudly.
5. Report unresolved instances separately from failed instances.

### Phase 5: reproducibility

1. Pin instance hashes.
2. Record solver configuration and code revision.
3. Save primal and lower-bound certificates for certified cases.
4. Add a command that replays certificates without invoking the optimizer.
5. Run the full benchmark suite in a clean checkout.

## 10. Definition of done

This work is complete only when all of the following are true:

1. No approximate test is named as an optimality proof.
2. Every benchmark has an explicit reference classification.
3. Every certified optimum has a valid primal certificate and a replayable lower-bound certificate.
4. The checker recomputes objective values from original data and offsets.
5. A deliberately corrupted certificate is rejected.
6. A solver result below a reference value cannot silently pass.
7. A result above a reference value is reported as feasible or unresolved unless a separate exact proof establishes a different reference.
8. Benchmark output makes it impossible to confuse 'BestKnown', 'SolverClaimedOptimal', and 'CertifiedOptimal'.

The purpose of this document is not to make the benchmark suite appear stricter. It is to ensure that “optimal” means one precise mathematical fact and that every agent preserves that meaning.
