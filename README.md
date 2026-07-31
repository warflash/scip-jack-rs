# scip-jack

A mathematically optimal Steiner tree problem solver implemented in Rust, based on the
directed cut formulation from the SCIP-Jack papers by Gamrath, Koch, Maher, Rehfeldt, and Shinano (ZIB).

## Goal

Implement a high-performance, exact solver for the Steiner Tree Problem in Graphs (STP) and its
variants using branch-and-cut with the directed cut formulation. The implementation targets
mathematical optimality — finding provably optimal solutions via integer programming techniques.

## Problem

Given an undirected connected graph G = (V, E), costs c : E → Q+ and a set T ⊂ V of terminals,
find a minimum weight tree S ⊆ G which spans T.

## Approach: Directed Cut Formulation

The solver transforms the undirected STP into a directed Steiner arborescence problem and solves
the following integer program:

```
min  c^T y

s.t. y(δ+(W)) ≥ 1,        ∀W ⊂ V, r ∈ W, (V \ W) ∩ T ≠ ∅
     y(δ⁻(v)) = 0,        if v = r
     y(δ⁻(v)) = 1,        if v ∈ T \ {r}
     y(δ⁻(v)) ≤ 1,        if v ∈ N
     y(δ⁻(v)) ≤ y(δ+(v)), ∀v ∈ N
     y(δ⁻(v)) ≥ y_a,      ∀a ∈ δ+(v), v ∈ N
     0 ≤ y_a ≤ 1,          ∀a ∈ A
     y_a ∈ {0, 1},          ∀a ∈ A
```

## Supported Problem Variants

- **STP** — Steiner Tree Problem in Graphs
- **SAP** — Steiner Arborescence Problem
- **RSMTP** — Rectilinear Steiner Minimum Tree Problem
- **NWSTP** — Node-Weighted Steiner Tree Problem
- **PCSTP** — Prize-Collecting Steiner Tree Problem
- **RPCSTP** — Rooted Prize-Collecting Steiner Tree Problem
- **MWCSP** — Maximum-Weight Connected Subgraph Problem
- **DCSTP** — Degree-Constrained Steiner Tree Problem
- **GSTP** — Group Steiner Tree Problem
- **HCSTP** — Hop-Constrained Steiner Tree Problem

## Architecture

```
src/
├── main.rs              # Entry point
├── graph/               # Graph data structures (directed/undirected)
├── model/               # Cut formulation and LP relaxation
├── preprocessing/       # Reduction techniques
├── separation/          # Cut separation (flow-cuts, Gomory, MIR)
├── heuristics/          # Primal heuristics (constructive, local search, recombination)
├── branch_and_bound/    # B&B tree management, branching rules, node selection
├── transformations/     # Problem variant transformations (NWSTP→SAP, PCSTP→SAP, etc.)
└── io/                  # Instance readers (STP format, SteinLib)
```

## References

- Gamrath, Koch, Rehfeldt, Shinano. "SCIP-Jack – A massively parallel STP solver." ZIB Report 14-35 (2014)
- Gamrath, Koch, Maher, Rehfeldt, Shinano. "SCIP-Jack – A solver for STP and variants with parallelization extensions." (2015)
- Koch, Martin. "Solving Steiner tree problems in graphs to optimality." Networks 32 (1998)
- Polzin. "Algorithms for the Steiner problem in networks." PhD thesis, Saarland University (2004)

## Papers

The `papers/` directory contains the reference PDFs and their extracted content (`EXTRACTED_CONTENT.md`)
with all mathematical formulations, transformations, and computational results.

## Benchmark comparisons

`BENCHMARK_REFERENCE_RESULTS.md` records the public PACE, DIMACS, SteinLib, and SCIP-Jack benchmark suites, including published solved counts, time limits, and runtime results. It also defines the end-to-end comparison protocol for adding external solver baselines.

`BENCHMARK_CERTIFICATION_GUIDE.md` defines the correctness and optimality-certification contract for those benchmarks.

## License

MIT
