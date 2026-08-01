# scip-jack

`scip-jack` is a Rust research solver for the classical Steiner Tree Problem in
Graphs (STP). It uses a bidirected directed-cut relaxation, safe graph
reductions, dual-ascent bounds, primal heuristics, and branch-and-cut with
HiGHS.

This is a working solver prototype, not a complete reimplementation of
SCIP-Jack and not a general solver for every problem type named in the source
tree.

## Current solver pipeline

For a classical `.stp` instance, the top-level solver runs:

```text
read instance
  -> classical reductions
  -> Dreyfus-Wagner DP when the estimated work is small
     or dual ascent / reduced-cost pruning
  -> branch-and-cut for the remaining instance
  -> independent incumbent verification and bound reporting
```

The implemented STP path includes:

- `.stp` parsing for graphs, terminals, optional roots, coordinates, prizes,
  degree metadata, and hop metadata;
- degree, block/cut-vertex, nearest-vertex, bottleneck-Steiner-distance, and
  star-domination reductions, with contracted cost tracked as an objective
  offset;
- shortest-path, LP-guided, MST-pruning, key-path exchange, iterated-local-
  search, and recombination heuristics;
- Wong-style dual ascent with replayable in-memory certificates and
  reduced-cost arc/node fixing;
- a persistent HiGHS LP model with structural rows, a global cut pool, warm
  starts, and cut-pool ageing;
- flow, cycle, terminal-partition, and terminal-free-set cut separation;
- branch-and-bound with time/node limits, strong branching near the root,
  pseudo-cost feedback, and best-estimate node selection; and
- Dreyfus-Wagner exact dynamic programming for affordable small-terminal
  instances.

`Optimal` is reported only when the maintained primal and dual bounds meet the
configured tolerance. Costs and LP computations currently use `f64`, so this is
an engineering-level numerical result rather than a formal exact-arithmetic
proof. The internal verifier checks arc validity, cost consistency, reachability,
terminal coverage, directed acyclicity, and duplicate arcs.

## Usage

Run the command-line solver on a SteinLib-style instance:

```text
cargo run --release -- path/to/instance.stp --time-limit 60 --quiet
```

The objective value is written to standard output. Progress and bound
statistics are written to standard error. Available options include
`--time-limit`, `--node-limit`, `--gap`, `--quiet`, `--no-preprocess`, and the
separator switches `--no-cycle-cuts`, `--no-partition-cuts`, and `--no-tf-cuts`.

Use the library API through `scip_jack::solve`, `solve_file`, or the exported
`SolverConfig`.

## Scope and known gaps

The reader recognizes SAP, RSMTP, NWSTP, PCSTP, RPCSTP, MWCSP, DCSTP, and HCSTP
problem labels, and transformation functions exist for several of them. The
CLI and `solve_file` currently dispatch only the classical STP representation.
RSMTP conversion still returns a placeholder instead of a completed Hanan-grid
graph, and the variant transformations need checked artificial-node allocation
and end-to-end objective/solution restoration before they can be advertised as
supported.

The legacy `model::CutFormulation` helper also contains an unfinished max-flow
stub; the active solver uses `model::LpRelaxation` together with the separators
under `src/separation/` instead.

For the implementation audit, the current non-ignored test suite passes:
93 library tests, 6 integration tests, and 16 SteinLib checks; 5 longer
benchmark/certificate tests remain ignored. Run the suite yourself with:

```text
cargo test --all-targets
```

## Documentation

- [Mathematical research and implementation-status memo](SCIP_JACK_MATH_RESEARCH.md)
- [Paper index](papers/PAPER_INDEX.md)
- [Extracted paper content](papers/EXTRACTED_CONTENT.md)
- [Benchmark reference results](BENCHMARK_REFERENCE_RESULTS.md)
- [Benchmark certification guide](BENCHMARK_CERTIFICATION_GUIDE.md)

## License

MIT
