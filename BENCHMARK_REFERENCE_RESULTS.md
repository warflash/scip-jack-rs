# Published benchmark reference results

This file records public benchmark suites and published solver results for the classical undirected Steiner Tree Problem in Graphs (STP). It is a reference for end-to-end testing, not a claim that historical numbers are directly reproducible on today's hardware.

Collected on 2026-07-31.

## How to interpret the numbers

There is no single universal "optimal implementation" speed. Different algorithms dominate different instance families: terminal-parameterized dynamic programming, treewidth dynamic programming, and branch-and-cut are not interchangeable baselines.

The most useful comparisons are:

1. solved instances at the same cutoff;
2. time to prove optimality, per instance;
3. final primal-dual gap when the cutoff is reached;
4. the distribution of runtime ratios on exactly the same instance files.

Machine and compiler details should still be recorded, but they are secondary interpretation metadata. A 10x or 100x gap across a broad suite is an algorithmic signal. A 1.5x gap is not decisive unless both runs use the same machine, build, thread count, and LP backend.

## PACE 2018: the cleanest exact challenge baseline

The [official challenge description](https://pacechallenge.org/2018/steiner-tree/) defines three tracks:

| Track | Problem regime | Instances | Limit | Exact? |
|---|---|---:|---:|:---:|
| A / Track 1 | Relatively few terminals | 200 | 30 minutes per instance | Yes |
| B / Track 2 | Relatively low treewidth, with a supplied decomposition | 200 | 30 minutes per instance | Yes |
| C / Track 3 | Large, difficult instances | 200 (one later removed) | 30 minutes per instance | No, heuristic |

The odd-numbered instances were public during the contest and the even-numbered instances were private. The complete corpus is now available in the [PACE instance repository](https://github.com/PACE-challenge/SteinerTree-PACE-2018-instances), including `track1.csv` and `track2.csv` with the solution values.

### Original competition results

The [PACE report](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.IPEC.2018.26) ranks submissions on the 100 private instances. The original results were:

| Track | SCIP-Jack solved | Best result | Best result other than SCIP-Jack |
|---|---:|---:|---:|
| A, few terminals | 93 / 100 | 95 / 100 | 95 / 100 |
| B, low treewidth | 92 / 100 | 92 / 100 | 77 / 100 |

The Track C result was heuristic rather than an exact solved-count comparison. SCIP-Jack's reported average ratio was `99.85 / 100`; the winning team reported `99.93 / 100`.

### Later SCIP-Jack rerun

A later [official SCIP presentation](https://www.scipopt.org/20years/slides/rehfeldt.pdf) reports updated results using SoPlex:

| Track | SCIP-Jack, newer version | Average time | Older PACE version | Average time | Best other solved |
|---|---:|---:|---:|---:|---:|
| A | 99 / 100 | 38 s | 94 / 100 | 111 s | 95 / 100 |
| B | 99 / 100 | 25 s | 92 / 100 | 132 s | 77 / 100 |

These are especially useful as an algorithm-level target because they use the same curated instances and the same 30-minute competition cutoff. They are still historical published results, not a promise about the current SCIP-Jack 2.2 binary.

## SCIP-Jack 2.0 on the 200 PACE exact instances

The [SCIP Optimization Suite 8 report](https://arxiv.org/abs/2112.08872) gives another PACE comparison with a one-hour limit per instance. It reports arithmetic mean time with timeouts counted as 3,600 seconds:

| Solver/configuration | Solved |
|---|---:|
| Commercial MIP solver | 67 / 200 |
| SPDP, best other PACE solver | 176 / 200 |
| SCIP-Jack with SoPlex | 198 / 200 |
| SCIP-Jack with Gurobi as LP solver | 199 / 200 |

The reported average-time speedups for SCIP-Jack/Gurobi were approximately 17.6x over SPDP, 96x over the commercial MIP baseline, and 1.9x over SCIP-Jack/SoPlex. The LP backend is part of the algorithmic configuration here; these should not be interpreted as a pure Rust-versus-C comparison.

The [current SCIP-Jack page](https://scipjack.zib.de/) says that version 2.2 is available on request, supports `.stp` and PACE `.gr` files, and can use SoPlex, CPLEX, Gurobi, or Xpress. For a current reference run, obtain the same version and record the LP backend separately.

## DIMACS 11: detailed per-instance timing data

The [DIMACS 11 downloads page](https://dimacs11.zib.de/downloads.html) collects the classical SPG instances used in the challenge, including SteinLib, Vienna, PUC-derived, GAPS, Copenhagen, and EFST families. It also provides a machine calibration program.

The official [competition results PDF](https://dimacs11.zib.de/contest/challenge-results.pdf) is the strongest public source for full timing detail. The setup was:

- 2-hour per-instance limit;
- 1-thread and 8-thread categories;
- Intel Xeon X5672 at 3.20 GHz;
- 48 GB RAM;
- per-instance primal bound, gap, primal integral, and time tables.

For example, in the exact SPG, one-thread table, `e18-p` was solved by SCIP-Jack in 454.2 seconds with zero gap, while `i640-211-p` ended at about 7,200 seconds with a 0.9% gap. The PDF contains the complete rows rather than only aggregate solved counts. The [HTML result page](https://dimacs11.zib.de/contest/results/results.html) provides the high-level winners by variant.

## Older published SCIP-Jack SteinLib/DIMACS results

The [SCIP-Jack solver paper](https://dimacs11.zib.de/workshop/GamrathKochMaherRehfeldtShinano.pdf) used a 12-hour limit on Intel Xeon E5-2670 CPUs at 2.50 GHz with 32 GB RAM. Its appendix gives instance-wise results; the summary values below are shifted-geometric means and should be treated as historical reference points:

| Test set | Instances | Solved | Reported time |
|---|---:|---:|---:|
| SP | 8 | 6 | 4.7 s |
| I640 | 100 | 65 | 62.8 s |
| PUC | 50 | 8 | 330.1 s |
| Vienna-i-simple | 85 | 58 | 2,673.0 s |
| Vienna-i-advanced | 85 | 61 | 1,727.5 s |

The same paper reports that PUC was substantially harder than SP and I640: only 8 of 50 instances were solved within the limit. This is one reason PUC should be included in any serious regression suite.

## Current repository coverage

The repository currently contains 78 SteinLib instances:

| Family | Count | Structure |
|---|---:|---|
| B | 18 | Sparse random weights, roughly 50--100 nodes |
| C | 20 | Sparse random weights, roughly 500 nodes |
| D | 20 | Sparse random weights, roughly 1,000 nodes |
| E | 20 | Sparse random weights, roughly 2,500 nodes |

The local tests and three-minute CI campaign measure the Rust solver's runtime and bounds, but do not yet contain external solver timing records. The B--E families also represent only one broad random sparse-graph regime. The official [SteinLib catalog](https://steinlib.zib.de/testset.php) lists harder or structurally different families such as `SP`, `PUC`, `I640`, `LIN`, Vienna, and VLSI/grid sets.

Relevant local entry points are:

- [`tests/steinlib_benchmark.rs`](tests/steinlib_benchmark.rs), including the full ignored B--E campaigns;
- [`src/bin/ci_benchmark.rs`](src/bin/ci_benchmark.rs), the fixed three-minute campaign;
- [`BENCHMARK_CERTIFICATION_GUIDE.md`](BENCHMARK_CERTIFICATION_GUIDE.md), the correctness and portfolio contract.

## End-to-end comparison protocol

When external datasets are added, use this protocol:

1. Preserve the original instance bytes and record a SHA-256 hash.
2. Keep PACE odd instances as the development set and even instances as the report set, even though all are now public.
3. Run one process per instance with a fixed cutoff, first using one thread.
4. Record `status`, `time_secs`, `primal_bound`, `dual_bound`, `gap_pct`, nodes, LP solves, cuts, preprocessing time, and verification status.
5. Report solved count first, then median and shifted-geometric mean time, then the empirical runtime distribution.
6. For unresolved instances, report the final gap instead of treating timeout as a correctness failure.
7. Compare Rust against SCIP-Jack on the same files and configuration families. At minimum, run SCIP-Jack with SoPlex; if available, run its Gurobi configuration separately.

The important result is not a machine-normalized universal factor. It is the shape of the comparison: how many instances each solver proves, where the Rust solver falls behind, whether it finds comparable incumbents, and whether the gap closes as the implementation matures.

## Recommended adoption order

1. Add the complete PACE Track 1 and Track 2 files and solution-value CSVs as an opt-in research campaign.
2. Add the DIMACS/SteinLib `SP`, `PUC`, and `I640` families next; these are the most informative for reductions, separation, and lower bounds.
3. Add Vienna and one VLSI/grid family for structural diversity.
4. Keep the existing B--E campaign as a fast scale-regression suite rather than treating it as the complete state-of-the-art benchmark.
