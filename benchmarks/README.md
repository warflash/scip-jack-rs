# External benchmark suites

The repository keeps the small SteinLib B--E regression corpus in `tests/`. Larger external suites are acquired on demand so a normal checkout stays small and CI does not silently download or execute hundreds of long-running instances.

## PACE 2018

The pinned PACE 2018 archive contains:

- `Track1/`: 200 exact, few-terminal `.gr` instances;
- `Track2/`: 200 exact, low-treewidth `.gr` instances;
- `Track3/`: 199 heuristic instances after the organizers removed instance 58;
- `track1.csv` and `track2.csv`: exact objective values;
- `track3.csv`: lower and upper bounds.

The source repository is [PACE-challenge/SteinerTree-PACE-2018-instances](https://github.com/PACE-challenge/SteinerTree-PACE-2018-instances). The downloader pins commit `4df73cea9c311faea7d03e6d6bffa8733c34a1aa`; the archive SHA-256 is recorded in the script.

The expanded archive is roughly 210 MiB, so it is intentionally not committed to this repository. Download it with:

```powershell
powershell -ExecutionPolicy Bypass -File .\benchmarks\download_pace2018.ps1
```

This creates `benchmarks/pace2018/`. The PACE `.gr` format is accepted by the existing STP reader because it uses the same `Graph`/`Terminals` sections.

## DIMACS 11

Use the [DIMACS 11 downloads page](https://dimacs11.zib.de/downloads.html) for the SPG, Vienna, PUC-derived, GAPS, Copenhagen, and EFST suites. DIMACS has multiple variants and archives, so they are not downloaded automatically. Keep each downloaded archive and its source URL/hash beside the local copy when adding a campaign.

The published [DIMACS results PDF](https://dimacs11.zib.de/contest/challenge-results.pdf) is the external timing reference for the historical 2-hour, 1-thread and 8-thread campaigns.

## Running the current local campaign

The existing fixed-budget campaign remains the fast regression path:

```powershell
cargo run --release --bin ci_benchmark -- --budget-secs 180
```

Full B--E runs are available as ignored tests:

```powershell
cargo test --release --test steinlib_benchmark -- --ignored
```

External PACE/DIMACS campaigns should be opt-in and should emit per-instance status, runtime, primal value, dual bound, gap, and verification status. See [`BENCHMARK_REFERENCE_RESULTS.md`](../BENCHMARK_REFERENCE_RESULTS.md) for the comparison contract and published reference numbers.
