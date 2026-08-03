#!/usr/bin/env bash
# The budget-invariance matrix: one binary, one slice, several time limits.
#
#   benchmarks/budget_matrix.sh <exe> <outdir> <tag> <dir> <optcsv> <first> <last> [jobs] [budgets...]
#
# Every proved-count in this repository used to be a claim about five seconds.
# This runs the same slice at several limits and emits one CSV per limit, named
# `<tag>@<limit>s.csv`, so the two assertions in `budget_gate.sh` can be checked:
#
#   1. the proved-count is *monotone in the budget* on every slice --- an
#      instance proved at 5 s must be proved at 30 s;
#   2. no change may be non-negative at 5 s while negative at 1 s or 30 s.
#
# The first is a property of one binary and is checked here; the second is a
# property of a *pair* and is checked by `budget_gate.sh` over two runs of this.
#
# Monotonicity is not a theorem about this solver --- a longer budget changes
# which stage runs when, and the 3--4 s finishing cluster makes any single pass
# noisy --- so a violation is reported as a *finding with its instances named*
# rather than as an assertion failure. What is inadmissible is a systematic
# violation, and naming the instances is what tells the two apart.
set -u
exe="${1:?solver executable}"
outdir="${2:?output directory}"
tag="${3:?tag}"
dir="${4:?instance directory}"
optcsv="${5:?optima csv}"
first="${6:-1}"
last="${7:-200}"
jobs="${8:-8}"
shift 8 2>/dev/null || shift $#
budgets=("$@")
if [[ ${#budgets[@]} -eq 0 ]]; then
  budgets=(1 5 30)
fi

here="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$outdir"

for b in "${budgets[@]}"; do
  csv="$outdir/$tag@${b}s.csv"
  bash "$here/par_measure.sh" "$exe" "$dir" "$optcsv" "$b" "$first" "$last" "$jobs" \
    > "$csv" 2>/dev/null
  bash "$here/summarize.sh" "$csv" "$tag@${b}s"
done

# Monotonicity within this binary: proved at a shorter budget => proved at a
# longer one. Reported per adjacent pair, with the regressing instances named.
prev=""
for b in "${budgets[@]}"; do
  cur="$outdir/$tag@${b}s.csv"
  if [[ -n "$prev" ]]; then
    awk -F, -v a="$prev_b" -v c="$b" '
      FNR == 1 { next }
      FILENAME == ARGV[1] { s[$1] = $5; next }
      { if (s[$1] == "Optimal" && $5 != "Optimal") { n++; bad = bad " " $1 } }
      END {
        if (n) printf "  !! %ss -> %ss: %d proved at %ss and not at %ss:%s\n", a, c, n, a, c, bad
        else   printf "  ok %ss -> %ss: monotone\n", a, c
      }
    ' "$prev" "$cur"
  fi
  prev="$cur"
  prev_b="$b"
done
