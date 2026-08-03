#!/usr/bin/env bash
# The merge gate of item 0, over a control/candidate pair of budget matrices.
#
#   benchmarks/budget_gate.sh <outdir> <ctlTag> <candTag> [budgets...]
#
# Reads the CSVs `budget_matrix.sh` wrote and asserts the two properties that are
# conditions of every merge:
#
#   1. *monotone in the budget*, on each side separately: an instance proved at a
#      shorter limit is proved at a longer one;
#   2. *no budget trade*: the candidate may not be non-negative at 5 s while
#      being negative at 1 s or at 30 s.
#
# The second is the one that matters and it is the one the fourteenth round's
# deleted gate would have failed (SS98): a rule that reads "run this only where
# the branch-and-cut has been observed to solve no LP" is a statement about a
# time limit, and it switches the round's largest win off at any budget where
# every node solves LPs.
#
# Exit status is 1 when property 2 fails --- that is the merge gate. Property 1
# is reported with its instances named but does not fail the gate on its own,
# because a longer budget genuinely reorders the stages and the 3--4 s finishing
# cluster makes any single pass noisy; a *systematic* violation is visible in the
# named instances and is what a reader is being asked to judge.
set -u
outdir="${1:?output directory}"
ctl="${2:?control tag}"
cand="${3:?candidate tag}"
shift 3
budgets=("$@")
if [[ ${#budgets[@]} -eq 0 ]]; then
  budgets=(1 5 30)
fi

count() {
  awk -F, 'FNR > 1 && $5 == "Optimal" { n++ } END { print n + 0 }' "$1"
}
wrong() {
  awk -F, 'FNR > 1 && $5 == "Optimal" && $3 != "" && int($3 + 0.5) != int($2 + 0.5) { n++ } END { print n + 0 }' "$1"
}

fail=0
echo "budget   control  candidate  delta  wrongA wrongB"
deltas=()
for b in "${budgets[@]}"; do
  a="$outdir/$ctl@${b}s.csv"
  c="$outdir/$cand@${b}s.csv"
  if [[ ! -f "$a" || ! -f "$c" ]]; then
    echo "  (missing ${b}s: $a or $c)"
    deltas+=("NA")
    continue
  fi
  ca=$(count "$a"); cc=$(count "$c")
  wa=$(wrong "$a"); wb=$(wrong "$c")
  d=$((cc - ca))
  deltas+=("$d")
  printf "%5ss   %7d  %9d  %+5d  %6d %6d\n" "$b" "$ca" "$cc" "$d" "$wa" "$wb"
  if [[ "$wb" -gt 0 ]]; then
    echo "  *** candidate reports a value differing from its reference under Optimal at ${b}s"
    fail=1
  fi
done

# Property 1, both sides.
for side in "$ctl" "$cand"; do
  prev=""; prev_b=""
  for b in "${budgets[@]}"; do
    cur="$outdir/$side@${b}s.csv"
    [[ -f "$cur" ]] || { prev=""; continue; }
    if [[ -n "$prev" ]]; then
      awk -F, -v s="$side" -v a="$prev_b" -v c="$b" '
        FNR == 1 { next }
        FILENAME == ARGV[1] { p[$1] = $5; next }
        { if (p[$1] == "Optimal" && $5 != "Optimal") { n++; bad = bad " " $1 } }
        END {
          if (n) printf "  monotonicity %-10s %ss -> %ss: %d regressed:%s\n", s, a, c, n, bad
          else   printf "  monotonicity %-10s %ss -> %ss: ok\n", s, a, c
        }
      ' "$prev" "$cur"
    fi
    prev="$cur"; prev_b="$b"
  done
done

# Property 2: no budget trade.
mid=""
for i in "${!budgets[@]}"; do
  [[ "${budgets[$i]}" == "5" ]] && mid="${deltas[$i]}"
done
if [[ -n "$mid" && "$mid" != "NA" && "$mid" -ge 0 ]]; then
  for i in "${!budgets[@]}"; do
    d="${deltas[$i]}"
    [[ "$d" == "NA" ]] && continue
    if [[ "$d" -lt 0 ]]; then
      echo "  *** BUDGET TRADE: delta ${mid} at 5s but ${d} at ${budgets[$i]}s --- inadmissible"
      fail=1
    fi
  done
fi

if [[ "$fail" -eq 0 ]]; then
  echo "budget gate: PASS"
else
  echo "budget gate: FAIL"
fi
exit "$fail"
