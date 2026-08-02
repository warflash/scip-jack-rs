#!/usr/bin/env bash
# Summarise one par_measure.sh CSV: proved, wrong, total seconds, unproved list.
#
#   benchmarks/summarize.sh <csv> [label]
#
# "Wrong" means the gate the notes state: a value differing from the reference
# *under an Optimal status*. An unproved instance whose incumbent sits above the
# optimum is not wrong, it is unproved, and conflating the two makes every A/B
# unreadable.
set -u
csv="${1:?csv}"
label="${2:-$(basename "$csv" .csv)}"
awk -F, -v label="$label" '
  NR == 1 { next }
  {
    n++
    secs += $6
    if ($5 == "Optimal") {
      proved++
      if ($3 != "" && int($3 + 0.5) != int($2 + 0.5)) {
        wrong++; bad = bad " " $1 "(" $3 "/" $2 ")"
      }
    } else {
      unproved = unproved " " $1
    }
  }
  END {
    printf "%-22s %3d/%-3d proved, %d wrong, %.1fs total\n", label, proved, n, wrong, secs
    if (wrong) printf "  *** WRONG UNDER Optimal:%s\n", bad
    if (unproved) printf "  unproved:%s\n", unproved
  }
' "$csv"
