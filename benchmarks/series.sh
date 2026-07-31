#!/usr/bin/env bash
# Run one SteinLib series against its reference optima under a per-instance
# time limit, and report the total wall clock. Usage:
#
#   benchmarks/series.sh C 5
#
# The reference values live in benchmarks/optima.txt as "<name> <value>".
set -u
series="${1:?series letter, e.g. C}"
limit="${2:-5}"
exe=target/release/scip-jack.exe

total_ns=0
proved=0
wrong=0
count=0
declare -a slow=()

while read -r name opt; do
  [[ "$name" == ${series,,}* ]] || continue
  f="tests/${series^^}/${name}.stp"
  [[ -f "$f" ]] || continue
  count=$((count + 1))
  t0=$(date +%s%N)
  out=$("$exe" "$f" -t "$limit" -q 2>&1)
  t1=$(date +%s%N)
  ns=$((t1 - t0))
  total_ns=$((total_ns + ns))
  val=$(printf '%s\n' "$out" | tail -1)
  status=$(printf '%s\n' "$out" | sed -n 's/.*Status: \([A-Za-z]*\).*/\1/p' | tail -1)
  gap=$(printf '%s\n' "$out" | sed -n 's/.*Gap: \([0-9.]*\)%.*/\1/p' | tail -1)
  ms=$((ns / 1000000))
  flag=""
  if [[ "$status" == "Optimal" ]]; then
    proved=$((proved + 1))
  else
    flag=" UNPROVED gap=${gap}%"
  fi
  if [[ "${val%.*}" != "${opt}" ]]; then
    wrong=$((wrong + 1))
    flag="$flag  *** WRONG: got ${val} want ${opt} ***"
  fi
  printf '%-6s %8sms  %-10s %10s / %-8s%s\n' "$name" "$ms" "$status" "$val" "$opt" "$flag"
  if (( ms > 1000 )); then slow+=("$name:${ms}ms"); fi
done < benchmarks/optima.txt

printf '\n%s: %d/%d proved optimal, %d wrong, total %d.%03ds\n' \
  "${series^^}" "$proved" "$count" "$wrong" $((total_ns / 1000000000)) $(( (total_ns / 1000000) % 1000 ))
if (( ${#slow[@]} )); then printf 'slow: %s\n' "${slow[*]}"; fi
