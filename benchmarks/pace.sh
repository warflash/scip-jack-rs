#!/usr/bin/env bash
# Run a slice of a PACE 2018 track against its published optima.
#
#   benchmarks/pace.sh 1 5 1 40      # track 1, 5s limit, instances 1..40
#
# Instance numbers are the ones in the file names; the reference values come
# from benchmarks/pace2018/track<N>.csv.
set -u
track="${1:?track number}"
limit="${2:-5}"
first="${3:-1}"
last="${4:-200}"
exe=target/release/scip-jack.exe
dir="benchmarks/pace2018/Track${track}"

total_ns=0
proved=0
wrong=0
count=0
declare -a hard=()

while IFS=, read -r name opt; do
  name="${name// /}"
  opt="${opt//[$'\r' ]/}"
  [[ "$name" == instance* ]] || continue
  num=$(printf '%s' "$name" | sed 's/instance0*\([0-9]*\)\.gr/\1/')
  (( num >= first && num <= last )) || continue
  f="$dir/$name"
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
    hard+=("$num")
  fi
  if [[ "${val%.*}" != "${opt}" ]]; then
    wrong=$((wrong + 1))
    flag="$flag  *** WRONG: got ${val} want ${opt} ***"
  fi
  if [[ -n "$flag" || $ms -gt 500 ]]; then
    printf '%-16s %8sms  %-10s %10s / %-8s%s\n' "$name" "$ms" "$status" "$val" "$opt" "$flag"
  fi
done < "benchmarks/pace2018/track${track}.csv"

printf '\nTrack%s [%s..%s]: %d/%d proved optimal, %d wrong, total %d.%03ds\n' \
  "$track" "$first" "$last" "$proved" "$count" "$wrong" \
  $((total_ns / 1000000000)) $(( (total_ns / 1000000) % 1000 ))
if (( ${#hard[@]} )); then printf 'unproved: %s\n' "${hard[*]}"; fi
