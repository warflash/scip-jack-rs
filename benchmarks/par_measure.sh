#!/usr/bin/env bash
# Eight-way-parallel per-instance measurement, emitted as CSV.
#
#   benchmarks/par_measure.sh <exe> <track-dir> <csv-of-optima> <limit> <first> <last> [jobs]
#
# Same fields as measure.sh, but the instances are farmed out to `jobs` workers
# and the rows are sorted back into instance order at the end. Every A/B in the
# notes since the ninth round is taken eight-way parallel on both sides, and a
# serial harness cannot reproduce those numbers: the contention costs roughly
# five Track 2 proofs. This is the harness that makes the two sides comparable.
set -u
exe="${1:?solver executable}"
dir="${2:?instance directory}"
optcsv="${3:?optima csv}"
limit="${4:-5}"
first="${5:-1}"
last="${6:-200}"
jobs="${7:-8}"

run_one() {
  local f="$1" name="$2" opt="$3" exe="$4" limit="$5"
  local t0 t1 out secs
  t0=$(date +%s%N)
  out=$("$exe" "$f" -t "$limit" -v 2>&1)
  t1=$(date +%s%N)
  secs=$(awk "BEGIN{printf \"%.3f\", ($t1-$t0)/1e9}")

  local primal dual status method red labels solves certlp
  primal=$(printf '%s\n' "$out" | sed -n 's/.*Primal bound: \([0-9.-]*\).*/\1/p' | tail -1)
  dual=$(printf '%s\n' "$out" | sed -n 's/.*Dual bound: \([0-9.-]*\).*/\1/p' | tail -1)
  status=$(printf '%s\n' "$out" | sed -n 's/.*Status: \([A-Za-z]*\).*/\1/p' | tail -1)
  method=$(printf '%s\n' "$out" | sed -n 's/^Results (\(.*\)):.*/\1/p' | tail -1)
  red=$(printf '%s\n' "$out" | sed -n 's/.*after [0-9]* rounds: |V|=\([0-9]*\) |E|=\([0-9]*\) |R|=\([0-9]*\) LB=\([0-9.]*\) UB=\([0-9.]*\).*/\1,\2,\3,\4,\5/p' | tail -1)
  [[ -n "$red" ]] || red=",,,,"
  labels=$(printf '%s\n' "$out" | sed -n 's/.*\[dsearch\][^:]*: \([0-9]*\) labels.*/\1/p' | tail -1)
  solves=$(printf '%s\n' "$out" | sed -n 's/.*packing [0-9.]* over [0-9]* sets, \([0-9]*\) solves.*/\1/p' | awk '{s+=$1} END{print s+0}')
  certlp=$(printf '%s\n' "$out" | sed -n 's/.*\[certify\] lp bound \([0-9.]*\).*/\1/p' | tail -1)

  printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
    "$name" "$opt" "${primal:-}" "${dual:-}" "${status:-}" "$secs" \
    "$red" "${labels:-}" "$solves" "${certlp:-}" "${method:-}"
}
export -f run_one

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

n=0
while IFS=, read -r name opt; do
  name="${name// /}"
  opt="${opt//[$'\r' ]/}"
  [[ "$name" == instance* || "$name" == [bcde][0-9]* ]] || continue
  num=$(printf '%s' "$name" | sed 's/[^0-9]*0*\([0-9]*\)\..*/\1/')
  [[ -n "$num" ]] || continue
  (( num >= first && num <= last )) || continue
  f="$dir/$name"
  [[ -f "$f" ]] || continue
  n=$((n + 1))
  printf '%s\t%s\t%s\n' "$f" "$name" "$opt"
done < "$optcsv" > "$tmp/list"

echo "instance,opt,primal,dual,status,secs,red_V,red_E,red_R,root_LB,root_UB,ds_labels,cert_solves,cert_lp,method"
# `xargs -P` with a bash -c wrapper: each line is one instance, workers are
# independent, and each writes one atomic short line to its own file.
export SJ_EXE="$exe" SJ_LIMIT="$limit" SJ_TMP="$tmp"
worker() {
  IFS=$'\t' read -r i f name opt <<< "$1"
  run_one "$f" "$name" "$opt" "$SJ_EXE" "$SJ_LIMIT" > "$SJ_TMP/$(printf %04d "$i").row"
}
export -f worker

i=0
while IFS=$'\t' read -r f name opt; do
  i=$((i + 1))
  printf '%s\t%s\t%s\t%s\n' "$i" "$f" "$name" "$opt"
done < "$tmp/list" | xargs -P "$jobs" -d '\n' -I{} bash -c 'worker "$@"' _ {}
cat "$tmp"/*.row 2>/dev/null
