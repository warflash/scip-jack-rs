#!/usr/bin/env bash
# Per-instance measurement sweep, emitted as CSV.
#
#   benchmarks/measure.sh <exe> <track-dir> <csv-of-optima> <limit> <first> <last>
#
# Unlike benchmarks/pace.sh, which reports only a pass count, this records the
# quantities a change has to be judged against: what the reduction left, what the
# search settled, how many LP solves the certificate managed, and both bounds.
# It parses the solver's own verbose trace, so it works against any build --
# including the frozen control -- without the binary knowing it is being measured.
set -u
exe="${1:?solver executable}"
dir="${2:?instance directory}"
optcsv="${3:?optima csv}"
limit="${4:-5}"
first="${5:-1}"
last="${6:-200}"

echo "instance,opt,primal,dual,status,secs,red_V,red_E,red_R,root_LB,root_UB,ds_labels,cert_solves,cert_lp,method"
while IFS=, read -r name opt; do
  name="${name// /}"
  opt="${opt//[$'\r' ]/}"
  [[ "$name" == instance* || "$name" == [bcde][0-9]* ]] || continue
  num=$(printf '%s' "$name" | sed 's/[^0-9]*0*\([0-9]*\)\..*/\1/')
  [[ -n "$num" ]] || continue
  (( num >= first && num <= last )) || continue
  f="$dir/$name"
  [[ -f "$f" ]] || continue
  t0=$(date +%s%N)
  out=$("$exe" "$f" -t "$limit" -v 2>&1)
  t1=$(date +%s%N)
  secs=$(awk "BEGIN{printf \"%.3f\", ($t1-$t0)/1e9}")

  primal=$(printf '%s\n' "$out" | sed -n 's/.*Primal bound: \([0-9.-]*\).*/\1/p' | tail -1)
  dual=$(printf '%s\n' "$out" | sed -n 's/.*Dual bound: \([0-9.-]*\).*/\1/p' | tail -1)
  status=$(printf '%s\n' "$out" | sed -n 's/.*Status: \([A-Za-z]*\).*/\1/p' | tail -1)
  method=$(printf '%s\n' "$out" | sed -n 's/^Results (\(.*\)):.*/\1/p' | tail -1)
  # Last reduction report wins: it is the state the final pass actually solved.
  red=$(printf '%s\n' "$out" | sed -n 's/.*after [0-9]* rounds: |V|=\([0-9]*\) |E|=\([0-9]*\) |R|=\([0-9]*\) LB=\([0-9.]*\) UB=\([0-9.]*\).*/\1,\2,\3,\4,\5/p' | tail -1)
  [[ -n "$red" ]] || red=",,,,"
  # The search reports a running total, so the last line is the count.
  labels=$(printf '%s\n' "$out" | sed -n 's/.*\[dsearch\][^:]*: \([0-9]*\) labels.*/\1/p' | tail -1)
  solves=$(printf '%s\n' "$out" | sed -n 's/.*packing [0-9.]* over [0-9]* sets, \([0-9]*\) solves.*/\1/p' | awk '{s+=$1} END{print s+0}')
  certlp=$(printf '%s\n' "$out" | sed -n 's/.*\[certify\] lp bound \([0-9.]*\).*/\1/p' | tail -1)

  printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
    "$name" "$opt" "${primal:-}" "${dual:-}" "${status:-}" "$secs" \
    "$red" "$labels" "$solves" "${certlp:-}" "${method:-}"
done < "$optcsv"
