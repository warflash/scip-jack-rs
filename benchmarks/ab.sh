#!/usr/bin/env bash
# Paired A/B: both binaries run back to back inside the same worker slot, so the
# two sides see the same machine state. Proved-counts on this benchmark are noisy
# because a cluster of instances finishes at 3-4s of a 5s budget; pairing removes
# the between-run component of that noise.
#   benchmarks/ab.sh <exeA> <exeB> <dir> <optcsv> <limit> <first> <last> [jobs]
set -u
A="$1"; B="$2"; dir="$3"; optcsv="$4"; limit="$5"; first="$6"; last="$7"; jobs="${8:-8}"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
export SJ_A="$A" SJ_B="$B" SJ_LIMIT="$limit" SJ_TMP="$tmp"
one() {
  IFS=$'\t' read -r i f name <<< "$1"
  local sa sb ta tb t0 t1
  t0=$(date +%s%N); sa=$("$SJ_A" "$f" -t "$SJ_LIMIT" 2>&1 | sed -n 's/^  Status: \([A-Za-z]*\).*/\1/p' | tail -1); t1=$(date +%s%N)
  ta=$(awk "BEGIN{printf \"%.2f\", ($t1-$t0)/1e9}")
  t0=$(date +%s%N); sb=$("$SJ_B" "$f" -t "$SJ_LIMIT" 2>&1 | sed -n 's/^  Status: \([A-Za-z]*\).*/\1/p' | tail -1); t1=$(date +%s%N)
  tb=$(awk "BEGIN{printf \"%.2f\", ($t1-$t0)/1e9}")
  printf '%s,%s,%s,%s,%s\n' "$name" "${sa:-none}" "${sb:-none}" "$ta" "$tb" > "$SJ_TMP/$(printf %04d "$i").row"
}
export -f one
i=0
while IFS=, read -r name opt; do
  name="${name// /}"; [[ "$name" == instance* || "$name" == [bcde][0-9]* ]] || continue
  num=$(printf '%s' "$name" | sed 's/[^0-9]*0*\([0-9]*\)\..*/\1/'); [[ -n "$num" ]] || continue
  (( num >= first && num <= last )) || continue
  [[ -f "$dir/$name" ]] || continue
  i=$((i+1)); printf '%s\t%s\t%s\n' "$i" "$dir/$name" "$name"
done < "$optcsv" | xargs -P "$jobs" -d '\n' -I{} bash -c 'one "$@"' _ {}
echo "instance,A,B,secsA,secsB"
cat "$tmp"/*.row 2>/dev/null
