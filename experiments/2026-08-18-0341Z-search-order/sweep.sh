#!/bin/bash
# sweep.sh --- run every (corpus, mode) pair as its own subprocess, appending
# rows to results.csv incrementally.  A 180 s timeout per run means one blowup
# costs one row (recorded as status=timeout), not the sweep.
#
# Usage: bash sweep.sh
set -u
cd "$(dirname "$0")"

DATA=/home/user/mini-stitch/stitch/data
OUT=results.csv

if [ ! -f "$OUT" ]; then
  echo "corpus,mode,max-arity,status,pops-expanded,pushed,considered,finished,utility,wall-ms,body" > "$OUT"
fi

run() { # corpus-file mode arity
  local f=$1 m=$2 a=$3
  local name; name=$(basename "$f" .json)
  # skip if this row already exists (lets the sweep resume after interruption)
  if grep -q "^$name,$m,$a," "$OUT"; then return; fi
  local line
  line=$(timeout 180 racket run-one.rkt "$f" "$m" "$a")
  if [ -z "$line" ]; then
    line="$name,$m,$a,timeout,,,,,,180000,"
  fi
  echo "$line" >> "$OUT"
  echo "done: $name $m arity=$a"
}

# basic corpora, minus the fused-lambda-tag ones the parser rejects
BASIC=$(ls "$DATA"/basic/*.json | grep -v -e simple3 -e simple4 -e simple5)
COGSCI="$DATA/cogsci/nuts-bolts.json $DATA/cogsci/wheels.json $DATA/cogsci/dials.json"

for f in $BASIC $COGSCI; do
  for m in best fifo lifo; do
    run "$f" "$m" 2
  done
done

# arity-3 sweep over data/basic only (run if the arity-2 sweep was fast)
if [ "${ARITY3:-0}" = "1" ]; then
  for f in $BASIC; do
    for m in best fifo lifo; do
      run "$f" "$m" 3
    done
  done
fi
