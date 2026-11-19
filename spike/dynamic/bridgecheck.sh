#!/bin/sh
# Checks every generated bridge in a directory in the toolchain image: proved, or the first error.
cd "$(dirname "$0")"
DIR=${1:-BGen}
export MODULES="Bridge.lean"
./lean.sh >/dev/null 2>&1
for f in "$DIR"/B*.lean; do
  s=$(date +%s)
  out=$(timeout "${BRIDGE_TIMEOUT:-90}" ./lean.sh "$f" 2>&1)
  t=$(( $(date +%s) - s ))
  if echo "$out" | grep -q "error"; then
    echo "FAIL $f ${t}s $(echo "$out" | grep -m1 error | cut -c1-120)"
  elif echo "$out" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]\|does not depend on any axioms\|depends on axioms: \[propext\]\|depends on axioms: \[propext, Quot.sound\]\|depends on axioms: \[Classical.choice"; then
    echo "OK $f ${t}s"
  else
    echo "FAIL $f ${t}s timeout or sorry"
  fi
done
