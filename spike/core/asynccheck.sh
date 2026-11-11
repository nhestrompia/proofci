#!/bin/bash
# usage: asynccheck.sh <out dir> [cases] [file::name ...]    (fixtures/async, in the spike's Lean volume)
set -e
cd "$(dirname "$0")"
OUT=${1:-/tmp/asynccheck}; shift || true
CASES=${1:-40}; shift || true
rm -rf "$OUT"; mkdir -p "$OUT"
node asynccheck.mjs fixtures/async "$OUT" "$CASES" "$@"
docker run --rm --network none --tmpfs /tmp:exec,mode=1777 -v "$PWD:/s" -v proofci-spike-lake-dev:/s/.lake -v "$OUT:/o" -w /s --entrypoint bash \
  ${LEAN_IMAGE:-proofci-toolchain:ts} -c 'LEAN_PATH=$(lake env printenv LEAN_PATH) lean /o/Check.lean > /o/Check.out 2>&1; echo $? > /o/Check.code'
agree=$(grep -c "PROOFCI_DIFF agree" "$OUT/Check.out" || true)
differ=$(grep -c "PROOFCI_DIFF differ" "$OUT/Check.out" || true)
failed=$(grep -c "PROOFCI_DIFF failed" "$OUT/Check.out" || true)
echo "lean exit $(cat "$OUT/Check.code"): $agree agree, $differ differ, $failed left the model"
grep -m3 "error" "$OUT/Check.out" || true
