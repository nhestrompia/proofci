#!/bin/bash
# usage: asynccore.sh <out dir> [cases] [file::name ...]   Core's reading of the async fixtures against Node.
set -e
cd "$(dirname "$0")"
OUT=${1:-/tmp/asynccore}; shift || true
CASES=${1:-30}; shift || true
rm -rf "$OUT"; mkdir -p "$OUT"
node asynccore.mjs fixtures/async "$OUT" "$CASES" "$@"
docker run --rm --network none --tmpfs /tmp:exec,mode=1777 -v "$PWD:/s" -v proofci-spike-lake-dev:/s/.lake -v "$OUT:/o" -w /s --entrypoint bash \
  ${LEAN_IMAGE:-proofci-toolchain:ts} -c 'LEAN_PATH=$(lake env printenv LEAN_PATH) lean /o/Core.lean > /o/Core.out 2>&1; echo $? > /o/Core.code'
python3 - "$OUT" <<'PY'
import json, sys
d = sys.argv[1]
expected = json.load(open(f"{d}/expected.json"))
got = [l for l in open(f"{d}/Core.out").read().splitlines() if l.startswith("ASYNC")]
errors = [l for l in open(f"{d}/Core.out").read().splitlines() if "error" in l]
bad = [(i, e, g) for i, (e, g) in enumerate(zip(expected, got)) if e != g]
print(f"lean exit {open(d + '/Core.code').read().strip()}: {len(got)} of {len(expected)} cases ran, {len(expected) - len(bad) - (len(expected) - len(got))} agree, {len(bad)} differ")
for i, e, g in bad[:3]:
    print("  node:", e[:300]); print("  core:", g[:300])
for l in errors[:3]: print(l[:300])
sys.exit(1 if bad or len(got) != len(expected) else 0)
PY
