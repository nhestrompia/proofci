#!/bin/bash
# usage: mutate_core_async.sh <asynccore out dir> <mutant dir>   Runs every mutant and prints the survivors.
set -e
cd "$(dirname "$0")"
python3 mutate_core_async.py "$1" "$2"
docker run --rm --network none --tmpfs /tmp:exec,mode=1777 -v "$PWD:/s" -v proofci-spike-lake-dev:/s/.lake -v "$2:/m" -w /s --entrypoint bash \
  ${LEAN_IMAGE:-proofci-toolchain:ts} -c '
export LP=$(lake env printenv LEAN_PATH)
one() { f=$1; n=$(basename $f .lean); LEAN_PATH=$LP timeout 300 lean $f > /m/$n.out 2>&1; echo $? > /m/$n.code; }
export -f one
ls /m/M*.lean | xargs -P ${JOBS:-3} -I{} bash -c "one {}"'
python3 - "$1" "$2" <<'PY'
import json, sys
src, d = sys.argv[1], sys.argv[2]
expected = json.load(open(f"{src}/expected.json"))
rows = json.load(open(f"{d}/index.json"))
survived, timeouts = [], []
for r in rows:
    out = open(f"{d}/M{r['i']}.out").read()
    code = open(f"{d}/M{r['i']}.code").read().strip()
    got = [l for l in out.splitlines() if l.startswith("ASYNC")]
    if code == "124":
        timeouts.append(r)
        continue
    if code != "0" or "error" in out or got != expected:
        continue
    survived.append(r)
print(f"{len(rows) - len(survived) - len(timeouts)} of {len(rows)} mutants rejected, {len(survived)} survived, {len(timeouts)} timed out")
for r in timeouts:
    print("timed out:", r["kind"], "line", r["line"])
for r in survived:
    print("survived:", r["kind"], "line", r["line"])
PY
