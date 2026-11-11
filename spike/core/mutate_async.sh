#!/bin/bash
# usage: mutate_async.sh <asynccheck out dir> <mutant dir>   Runs every mutant and prints the survivors.
set -e
cd "$(dirname "$0")"
python3 mutate_async.py "$1" "$2"
docker run --rm --network none --tmpfs /tmp:exec,mode=1777 -v "$PWD:/s" -v proofci-spike-lake-dev:/s/.lake -v "$2:/m" -w /s --entrypoint bash \
  ${LEAN_IMAGE:-proofci-toolchain:ts} -c '
export LP=$(lake env printenv LEAN_PATH)
one() { f=$1; n=$(basename $f .lean); LEAN_PATH=$LP timeout 300 lean $f > /m/$n.out 2>&1; echo $? > /m/$n.code; }
export -f one
ls /m/M*.lean | xargs -P ${JOBS:-4} -I{} bash -c "one {}"'
python3 - "$2" <<'PY'
import json, sys, collections
d = sys.argv[1]
rows = json.load(open(f"{d}/index.json"))
survived, killed = [], collections.Counter()
for r in rows:
    out = open(f"{d}/M{r['i']}.out").read()
    code = open(f"{d}/M{r['i']}.code").read().strip()
    if "PROOFCI_DIFF differ" in out or "error" in out or code not in ("0",):
        killed[r["kind"]] += 1
    else:
        survived.append(r)
print(f"{len(rows) - len(survived)} of {len(rows)} mutants rejected")
for r in survived:
    print("survived:", r["kind"], "line", r["line"])
PY
