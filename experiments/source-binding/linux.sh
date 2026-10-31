#!/bin/sh
# Reproduce the pinned Linux spike. Candidate and contract files are inputs, not configuration.
set -eu

temp_dir=
reported=0
report_expected=1
case ${1:-} in --corpus|--admission|--adversarial) report_expected=0 ;; esac
cleanup() {
  status=$?
  trap - EXIT HUP INT TERM
  if [ -n "$temp_dir" ]; then rm -rf "$temp_dir" || true; fi
  if [ "$status" -ne 0 ] && [ "$report_expected" -eq 1 ] && [ "$reported" -eq 0 ]; then
    printf '%s\n' '{"decision":"unproven","reason":"runner setup or container failed"}'
  fi
  exit "$status"
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
temp_dir=$(mktemp -d "${TMPDIR:-/tmp}/proofci-spike.XXXXXXXX")

lean_archive=${PROOFCI_LEAN_ARCHIVE:-$temp_dir/lean.tar.zst}
bwrap_package=${PROOFCI_BWRAP_PACKAGE:-$temp_dir/bubblewrap.deb}
if [ ! -f "$lean_archive" ]; then
  curl -fsSL 'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst' -o "$lean_archive"
fi
if [ ! -f "$bwrap_package" ]; then
  curl -fsSL 'https://deb.debian.org/debian/pool/main/b/bubblewrap/bubblewrap_0.12.0-1~deb13u1_arm64.deb' -o "$bwrap_package"
fi
bwrap_package=$(CDPATH= cd -- "$(dirname -- "$bwrap_package")" && pwd)/$(basename -- "$bwrap_package")
python3 - "$lean_archive" c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028 "$bwrap_package" d1ac1d0d81c815fc15842b9f04fdf414830ed14a0a602bf6344740f90bb36c00 <<'PY'
import hashlib
from pathlib import Path
import sys
for filename, expected in zip(sys.argv[1::2], sys.argv[2::2]):
    h = hashlib.sha256()
    with Path(filename).open("rb") as source:
        while chunk := source.read(1024 * 1024):
            h.update(chunk)
    if h.hexdigest() != expected:
        raise SystemExit(f"SHA-256 mismatch: {filename}")
PY
tar --zstd -xf "$lean_archive" -C "$temp_dir"
mkdir "$temp_dir/bwrap"
(cd "$temp_dir/bwrap" && ar x "$bwrap_package" && tar -xJf data.tar.xz)
mkdir "$temp_dir/input"
chmod 755 "$temp_dir/input"

case ${1:-} in
  --corpus|--admission|--adversarial)
    [ "$#" -eq 1 ] || { echo 'expected one experiment selector' >&2; exit 2; }
    program=${1#--}.py
    shift
    ;;
  *)
    [ "$#" -eq 2 ] || { echo 'usage: linux.sh CANDIDATE CONTRACT | --corpus | --admission | --adversarial' >&2; exit 2; }
    python3 - "$1" "$2" "$temp_dir/input" <<'PY'
from pathlib import Path
import sys
for source, name in zip(sys.argv[1:3], ("candidate.lean", "contract.json")):
    with Path(source).open("rb") as f:
        data = f.read(16385)
    if len(data) > 16384:
        raise SystemExit(f"input exceeds 16384 bytes: {source}")
    (Path(sys.argv[3]) / name).write_bytes(data)
PY
    chmod a+r "$temp_dir/input/candidate.lean" "$temp_dir/input/contract.json"
    program=verdict.py
    set -- /input/candidate.lean /input/contract.json
    ;;
esac

run_container() {
  docker run --rm --network none --platform linux/arm64 --cap-drop ALL \
    --security-opt no-new-privileges --security-opt seccomp=unconfined \
    --security-opt systempaths=unconfined --user 65534:65534 --read-only \
    --tmpfs /tmp:rw,size=2g,mode=1777 --tmpfs /run:rw,mode=1777 -e HOME=/tmp \
    -v "$temp_dir/bwrap/usr/bin/bwrap:/usr/bin/bwrap:ro" \
    -v "$temp_dir/lean-4.35.0-linux_aarch64:/lean:ro" \
    -v "$script_dir:/probe:ro" -v "$temp_dir/input:/input:ro" \
    python@sha256:6a9220edda062e9223ea0784740a535987299420b96fbfd520b89bbd3e772485 \
    sh -c 'mkdir -p /run/user; program=$1; shift; exec python3 "/probe/$program" "$@" --lean /lean/bin/lean --lake /lean/bin/lake' \
    sh "$program" "$@"
}

if [ "$program" = verdict.py ]; then
  set +e
  run_container "$@" > "$temp_dir/result.json"
  status=$?
  set -e
  python3 - "$temp_dir/result.json" "$status" <<'PY'
import json
from pathlib import Path
import sys
report = json.loads(Path(sys.argv[1]).read_bytes())
status = int(sys.argv[2])
if status not in (0, 1) or report.get("decision") != ("verified" if status == 0 else "unproven"):
    raise SystemExit("validator output does not match its exit status")
print(json.dumps(report, indent=2))
PY
  reported=1
  exit "$status"
else
  run_container "$@"
fi
