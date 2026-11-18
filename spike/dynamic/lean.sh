#!/bin/sh
# Checks the dynamic spike in the toolchain image. Builds Dyn and the modules in MODULES
# (paths like Gen/Union.lean), then checks each argument. OUT holds the compiled modules.
set -e
OUT=${OUT:-/tmp/dyn-olean}
LP=$(cd /opt/proofci/spike/core && lake env printenv LEAN_PATH)
export LEAN_PATH="$LP:$OUT"
cd "$(dirname "$0")"
for f in Dyn.lean ${MODULES:-}; do
  o="$OUT/${f%.lean}.olean"
  mkdir -p "$(dirname "$o")"
  [ "$o" -nt "$f" ] && [ "$o" -nt Dyn.lean ] || lean -o "$o" "$f"
done
for f in "$@"; do lean "$f"; done
