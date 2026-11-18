#!/bin/sh
# Checks the spike in the toolchain image: builds Gen/, checks the proofs, plants mutants,
# and replays the cases written by `node diff.mjs gen` if Diff.lean exists.
set -e
cd "$(dirname "$0")"
export MODULES="Gen/Unknown.lean Gen/Union.lean Gen/Alias.lean Gen/Closure.lean Gen/Budget.lean Gen/Slideshow.lean Gen/Fixtures.lean Gen/Bank.lean"
./lean.sh Proofs.lean
node mutate.mjs | tail -1
[ -f Diff.lean ] && ./lean.sh Diff.lean > "${DIFF_OUT:-/tmp/dyn-diff.txt}" || true
