#!/bin/bash
# One attempt per function, with the generator as committed. Nothing is tuned between runs.
cd "$(dirname "$0")"
SP=$1
for f in ${FNS:-isCellMatch maybeIncrementLevel getNextRunningBalance deriveAuctionOutcome calculateTrend clamp rangePosition daysToWeeks trimIntervalDataToRange getV3HopCount}; do
  t="src/heldout.ts::$f"
  if ! node --input-type=module -e "
    import { writeFileSync } from 'node:fs';
    import { lower } from './lower.mjs';
    const r = lower(process.cwd() + '/work', ['$t']);
    writeFileSync('Spike/Gen.lean', r.lean);" 2> work/e.out; then
    echo "$f | lowering | $(grep -m1 Error work/e.out | cut -c1-90)"; continue; fi
  if ! node view.mjs "$t" 2> work/e.out; then echo "$f | view | $(tail -1 work/e.out | cut -c1-90)"; continue; fi
  if grep -q "$t" work/e.out; then echo "$f | translator | $(grep "$t" work/e.out | cut -c1-110)"; continue; fi
  if ! node bridge.mjs "$t" 2> work/e.out; then echo "$f | generator | $(grep -m1 Error work/e.out | cut -c1-90)"; continue; fi
  $SP 'timeout 100 lake build Spike.Bridges > work/raw.out 2>&1; echo $? > work/code' 
  if [ "$(cat work/code)" = 0 ]; then echo "$f | PROVED |"; else echo "$f | proof | $(grep -m1 '^error' work/raw.out | cut -c1-100)"; fi
done
