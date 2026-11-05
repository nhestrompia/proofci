#!/bin/bash
cd "$(dirname "$0")"; SP=$1
for f in ${FNS:-chain5 chain20 chain80 line10 line40 line160 joins2 joins4 joins6 joins8 joins10}; do
  t=src/scale.ts::$f
  node --input-type=module -e "
    import { writeFileSync } from 'node:fs'; import { lower } from './lower.mjs';
    writeFileSync('Spike/Gen.lean', lower(process.cwd()+'/work',['$t']).lean);" || { echo "$f lowering failed"; continue; }
  node view.mjs $t 2>/dev/null; node bridge.mjs $t 2>/dev/null
  sed -i '' '1a\
set_option maxHeartbeats 0\
set_option maxRecDepth 200000
' Spike/Bridges.lean
  $SP "S=\$(date +%s); timeout 170 lake build Spike.Bridges > work/raw.out 2>&1; c=\$?; echo $f exit \$c \$(( \$(date +%s)-S ))s \$(grep -m1 -E '^error' work/raw.out | cut -c1-110)"
done
