#!/bin/bash
cd "$(dirname "$0")"; SP=$1
for f in $FNS; do
  t=src/scale.ts::$f
  node --input-type=module -e "
    import { writeFileSync } from 'node:fs'; import { lower } from './lower.mjs';
    writeFileSync('Spike/Gen.lean', lower(process.cwd()+'/work',['$t']).lean);" || continue
  node view.mjs $t 2>/dev/null; node bridge2.mjs $t || continue
  $SP "S=\$(date +%s); timeout 170 lake build Spike.Bridges2 > work/raw.out 2>&1; c=\$?; echo $f exit \$c \$(( \$(date +%s)-S ))s \$(wc -l < Spike/Bridges2.lean) lines \$(grep -m1 -E '^error' work/raw.out | cut -c1-110)"
done
