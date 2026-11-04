"""Compares ProofCI's model of JavaScript numbers with Node.

The model promises that when it returns a value, JavaScript computes the same
value, including for `Math.floor(a / b)` near the limits of safe integers.
Run inside the toolchain image:

    PROOFCI_TOOLCHAIN=1 python3 -m unittest tests.test_js_numbers -v
"""

import json
import os
import tempfile
import unittest
from pathlib import Path

from proofci import lean, typescript

OPERATIONS = """
export const add = (a: number, b: number) => a + b;
export const sub = (a: number, b: number) => a - b;
export const mul = (a: number, b: number) => a * b;
export const div = (a: number, b: number) => a / b;
export const rem = (a: number, b: number) => a % b;
export const neg = (a: number) => -a;
export const floor = (a: number, b: number) => Math.floor(a / b);
export const ceil = (a: number, b: number) => Math.ceil(a / b);
export const trunc = (a: number, b: number) => Math.trunc(a / b);
export const abs = (a: number) => Math.abs(a);
export const min = (a: number, b: number) => Math.min(a, b);
export const max = (a: number, b: number) => Math.max(a, b);
export const lt = (a: number, b: number) => a < b;
export const le = (a: number, b: number) => a <= b;
export const eq = (a: number, b: number) => a === b;
export const ne = (a: number, b: number) => a !== b;
export const both = (a: boolean, b: boolean) => a && !b;
export const either = (a: boolean, b: boolean) => a || b;
export const pick = (a: boolean, b: number) => a ? b : 0;
export const orNull = (a: number | null) => { if (a === null) return 0; return a; };
export const undefinedIsNotNull = (a: number | undefined) => { if (a === undefined) return 1; return a; };
export const bigMul = (a: bigint, b: bigint) => a * b - 1n;
export const bigDiv = (a: bigint, b: bigint) => a / b;
export const bigRem = (a: bigint, b: bigint) => a % b;
export const bigLess = (a: bigint, b: bigint) => a < b;
export function check(a: number): void { if (a < 0) throw new RangeError("negative"); }
export function caught(a: number) { try { check(a); return a; } catch { return 7; } }
export function joined(a: number, b: number) { let r = a; if (r > b) { r = b; } else { r = r + 1; } return r * 2; }
export function capped(n: number) { let s = 0; for (let i = 0; i < n && i < 50; i++) { if (i % 3 === 0) continue; if (s > 100) break; s += i; } return s; }
export function search(n: number) { let i = 0; while (i < 40) { if (i * i >= n) return i; i += 1; } return -1; }
export function fact(n: number): number { if (n <= 0 || n > 25) return 1; return n * fact(n - 1); }
export function sum(xs: number[]) { let s = 0; for (const x of xs) { s += x; } return s; }
export function evens(xs: number[]) { const out: number[] = []; for (const x of xs) { if (x % 2 === 0) { out.push(x); } } return out; }
export const chain = (xs: number[]) => xs.filter(x => x > 0).map(x => x * 2).reduce((a, b) => a + b, 0);
export const anyBig = (xs: number[]) => xs.some(x => x > 100);
export const allBig = (xs: number[]) => xs.every(x => x > 100);
export const found = (xs: number[]) => xs.find(x => x > 1);
export const at = (xs: number[], i: number) => xs[i];
export const size = (xs: number[]) => xs.length;
export const cut = (xs: number[], a: number, b: number) => xs.slice(a, b);
export const cutFrom = (xs: number[], a: number) => xs.slice(a);
export const has = (xs: number[], a: number) => xs.includes(a);
export const where = (xs: number[], a: number) => xs.indexOf(a);
export const joinAll = (xs: number[], ys: number[]) => [...xs, 1, ...ys].concat(xs);
export function changes(xs: number[], i: number, v: number) { const a = xs.slice(); a[i % 9] = v; a.push(v); a.unshift(1); a.pop(); a.shift(); a.reverse(); return a; }
"""
NAMES = [line.split()[2].split("(")[0] for line in OPERATIONS.strip().splitlines()]


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class Numbers(unittest.TestCase):
    def test_model_agrees_with_node(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            package = work / "package"
            (package / "src").mkdir(parents=True)
            (package / "package.json").write_text(json.dumps({"name": "numbers"}))
            (package / "src/ops.ts").write_text(OPERATIONS)
            (work / "lean-src").mkdir()
            module = "Numbers"
            (work / "lean-src/Contract.lean").write_text(f"import {module}\n")
            functions = [f"src/ops.ts::{name}" for name in NAMES]
            extraction = typescript.extract(package.parent, "package", work, functions)
            self.assertEqual(extraction.failures, {})
            ws = lean.assemble(work / "lean", extraction.lean_file, extraction.module,
                               work / "lean-src", work / "lean-src")
            self.assertIsNone(lean.build_translation(ws))
            differ, notes = typescript.differential(package.parent, "package", work, ws, extraction, cases=500)
            self.assertEqual(differ[:5], [])
            print(notes)
            self.assertIn("compared with Node", notes[-1])
