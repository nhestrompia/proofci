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
"""
NAMES = [line.split()[2] for line in OPERATIONS.strip().splitlines()]


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
            differ, notes = typescript.differential(package.parent, "package", work, ws, extraction, cases=2000)
            self.assertEqual(differ[:5], [])
            print(notes)
            self.assertIn("compared with Node", notes[-1])
