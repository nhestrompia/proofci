"""Tests for the trusted standard-library models (proofci/models.py).

The differential test compiles a small crate that calls every modelled
function, runs it with Rust on boundary values, translates the same crate
with ProofCI (so the models are applied exactly as in a real check) and
evaluates the Lean translation on the same inputs. Every result must agree.
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import models  # noqa: E402

U64MAX, U128MAX = 2**64 - 1, 2**128 - 1
I128MIN, I128MAX = -2**127, 2**127 - 1

# (function, Rust parameter types, return kind, input tuples)
CASES = [
    ("abs_diff_u64", ["u64", "u64"], "u", [(0, 0), (3, 5), (5, 3), (0, U64MAX), (U64MAX, 0), (U64MAX, U64MAX)]),
    ("abs_diff_u8", ["u8", "u8"], "u", [(0, 255), (200, 7), (7, 7)]),
    ("unsigned_abs_i128", ["i128"], "u", [(0,), (-1,), (5,), (I128MIN,), (I128MAX,), (I128MIN + 1,)]),
    ("unsigned_abs_i8", ["i8"], "u", [(-128,), (127,), (-3,)]),
    ("is_negative_i128", ["i128"], "b", [(0,), (-1,), (1,), (I128MIN,), (I128MAX,)]),
    ("is_positive_i32", ["i32"], "b", [(0,), (-1,), (1,)]),
    ("u128_to_u64", ["u128"], "o", [(0,), (U64MAX,), (U64MAX + 1,), (U128MAX,)]),
    ("u128_to_i128", ["u128"], "o", [(0,), (I128MAX,), (I128MAX + 1,), (U128MAX,)]),
    ("i64_to_u8", ["i64"], "o", [(0,), (255,), (256,), (-1,), (-2**63,)]),
    ("i128_to_i64", ["i128"], "o", [(0,), (2**63 - 1,), (2**63,), (-2**63,), (-2**63 - 1,), (I128MIN,)]),
    ("u64_to_i128", ["u64"], "i", [(0,), (U64MAX,)]),
    ("u8_to_u64", ["u8"], "u", [(0,), (255,)]),
    ("i8_to_i64", ["i8"], "i", [(-128,), (127,)]),
    ("u64_try_into_i128", ["u64"], "i", [(0,), (U64MAX,)]),
    ("and_then_incr", ["u64", "bool"], "o", [(1, True), (U64MAX, True), (5, False)]),
    ("question_mark", ["u64", "bool"], "o", [(1, True), (9, False)]),
]

RUST_LIB = """
pub fn abs_diff_u64(a: u64, b: u64) -> u64 { a.abs_diff(b) }
pub fn abs_diff_u8(a: u8, b: u8) -> u8 { a.abs_diff(b) }
pub fn unsigned_abs_i128(x: i128) -> u128 { x.unsigned_abs() }
pub fn unsigned_abs_i8(x: i8) -> u8 { x.unsigned_abs() }
pub fn is_negative_i128(x: i128) -> bool { x.is_negative() }
pub fn is_positive_i32(x: i32) -> bool { x.is_positive() }
pub fn u128_to_u64(x: u128) -> Option<u64> { match u64::try_from(x) { Ok(v) => Some(v), Err(_) => None } }
pub fn u128_to_i128(x: u128) -> Option<i128> { match i128::try_from(x) { Ok(v) => Some(v), Err(_) => None } }
pub fn i64_to_u8(x: i64) -> Option<u8> { match u8::try_from(x) { Ok(v) => Some(v), Err(_) => None } }
pub fn i128_to_i64(x: i128) -> Option<i64> { match i64::try_from(x) { Ok(v) => Some(v), Err(_) => None } }
pub fn u64_to_i128(x: u64) -> i128 { i128::from(x) }
pub fn u8_to_u64(x: u8) -> u64 { u64::from(x) }
pub fn i8_to_i64(x: i8) -> i64 { i64::from(x) }
pub fn u64_try_into_i128(x: u64) -> i128 {
    let r: Result<i128, core::convert::Infallible> = <i128 as TryFrom<i128>>::try_from(i128::from(x));
    match r { Ok(v) => v, Err(_) => 0 }
}
pub fn and_then_incr(x: u64, present: bool) -> Option<u64> {
    let o = if present { Some(x) } else { None };
    o.and_then(|v| v.checked_add(1))
}
pub fn question_mark(x: u64, present: bool) -> Option<u64> {
    let o = if present { Some(x) } else { None };
    let v = o?;
    Some(v / 2)
}
"""


def _rust_literal(value, ty):
    return f"{value}{ty}" if value >= 0 else f"({value}{ty})"


def _lean_literal(value, ty):
    suffix = "#" + ty
    if value < 0:
        return f"(({value}){suffix})"   # Aeneas writes negative literals as (-3)#i32
    return f"({value}{suffix})"


class ApplyTests(unittest.TestCase):
    def test_replaces_only_known_paths(self):
        source = (
            '@[rust_fun "core::num::{u64}::abs_diff"]\n'
            "axiom core.num.U64.abs_diff : Std.U64 → Std.U64 → Result Std.U64\n\n"
            '@[rust_fun "core::num::{u64}::leading_zeros"]\n'
            "axiom core.num.U64.leading_zeros : Std.U64 → Result Std.U32\n\n"
            "axiom unrelated : False\n")
        out, applied = models.apply(source)
        self.assertEqual(applied, ["core::num::{u64}::abs_diff"])
        self.assertIn("def core.num.U64.abs_diff : Std.U64 → Std.U64 → Result Std.U64 :=", out)
        self.assertIn("axiom core.num.U64.leading_zeros", out)
        self.assertIn("axiom unrelated : False", out)

    def test_paths_must_match_exactly(self):
        source = ('@[rust_fun "core::num::{u64}::abs_diff_extra"]\n'
                  "axiom f : Std.U64 → Result Std.U64\n")
        self.assertEqual(models.apply(source)[1], [])


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class DifferentialTests(unittest.TestCase):
    def test_models_agree_with_rust(self):
        from proofci import extract, lean
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            crate = tmp / "repo"
            (crate / "src").mkdir(parents=True)
            (crate / "Cargo.toml").write_text('[package]\nname = "models"\nversion = "0.1.0"\nedition = "2021"\n')
            (crate / "src" / "lib.rs").write_text(RUST_LIB)

            # Rust: evaluate every case.
            main = ["mod lib { " + RUST_LIB + " }", "use lib::*;", "fn main() {"]
            for name, types, kind, inputs in CASES:
                for args in inputs:
                    call = f"{name}({', '.join(_rust_literal(a, t) if t != 'bool' else str(a).lower() for a, t in zip(args, types))})"
                    fmt = {"u": "{}", "i": "{}", "b": "{}", "o": "{:?}"}[kind]
                    main.append(f'    println!("{name} {args!r} = {fmt}", {call});')
            main.append("}")
            (tmp / "main.rs").write_text("\n".join(main) + "\n")
            subprocess.run(["rustc", "--edition", "2021", "-O", "-o", tmp / "main", tmp / "main.rs"],
                           check=True, capture_output=True)
            rust = subprocess.run([tmp / "main"], check=True, capture_output=True, text=True).stdout

            # Lean: translate with ProofCI (models applied) and evaluate.
            work = tmp / "work"
            work.mkdir()
            names = [f"models::{name}" for name, *_ in CASES]
            ex = extract.extract(crate, ".", work, start_from=names)
            contract = tmp / "contract"
            contract.mkdir()
            (contract / "Contract.lean").write_text(f"import {ex.module}\n")
            ws = lean.assemble(work / "lean", ex.lean_file, ex.module, contract, contract)
            lean.build_contract(ws)
            lines = [f"import {ex.module}", "open Aeneas Aeneas.Std Result models", "",
                     "def showU {t} (r : Result (UScalar t)) : String := match r.match with | .ok v => s!\"{v.val}\" | _ => \"panic\"",
                     "def showI {t} (r : Result (IScalar t)) : String := match r.match with | .ok v => s!\"{v.val}\" | _ => \"panic\"",
                     "def showB (r : Result Bool) : String := match r.match with | .ok v => s!\"{v}\" | _ => \"panic\"",
                     "def showOU {t} (r : Result (Option (UScalar t))) : String := match r.match with",
                     "  | .ok (some v) => s!\"Some({v.val})\" | .ok none => \"None\" | _ => \"panic\"",
                     "def showOI {t} (r : Result (Option (IScalar t))) : String := match r.match with",
                     "  | .ok (some v) => s!\"Some({v.val})\" | .ok none => \"None\" | _ => \"panic\"", ""]
            for name, types, kind, inputs in CASES:
                ret = re.search(r"-> (Option<)?(\w+)", RUST_LIB.split(f"fn {name}(")[1]).group(2)
                show = {"u": "showU", "i": "showI", "b": "showB"}.get(kind) or (
                    "showOI" if ret.startswith("i") else "showOU")
                for args in inputs:
                    lean_args = " ".join(_lean_literal(a, t) if t != "bool" else str(a).lower()
                                         for a, t in zip(args, types))
                    lines.append(f'#eval IO.println ("{name} {args!r} = " ++ {show} ({name} {lean_args}))')
            (ws.root / "Eval.lean").write_text("\n".join(lines) + "\n")
            result = lean._lake(ws, ["env", "lean", "Eval.lean"])
            errors = [l for l in result.output.splitlines() if "error" in l and "sorry" not in l]
            self.assertEqual(result.status, 0, "\n".join(errors[:20]) or result.output[-3000:])
            got = [l for l in result.output.splitlines() if " = " in l and l.split(" ")[0] in {c[0] for c in CASES}]
            self.assertEqual(got, rust.splitlines())
            self.assertGreaterEqual(len(ex.modelled), 8, ex.modelled)


if __name__ == "__main__":
    unittest.main()
