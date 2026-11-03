"""Models of standard-library functions that Aeneas leaves as axioms.

When translated code calls a library function Aeneas has no definition for,
Aeneas declares it as an `axiom` tagged with the function's exact Rust path,
for example

    @[rust_fun "core::num::{u64}::abs_diff"]
    axiom core.num.U64.abs_diff : Std.U64 → Std.U64 → Result Std.U64

ProofCI replaces such a declaration with a definition of the function's Rust
behaviour, keeping Aeneas' exact name and signature. The guarantees that call
it can then be proved instead of being reported as unsupported.

These definitions are trusted, like the Aeneas library itself: they ship with
ProofCI and never come from the repository being checked. Each is matched by
the full Rust path, so a model only ever replaces the declaration it was
written for. `tests/test_models.py` checks every model against values computed
by Rust. Anything not listed here stays an axiom, and guarantees that depend
on it remain unsupported.
"""

import re
from dataclasses import dataclass

UNSIGNED = {"u8": "U8", "u16": "U16", "u32": "U32", "u64": "U64", "u128": "U128", "usize": "Usize"}
SIGNED = {"i8": "I8", "i16": "I16", "i32": "I32", "i64": "I64", "i128": "I128", "isize": "Isize"}
INT = "|".join([*UNSIGNED, *SIGNED])


@dataclass(frozen=True)
class Model:
    pattern: str        # regex for the full rust_fun path
    body: object        # callable(match, declaration) -> Lean term
    description: str
    spec: object = None  # callable(match, name) -> a proved @[step] theorem, or None


def _binder(declaration, cls):
    match = re.search(r"\((\w+)\s*:\s*" + re.escape(cls), declaration)
    if not match:
        raise ValueError(f"no {cls} instance in {declaration!r}")
    return match.group(1)


def _try_from(m, _):
    dst, src = m.group(1), m.group(2)
    err = "ok (.Err ())"
    if dst in UNSIGNED and src in UNSIGNED:
        return f"fun x => core.num.tryFromUScalar .{UNSIGNED[dst]} x"
    if dst in SIGNED and src in UNSIGNED:
        return (f"fun x => if (x.val : Int) ≤ IScalar.max .{SIGNED[dst]} "
                f"then ok (.Ok ⟨BitVec.ofNat _ x.val⟩) else {err}")
    if dst in UNSIGNED and src in SIGNED:
        return (f"fun x => if 0 ≤ x.val ∧ x.val.toNat ≤ UScalar.max .{UNSIGNED[dst]} "
                f"then ok (.Ok ⟨BitVec.ofNat _ x.val.toNat⟩) else {err}")
    return (f"fun x => if IScalar.min .{SIGNED[dst]} ≤ x.val ∧ x.val ≤ IScalar.max .{SIGNED[dst]} "
            f"then ok (.Ok ⟨BitVec.ofInt _ x.val⟩) else {err}")


def _from(m, _):
    dst, src = m.group(1), m.group(2)
    # Rust only implements `From` for conversions that never lose information.
    if dst in UNSIGNED and src in UNSIGNED:
        return "fun x => ok ⟨BitVec.ofNat _ x.val⟩"
    if dst in SIGNED and src in UNSIGNED:
        return "fun x => ok ⟨BitVec.ofNat _ x.val⟩"
    if dst in SIGNED and src in SIGNED:
        return "fun x => ok ⟨BitVec.ofInt _ x.val⟩"
    raise ValueError(f"no lossless From<{dst}, {src}>")


def _abs_diff_spec(m, name):
    ty = "Std." + UNSIGNED[m.group(1)]
    return (f"@[step] theorem {name}.spec (a b : {ty}) :\n"
            f"    {name} a b ⦃ r => r.val = if b.val ≤ a.val then a.val - b.val else b.val - a.val ⦄ := by\n"
            f"  unfold {name}\n"
            f"  split <;> step*")


def _try_from_spec(m, name):
    dst, src = m.group(1), m.group(2)
    if not (dst in UNSIGNED and src in UNSIGNED):
        return None
    d, s = UNSIGNED[dst], UNSIGNED[src]
    return (f"@[step] theorem {name}.spec (x : Std.{s}) :\n"
            f"    {name} x ⦃ r => (x.val ≤ {d}.max → ∃ y : Std.{d}, r = .Ok y ∧ y.val = x.val) ∧\n"
            f"      ({d}.max < x.val → r = .Err ()) ⦄ := by\n"
            f"  unfold {name} core.num.tryFromUScalar\n"
            f"  split <;> rename_i hb <;> simp only [WP.spec_ok]\n"
            f"  · refine ⟨fun _ => ⟨_, rfl, ?_⟩, fun habsurd => by scalar_tac⟩\n"
            f"    have hcast := (UScalar.cast_inBounds_spec (src_ty := .{s}) (tgt_ty := .{d}) x (by scalar_tac))\n"
            f"    simp only [lift, WP.spec_ok] at hcast\n"
            f"    exact hcast\n"
            f"  · exact ⟨fun habsurd => by scalar_tac, fun _ => by simp⟩")


MODELS = (
    Model(r"core::num::\{(u8|u16|u32|u64|u128|usize)\}::abs_diff",
          lambda m, d: "fun a b => if b.val ≤ a.val then a - b else b - a",
          "|a - b| for unsigned integers; never overflows", _abs_diff_spec),
    Model(r"core::num::\{(i8|i16|i32|i64|i128|isize)\}::is_negative",
          lambda m, d: "fun x => ok (decide (x.val < 0))", "x < 0"),
    Model(r"core::num::\{(i8|i16|i32|i64|i128|isize)\}::is_positive",
          lambda m, d: "fun x => ok (decide (0 < x.val))", "x > 0"),
    Model(r"core::num::\{(i8|i16|i32|i64|i128|isize)\}::unsigned_abs",
          lambda m, d: "fun x => ok ⟨BitVec.ofNat _ x.val.natAbs⟩",
          "|x| as the unsigned type of the same width; never overflows"),
    Model(rf"core::convert::num::\{{core::convert::TryFrom<({INT}), ({INT}), core::num::error::TryFromIntError>\}}::try_from",
          _try_from, "integer conversion that fails when the value does not fit", _try_from_spec),
    Model(rf"core::convert::num::\{{core::convert::From<({INT}), ({INT})>\}}::from",
          _from, "lossless integer conversion"),
    Model(r"core::convert::\{core::convert::TryFrom<@T, @U, !>\}::try_from",
          lambda m, d: f"fun u => do let t ← {_binder(d, 'core.convert.Into')}.into u; ok (.Ok t)",
          "the blanket TryFrom for types with a From conversion: always Ok"),
    Model(r"core::option::\{core::option::Option<@T>\}::and_then",
          lambda m, d: (f"fun o f => match o with | none => ok none "
                        f"| some x => {_binder(d, 'core.ops.function.FnOnce')}.call_once f x"),
          "Option::and_then"),
    Model(r"core::option::\{core::ops::try_trait::Try<core::option::Option<@T>>\}::branch",
          lambda m, d: "fun o => match o with | none => ok (.Break none) | some x => ok (.Continue x)",
          "the `?` operator on Option"),
    Model(r"core::option::\{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>\}::from_residual",
          lambda m, d: "fun _ => ok none", "the `?` operator on Option returning None"),
)

DECLARATION = re.compile(
    r'(?P<attr>@\[rust_fun\s+"(?P<path>[^"]+)"\]\s*\n)axiom(?P<decl>\s.*?)(?=\n\s*\n|\n@\[|\Z)', re.S)


def apply(lean_source: str):
    """Replace modelled axioms with definitions. Returns (source, [(rust path, Lean name)])."""
    applied = []

    def replace(match):
        path, decl = match.group("path"), match.group("decl")
        for model in MODELS:
            found = re.fullmatch(model.pattern, path)
            if found:
                try:
                    body = model.body(found, decl)
                except ValueError:
                    return match.group(0)
                name = decl.split()[0]
                applied.append((path, name))
                definition = f"{match.group('attr')}def{decl.rstrip()} :=\n  {body}"
                spec = model.spec(found, name) if model.spec else None
                return definition + (f"\n\n{spec}" if spec else "")
        return match.group(0)

    return DECLARATION.sub(replace, lean_source), applied
