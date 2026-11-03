"""Assemble the Lean workspace and judge the proofs.

Workspace layout (all assembled by ProofCI, never taken whole from the PR):

    lakefile.lean, lake-manifest.json   generated; dependencies are the pinned
                                        Aeneas library and Mathlib, by path
    <Crate>.lean                        regenerated from the PR's Rust
    Contract.lean, Contract/**          protected statements (policy commit)
    Proofs.lean, Proofs/**              proofs from the pull request
    comparator.json                     generated from the protected manifest

`lake comparator` builds the contract and the proofs inside its own sandbox,
exports both, and checks that every named theorem in the proofs has exactly
the contract's statement (including every constant it mentions, such as the
extracted Rust functions), uses only permitted axioms, and is accepted by
Lean's kernel and by nanoda.
"""

import json
import os
import re
import shutil
from dataclasses import dataclass, field
from pathlib import Path

from . import sandbox

PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")
AUDIT_MARKER = "PROOFCI_AUDIT "
MAX_LEAN_BYTES = 2 * 1024 * 1024
MAX_LEAN_FILES = 200


class ContractError(Exception):
    """The protected contract does not elaborate against the candidate."""


def aeneas_lean_dir():
    return Path(os.environ.get("PROOFCI_AENEAS_LEAN", "/opt/aeneas/backends/lean"))


def _lake_manifest(name):
    base = aeneas_lean_dir()
    upstream = json.loads((base / "lake-manifest.json").read_text())
    packages = [{
        "type": "path", "scope": "", "name": "aeneas", "manifestFile": "lake-manifest.json",
        "inherited": False, "dir": str(base), "configFile": "lakefile.lean",
    }]
    for entry in upstream["packages"]:
        directory = base / ".lake" / "packages" / entry["name"]
        config = "lakefile.lean" if (directory / "lakefile.lean").exists() else "lakefile.toml"
        packages.append({
            "type": "path", "scope": "", "name": entry["name"], "manifestFile": "lake-manifest.json",
            "inherited": True, "dir": str(directory), "configFile": config,
        })
    return {"version": upstream["version"], "packagesDir": ".lake/packages",
            "packages": packages, "name": name, "lakeDir": ".lake"}


def _copy_lean_tree(source_dir: Path, module: str, dest: Path, required=True):
    """Copy `<module>.lean` and `<module>/**/*.lean` (regular files only)."""
    root = source_dir / f"{module}.lean"
    if not root.is_file() or root.is_symlink():
        if required:
            raise FileNotFoundError(f"{root} is missing")
        return
    files = [root]
    tree = source_dir / module
    if tree.is_dir() and not tree.is_symlink():
        files += sorted(p for p in tree.rglob("*.lean"))
    total = 0
    for path in files:
        if path.is_symlink() or any(p.is_symlink() for p in path.relative_to(source_dir).parents
                                    if (source_dir / p) != source_dir and (source_dir / p).is_symlink()):
            raise ValueError(f"symbolic links are not allowed: {path}")
        data = path.read_bytes()
        total += len(data)
        if len(files) > MAX_LEAN_FILES or total > MAX_LEAN_BYTES:
            raise ValueError(f"{module} sources exceed the size limits")
        target = dest / path.relative_to(source_dir)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)


FROM_PAIRS = [  # lossless conversions Aeneas defines, with their `from_val_eq` lemmas
    ("U16", "U8"), ("U32", "U8"), ("U32", "U16"), ("U64", "U8"), ("U64", "U16"), ("U64", "U32"),
    ("U128", "U8"), ("U128", "U16"), ("U128", "U32"), ("U128", "U64"),
    ("Usize", "U8"), ("Usize", "U16"), ("Usize", "U32"),
    ("I16", "I8"), ("I32", "I8"), ("I32", "I16"), ("I64", "I8"), ("I64", "I16"), ("I64", "I32"),
    ("I128", "I8"), ("I128", "I16"), ("I128", "I32"), ("I128", "I64"),
    ("Isize", "I8"), ("Isize", "I16"), ("Isize", "I32"),
]
SCALARS = ["U8", "U16", "U32", "U64", "U128", "Usize", "I8", "I16", "I32", "I64", "I128", "Isize"]


def specs_module():
    """`ProofciSpecs`: step lemmas for common library calls that Aeneas
    defines but gives no `@[step]` spec. Proof modules may `import ProofciSpecs`.
    Every lemma is proved, so importing it adds nothing to what is trusted."""
    lines = ["import Aeneas", "open Aeneas Aeneas.Std Result", "", "namespace ProofciSpecs", ""]
    for dst, src in FROM_PAIRS:
        f = f"core.convert.num.From{dst}{src}.from"
        lines += [f"@[step] theorem from_{dst.lower()}_{src.lower()} (x : Std.{src}) :",
                  f"    lift ({f} x) ⦃ y => y.val = x.val ⦄ := by",
                  f"  simp [lift, WP.spec_ok, core.convert.num.From{dst}{src}.from_val_eq]", ""]
    for ty in SCALARS:
        lines += [f"@[step] theorem cmp_{ty.lower()} (a b : Std.{ty}) :",
                  f"    lift (core.cmp.impls.Ord{ty}.cmp a b) ⦃ o => o = compare a.val b.val ⦄ := by",
                  f"  simp [lift, WP.spec_ok, core.cmp.impls.Ord{ty}.cmp]", ""]
    lines += [
        "@[step] theorem ok_or_some {T E : Type _} (v : T) (e : E) :",
        "    core.option.Option.ok_or (some v) e ⦃ r => r = .Ok v ⦄ := by",
        "  simp [core.option.Option.ok_or, WP.spec_ok]", "",
        "@[step] theorem ok_or_none {T E : Type _} (e : E) :",
        "    core.option.Option.ok_or (none : Option T) e ⦃ r => r = .Err e ⦄ := by",
        "  simp [core.option.Option.ok_or, WP.spec_ok]", "",
        "@[step] theorem map_err_ok {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F) (v : T) (f : O) :",
        "    core.result.Result.map_err fnOnce (.Ok v) f ⦃ r => r = .Ok v ⦄ := by",
        "  simp [core.result.Result.map_err, WP.spec_ok]", "",
        "end ProofciSpecs", ""]
    return "\n".join(lines)


def _lib(module, root):
    if (root / module).is_dir():
        return f"lean_lib {module} where\n  globs := #[.andSubmodules `{module}]\n"
    return f"lean_lib {module}\n"


@dataclass
class Workspace:
    root: Path
    crate_module: str
    theorems: list = field(default_factory=list)


def assemble(root: Path, extracted_file: Path, crate_module: str, contract_dir: Path, proofs_dir: Path):
    root.mkdir(parents=True)
    shutil.copyfile(extracted_file, root / f"{crate_module}.lean")
    _copy_lean_tree(contract_dir, "Contract", root)
    _copy_lean_tree(proofs_dir, "Proofs", root, required=False)
    (root / "ProofciSpecs.lean").write_text(specs_module())
    (root / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n"
        "package proofci_check\n"
        f'require aeneas from "{aeneas_lean_dir()}"\n'
        f"lean_lib {crate_module}\n"
        "lean_lib ProofciSpecs\n"
        + _lib("Contract", root) + _lib("Proofs", root)
    )
    (root / "lake-manifest.json").write_text(json.dumps(_lake_manifest("proofci_check"), indent=1))
    (root / ".lake").mkdir()
    return Workspace(root, crate_module)


def clone(ws, dest: Path, proofs_from=None):
    """Copy a workspace, including its build directory.

    Proof code runs while proofs are built, and that build can write to
    `.lake`. Every step that runs proof code therefore gets its own copy of a
    workspace in which only trusted code (the extracted model and the
    contract) has ever been built. In particular, a compiled contract that a
    proof overwrote is never shown to the comparator. With `proofs_from`, the
    proof sources are taken from that workspace instead.
    """
    shutil.copytree(ws.root, dest, symlinks=True)
    if proofs_from is not None:
        for name in ("Proofs.lean", "Proofs"):
            target = dest / name
            if target.is_dir():
                shutil.rmtree(target)
            elif target.exists():
                target.unlink()
            source = proofs_from.root / name
            if source.is_dir():
                shutil.copytree(source, target, symlinks=True)
            elif source.is_file():
                shutil.copyfile(source, target)
    return Workspace(dest, ws.crate_module, list(ws.theorems))


def _lake(ws, args, timeout=900):
    return sandbox.run(["lake", *args], readable=[ws.root], writable=[ws.root / ".lake"],
                       cwd=ws.root, timeout=timeout)


def build_contract(ws):
    result = _lake(ws, ["build", "Contract"])
    if result.status != 0:
        raise ContractError(_errors(result.output))


AUDIT_LEAN = r"""
import Contract
open Lean Meta

/-- Constants reachable from `root` through definitions of the same module
    (the extracted crate), so the walk never descends into the libraries. -/
partial def proofciReach (env : Environment) (root : Name) : NameSet := Id.run do
  let modIdx := env.getModuleIdxFor? root
  let mut seen : NameSet := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if env.getModuleIdxFor? n != modIdx then continue
    match env.find? n with
    | some (.defnInfo d) => todo := d.value.getUsedConstants.toList ++ todo
    | some (.opaqueInfo d) => todo := d.value.getUsedConstants.toList ++ todo
    | _ => pure ()
  return seen

/-- Does the postcondition of a `WP.spec` triple ignore the result while
    still claiming something? (`f x ⦃ _ => True ⦄`, "never panics or
    overflows", is a meaningful guarantee and is not flagged.) -/
def proofciPostIgnoresResult (e : Expr) : Bool :=
  if e.isAppOf ``Aeneas.Std.WP.spec then
    match e.getAppArgs.back? with
    | some (.lam _ _ body _) => !body.hasLooseBVars && !body.isConstOf ``True
    | _ => false
  else false

def proofciAudit (thm fn : Name) (models : List Name) : MetaM Unit := do
  let env ← getEnv
  let fnFound := env.contains fn
  let mut kind := "missing"
  let mut conclusion := false
  let mut hypothesis := false
  let mut trivial := false
  let mut ignores := false
  match env.find? thm with
  | some (.thmInfo info) =>
    kind := "theorem"
    let r ← forallTelescope info.type fun xs body => do
      let mut hyp := false
      for x in xs do
        let ty ← inferType x
        if (← isProp ty) && ty.getUsedConstants.contains fn then hyp := true
      let refl := body.isAppOfArity ``Eq 3 && body.appFn!.appArg! == body.appArg!
      pure (body.getUsedConstants.contains fn, hyp, body.isConstOf ``True || refl,
            proofciPostIgnoresResult body)
    (conclusion, hypothesis, trivial, ignores) := r
  | some _ => kind := "other"
  | none => pure ()
  let axioms ← if fnFound then collectAxioms fn else pure #[]
  let reach := if fnFound then proofciReach env fn else {}
  let used := models.filter reach.contains
  IO.println ("PROOFCI_AUDIT " ++ (Json.mkObj [
    ("theorem", Json.str thm.toString), ("function", Json.str fn.toString),
    ("kind", Json.str kind), ("function_found", Json.bool fnFound),
    ("conclusion_mentions_function", Json.bool conclusion),
    ("hypothesis_mentions_function", Json.bool hypothesis),
    ("trivial_conclusion", Json.bool trivial), ("post_ignores_result", Json.bool ignores),
    ("models", Json.arr (used.map (fun n => Json.str n.toString)).toArray),
    ("function_axioms", Json.arr (axioms.map (fun a => Json.str a.toString)))]).compress)
"""


def audit(ws, checks, models=()):
    """For each (theorem, lean_function): existence, how the statement uses
    the function, the function's axioms, and which ProofCI models it uses.

    Runs only over trusted inputs: the protected contract and the extracted
    model. Proof modules are never loaded here.
    """
    model_list = "[" + ", ".join(f"`{name}" for name in models) + "]"
    lines = [AUDIT_LEAN.strip(), ""]
    for theorem, function in checks:
        lines.append(f"#eval proofciAudit `{theorem} `{function} {model_list}")
    (ws.root / "ProofciAudit.lean").write_text("\n".join(lines) + "\n")
    result = _lake(ws, ["env", "lean", "ProofciAudit.lean"])
    found = {}
    for line in result.output.splitlines():
        if line.startswith(AUDIT_MARKER):
            item = json.loads(line[len(AUDIT_MARKER):])
            found[item["theorem"]] = item
    if result.status != 0 or len(found) != len(checks):
        raise ContractError("contract audit failed:\n" + _errors(result.output))
    return found


DECL_START = re.compile(
    r"^(?:@\[|/--|(?:private |protected |noncomputable |partial |unsafe )*"
    r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)\b)")
TOP_LEVEL = re.compile(r"^\S")
DECL_NAME = re.compile(r"\b(?:theorem|lemma|def|abbrev|instance|opaque|axiom)\s+([^\s(:{\[]+)")
# Lake prints `error: Proofs.lean:L:C: msg`; plain lean prints `Proofs.lean:L:C: error: msg`.
ERROR_LINE = re.compile(r"^(?:error: Proofs\.lean:(\d+):\d+:|Proofs\.lean:(\d+):\d+: error)", re.M)


def _blocks(lines):
    """Split a Lean file into top-level blocks: (start, end, is_decl)."""
    starts = [i for i, line in enumerate(lines) if TOP_LEVEL.match(line)]
    blocks, i = [], 0
    while i < len(starts):
        start = starts[i]
        j = i + 1
        # a docstring or attribute line belongs to the declaration that follows
        while lines[start].startswith(("/--", "@[")) and j < len(starts) and not DECL_NAME.search(
                "\n".join(lines[start:starts[j]])):
            j += 1
        end = starts[j] if j < len(starts) else len(lines)
        blocks.append((start, end, bool(DECL_START.match(lines[start]))))
        i = j
    return blocks


def build_proofs(ws, max_rounds=8):
    """Build the proof module, deleting declarations that fail to elaborate.

    Returns {theorem name: Lean error} for removed declarations. This only
    decides which proofs reach the comparator; the comparator re-checks
    everything that remains against the protected statements, so removal
    cannot make a false guarantee pass. Returns None when the proofs
    cannot be built even after removals (e.g. an error in an import).
    """
    removed = {}
    path = ws.root / "Proofs.lean"
    for _ in range(max_rounds):
        result = _lake(ws, ["build", "Proofs"])
        if result.status == 0:
            return removed
        text = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", result.output)
        error_lines = sorted({int(a or b) - 1 for a, b in ERROR_LINE.findall(text)})
        lines = path.read_text().splitlines()
        doomed = []
        for start, end, _ in _blocks(lines):
            # Any failing top-level block (declaration or command such as
            # `#eval`) is removed; imports are not, as removing one changes
            # what every later declaration means.
            if not lines[start].startswith("import ") and any(start <= n < end for n in error_lines):
                doomed.append((start, end))
        if not doomed:
            return None
        for start, end in reversed(doomed):
            block = "\n".join(lines[start:end])
            match = DECL_NAME.search(block)
            name = match.group(1) if match else f"line {start + 1}"
            messages = [m for m in _messages(text) if start < m[0] <= end]
            removed[name] = "\n".join(msg for _, msg in messages) or "does not elaborate"
            del lines[start:end]
        path.write_text("\n".join(lines) + "\n")
    return None


def _messages(text):
    out, current = [], None
    for line in text.splitlines():
        match = (re.match(r"^error: Proofs\.lean:(\d+):\d+:(.*)$", line)
                 or re.match(r"^Proofs\.lean:(\d+):\d+: error:?(.*)$", line))
        if match:
            current = [int(match.group(1)), "Proofs.lean:" + match.group(1) + ":" + match.group(2)]
            out.append(current)
        elif current is not None and line and not line.startswith(("error:", "✖", "⚠", "✔", "warning", "Some required")):
            if len(current[1]) < 2000:
                current[1] += "\n" + line
        else:
            current = None
    return [(n, msg) for n, msg in out]


@dataclass
class Verdict:
    accepted: bool
    reason: str
    output: str


def comparator(ws, theorems, timeout=1800):
    config = {
        "challenge_module": "Contract", "solution_module": "Proofs",
        "theorem_names": list(theorems), "definition_names": [],
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "external_kernels": {"nanoda": ["nanoda_bin"]},
    }
    (ws.root / "comparator.json").write_text(json.dumps(config))
    # lake comparator applies its own bwrap sandbox to the untrusted build.
    result = _comparator_run(ws, timeout)
    accepted = result.status == 0 and "Your solution is okay!" in result.output
    return Verdict(accepted, "" if accepted else classify(result.output), result.output)


def _comparator_run(ws, timeout):
    import subprocess
    try:
        done = subprocess.run(["lake", "comparator"], cwd=ws.root, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=timeout,
                              env={**os.environ, "HOME": "/tmp/home"})
        return sandbox.Result(done.returncode, done.stdout[-sandbox.MAX_OUTPUT:].decode("utf-8", "replace"))
    except subprocess.TimeoutExpired:
        return sandbox.Result(124, "comparator timed out", True)


def classify(output):
    text = output
    if "kernel rejected the solution" in text:
        return "the Lean kernel rejects the proof"
    if "statement do not match" in text or "statements do not match" in text:
        match = re.search(r"do not match: '([^']+)'", text)
        name = f" `{match.group(1)}`" if match else ""
        return f"the proof of{name} states something different from the contract"
    if "Building Proofs" in text and re.search(r"error: .*Proofs", text) and "Exporting" not in text.split("Building Proofs", 1)[1]:
        return "the proofs do not build:\n" + _errors(text.split("Building Proofs", 1)[1])
    if "sorryAx" in text or "uses `sorry`" in text.split("Building Proofs", 1)[-1]:
        return "a proof uses `sorry`"
    match = re.search(r"(?im)^.*axiom.*$", text.split("Building Proofs", 1)[-1])
    if match and "kernel accepts" not in match.group(0):
        return "a proof depends on a forbidden axiom: " + match.group(0).strip()
    for pattern in (r"(?im)^.*(does not match|mismatch|differs).*$", r"(?im)^.*not found.*$",
                    r"(?im)^.*rejects.*$", r"(?im)^error.*$"):
        match = re.search(pattern, text)
        if match:
            return match.group(0).strip()
    return "the comparator rejected the proofs"


def _errors(text, limit=30):
    cleaned = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", text)
    keep = [line for line in cleaned.splitlines()
            if not line.startswith(("- ", "⚠", "✔", "warning:", "Note:")) and line.strip()]
    errors = [i for i, line in enumerate(keep) if "error" in line]
    if errors:
        keep = keep[errors[0]:]
    return "\n".join(keep[:limit])
