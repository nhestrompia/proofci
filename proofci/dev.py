"""`proofci dev`: fast feedback while writing proofs.

Keeps a workspace between runs. The Rust code is re-translated and the
contract rebuilt only when they change; otherwise a run only rebuilds the
proofs and prints Lean's messages (errors, unsolved goals), which is what a
person or an agent needs to iterate. `--judge` then runs the same comparator
check as CI on the current proofs. `--json` prints one machine-readable
document instead of log lines: what failed to translate, Lean's errors with
file and line, and each guarantee's verdict.

This is a convenience for authors. CI always runs `proofci check`, which
shares none of this cached state.
"""

import hashlib
import json
import shutil
import time
from pathlib import Path

from . import claims, extract, lean, typescript
from .check import ConfigError, lean_function, load_manifest


def _digest(paths):
    h = hashlib.sha256()
    for root in paths:
        root = Path(root)
        files = sorted(p for p in root.rglob("*") if p.is_file()) if root.is_dir() else [root]
        for p in files:
            if any(part in ("target", ".lake", ".git") for part in p.parts):
                continue
            h.update(str(p).encode() + b"\0" + p.read_bytes() + b"\0")
    return h.hexdigest()


def _report(output, limit=60000):
    """Lean's messages, errors first (in full), then infos; warnings only counted."""
    blocks, current = [], None
    for line in output.splitlines():
        if line.startswith(("error:", "warning:", "info:")):
            current = [line]
            blocks.append(current)
        elif line.startswith(("trace:", "✔", "ℹ [", "⚠ [", "✖ [", "Build completed", "Some required", "- ")):
            current = None
        elif current is not None:
            current.append(line)
    errors = [b for b in blocks if b[0].startswith("error:") and b[0] != "error: build failed"]
    infos = [b for b in blocks if b[0].startswith("info:")]
    warnings = [b for b in blocks if b[0].startswith("warning:")]
    text = "\n\n".join("\n".join(b) for b in errors + infos)
    if len(text) > limit:
        text = text[:limit] + "\n… (truncated)"
    summary = f"{len(errors)} error(s), {len(warnings)} warning(s)"
    return (text + "\n\n" if text else "") + summary


def run(repo: Path, work: Path, vendor=None, judge=False, show=False, as_json=False, out=print):
    repo = repo.resolve()
    manifest = load_manifest(repo)
    work.mkdir(parents=True, exist_ok=True)
    state_file = work / "state.json"
    state = json.loads(state_file.read_text()) if state_file.exists() else {}
    functions = sorted({t.function for t in manifest.targets})
    result = {"unsupported": {}, "errors": [], "guarantees": []}

    say = (lambda *args: None) if as_json else out

    def done(status):
        result["ok"] = status == 0
        if as_json:
            out(json.dumps(result, indent=2))
        return status

    t0 = time.monotonic()
    crate_key = (_digest([repo / manifest.crate]) + json.dumps(functions)
                 + json.dumps([manifest.assumes, [e.entry() for e in manifest.effects]]))
    if vendor and (Path(vendor) / typescript.INDEX).is_file():
        crate_key += (Path(vendor) / typescript.INDEX).read_text()
    ws_root = work / "lean"
    if state.get("crate") != crate_key or not ws_root.exists():
        for name in ("translate", "lean"):
            shutil.rmtree(work / name, ignore_errors=True)
        (work / "translate").mkdir()
        try:
            if manifest.language == "typescript":
                ex = typescript.extract(repo, manifest.crate, work / "translate", functions, assumes=manifest.assumes, effects=manifest.effects,
                                   vendor_dir=vendor)
                for function, reason in ex.failures.items():
                    say(f"unsupported: {function}: {reason}")
                    head, hint = typescript.split_hint(reason)
                    result["unsupported"][function] = {"reason": head, "hint": hint}
                if len(ex.failures) == len(functions):
                    return done(1)
            else:
                ex = extract.extract(repo, manifest.crate, work / "translate", start_from=functions, vendor_dir=vendor)
        except extract.Unsupported as error:
            say(f"unsupported: {error}")
            head, hint = typescript.split_hint(str(error))
            result["unsupported"]["*"] = {"reason": head, "hint": hint}
            return done(1)
        ws = lean.assemble(ws_root, ex.lean_file, ex.module, repo / manifest.lean, repo / manifest.lean)
        state = {"crate": crate_key, "module": ex.module, "modelled": ex.modelled,
                 "names": ex.names or {}, "unsupported": result["unsupported"]}
        say(f"translated the code ({time.monotonic() - t0:.1f}s); "
            f"standard-library models used: {len(ex.modelled)}")
    else:
        result["unsupported"] = state.get("unsupported", {})
        ws = lean.Workspace(ws_root, state["module"])
        # Refresh the Lean sources from the repository.
        for module in ("Contract", "Proofs"):
            for stale in (ws_root / f"{module}.lean", ws_root / module):
                if stale.is_dir():
                    shutil.rmtree(stale)
                elif stale.exists():
                    stale.unlink()
            lean._copy_lean_tree(repo / manifest.lean, module, ws_root, required=module == "Contract")
    state_file.write_text(json.dumps(state))
    if show:
        say((ws_root / f"{state['module']}.lean").read_text())

    t1 = time.monotonic()
    contract = lean._lake(ws, ["build", "Contract"])
    if contract.status != 0:
        say("the contract does not build:\n" + lean._errors(contract.output, limit=80))
        result["errors"] = lean.structured_errors(contract.output)
        return done(1)
    if not (ws_root / "Proofs.lean").exists():
        say(f"no {manifest.proofs} yet")
        return done(1)
    proofs = lean._lake(ws, ["build", "Proofs"])
    say(_report(proofs.output))
    say(f"proofs {'build' if proofs.status == 0 else 'do not build'} ({time.monotonic() - t1:.1f}s)")
    result["errors"] = lean.structured_errors(proofs.output)
    if proofs.status != 0 or not judge:
        return done(0 if proofs.status == 0 else 1)

    status = 0
    contract = repo / manifest.lean / "Contract.lean"
    stated = claims.theorems(contract.read_text()) if contract.is_file() else {}
    for target, guarantee in manifest.guarantees():
        trial = lean.clone(ws, work / f"judge-{guarantee.theorem}")
        try:
            verdict = lean.comparator(trial, [guarantee.theorem])
        finally:
            shutil.rmtree(trial.root, ignore_errors=True)
        mark = "verified" if verdict.accepted else f"not verified: {verdict.reason}"
        lean_name = state.get("names", {}).get(target.function, lean_function(target.function))
        say(f"{target.id}/{guarantee.id} ({lean_name}): {mark}")
        info = stated.get(guarantee.theorem) or {}
        result["guarantees"].append({
            "guarantee": f"{target.id}/{guarantee.id}", "function": target.function,
            "theorem": guarantee.theorem, "verified": verdict.accepted, "reason": verdict.reason,
            "claim": info.get("claim"), "hypotheses": info.get("hypotheses")})
        status |= 0 if verdict.accepted else 1
    return done(status)


__all__ = ["run", "ConfigError"]
