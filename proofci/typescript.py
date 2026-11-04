"""Translate a TypeScript package into Lean inside the sandbox.

The translator reads and type-checks the candidate's sources and never runs
them. See `typescript/translate.mjs` for the subset and `lean/ProofciJs.lean`
for what `number` means.
"""

import json
import os
import re
from pathlib import Path

from . import sandbox
from .extract import Extraction, Unsupported, lean_module_name


MARKER = "PROOFCI_DIFF "


def translator():
    """The translator sits beside its installed compiler. Tests that mount a
    checkout over the code still use the compiler from the image."""
    installed = Path("/opt/proofci/typescript/translate.mjs")
    default = installed if installed.exists() else Path(__file__).resolve().parent.parent / "typescript" / "translate.mjs"
    return Path(os.environ.get("PROOFCI_TRANSLATOR", default))


def module_name(root: Path):
    """The Lean module, from the package name: `@acme/bank-core` -> `BankCore`."""
    name = root.resolve().name
    manifest = root / "package.json"
    if manifest.is_file() and not manifest.is_symlink():
        try:
            declared = json.loads(manifest.read_text()).get("name")
        except (ValueError, OSError):
            declared = None
        if isinstance(declared, str) and declared:
            name = declared.rsplit("/", 1)[-1]
    name = re.sub(r"[^A-Za-z0-9_]", "_", name).lstrip("_0123456789")
    return name or "package"


def extract(checkout: Path, package_rel: str, work: Path, functions) -> Extraction:
    root = checkout / package_rel
    crate_name = module_name(root)
    module = lean_module_name(crate_name)
    out = work / "translated"
    out.mkdir()
    config = out / "config.json"
    config.write_text(json.dumps({"root": str(root), "module": module, "out": str(out), "targets": list(functions)}))
    program = translator()
    result = sandbox.run(["node", str(program), str(config)], readable=[checkout, program.parent],
                         writable=[out], cwd=out, timeout=300)
    if result.status != 0:
        raise Unsupported("the TypeScript translator failed:\n" + result.output[-4000:])
    outcome = json.loads(result.output.splitlines()[-1])
    if outcome.get("fatal"):
        raise Unsupported(outcome["fatal"])
    lean_file = out / f"{module}.lean"
    extraction = Extraction(module, lean_file, crate_name, result.output, [], outcome["names"], outcome["failures"])
    extraction.signatures = outcome["signatures"]
    extraction.files = outcome["files"]
    return extraction


def differential(checkout: Path, package_rel: str, work: Path, ws, extraction, cases=200):
    """Compare the translated functions with Node on generated inputs.

    Returns (disagreements, notes). Only code that passed the translator's
    checks runs here, and only in the sandbox: it is the candidate's code, so
    this finds translator bugs and defends against nothing else."""
    out = work / "differential"
    out.mkdir()
    config = out / "config.json"
    config.write_text(json.dumps({
        "root": str(checkout / package_rel), "out": str(out), "module": extraction.module, "cases": cases,
        "signatures": extraction.signatures, "files": extraction.files}))
    program = translator().parent / "differential.mjs"
    node = sandbox.run(["node", str(program), str(config)], readable=[checkout, program.parent],
                       writable=[out], cwd=out, timeout=60)
    if node.status != 0:
        return [], ["the comparison with Node did not run: " + node.output[-600:]]
    notes = [f"not compared with Node: {item}" for item in json.loads(node.output.splitlines()[-1])["skipped"]]
    replay = sandbox.run(["lake", "env", "lean", str(out / "Differential.lean")], readable=[ws.root, out],
                         writable=[ws.root / ".lake"], cwd=ws.root, timeout=300)
    counts = {"agree": 0, "differ": 0, "failed": 0}
    disagreements = []
    for line in replay.output.splitlines():
        if line.startswith(MARKER):
            kind, _, label = line[len(MARKER):].partition(" ")
            counts[kind] += 1
            if kind == "differ":
                disagreements.append(label)
    if not sum(counts.values()):
        return [], ["the comparison with Node did not run: " + replay.output[-600:]]
    notes.append(f"compared with Node: {counts['agree']} results agree, "
                 f"{counts['failed']} inputs left the safe-integer model")
    return disagreements, notes
