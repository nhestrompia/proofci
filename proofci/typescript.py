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


def translator():
    default = Path(__file__).resolve().parent.parent / "typescript" / "translate.mjs"
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
    return Extraction(module, lean_file, crate_name, result.output, [], outcome["names"], outcome["failures"])
