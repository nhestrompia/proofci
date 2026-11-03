"""Delete build artifacts of Lean modules outside the import closure of Aeneas.

Proofs may import `Aeneas` and anything it imports transitively (which
includes a large part of Mathlib). Artifacts of every other module are
removed to keep the toolchain image small; importing one of those modules
fails with a build error instead of silently rebuilding.

usage: prune.py AENEAS_LEAN_DIR [--drop-ilean]
"""

import re
import sys
from pathlib import Path

IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»']+)", re.M)
ARTIFACT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".c",
                     ".trace", ".setup.json", ".ir.sig", ".ltar")


def package_roots(base: Path):
    roots = [base]
    roots += sorted(p for p in (base / ".lake" / "packages").iterdir() if p.is_dir())
    return roots


def find_source(module, roots):
    rel = Path(*module.split(".")).with_suffix(".lean")
    for root in roots:
        if (root / rel).is_file():
            return root / rel
    return None


def closure(seeds, roots):
    seen, stack = set(), list(seeds)
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        source = find_source(module, roots)
        if source is None:
            continue  # Init/Std/Lean from the toolchain
        header = source.read_text(errors="replace")
        for name in IMPORT.findall(header):
            if name not in seen:
                stack.append(name)
    return seen


def artifact_module(path: Path, lib: Path):
    rel = path.relative_to(lib).as_posix()
    if rel.endswith(".hash"):
        rel = rel[: -len(".hash")]
    for suffix in sorted(ARTIFACT_SUFFIXES, key=len, reverse=True):
        if rel.endswith(suffix):
            return rel[: -len(suffix)].replace("/", ".")
    return None


def main():
    base = Path(sys.argv[1])
    drop_ilean = "--drop-ilean" in sys.argv
    roots = package_roots(base)
    keep = closure(["Aeneas"], roots)
    removed = kept = 0
    # Aeneas' own package is small and partly precompiled as plugins: keep it whole.
    for root in roots[1:]:
        build = root / ".lake" / "build"
        for sub in ("lib/lean", "ir"):
            lib = build / sub
            if not lib.is_dir():
                continue
            for path in lib.rglob("*"):
                if not path.is_file():
                    continue
                module = artifact_module(path, lib)
                if module is None:
                    continue
                if module not in keep or (drop_ilean and path.name.endswith((".ilean", ".ilean.hash"))):
                    path.unlink()
                    removed += 1
                else:
                    kept += 1
    print(f"modules in closure: {len(keep)}; removed {removed} files; kept {kept}")


if __name__ == "__main__":
    main()
