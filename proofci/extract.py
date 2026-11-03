"""Trusted translation of the candidate Rust crate into Lean.

ProofCI always regenerates the Lean model itself from the pull request's Rust
source with pinned Charon and Aeneas. Any Lean translation committed in the
repository is ignored, so a pull request cannot supply a convenient model.

Only self-contained crates are supported: no dependencies, no build scripts,
no procedural macros and no `unsafe`. Anything else is reported as
unsupported rather than guessed at.
"""

import re
import shutil
import tomllib
from dataclasses import dataclass
from pathlib import Path

from . import sandbox

MAX_SOURCE_BYTES = 4 * 1024 * 1024
MAX_SOURCE_FILES = 200
UNSAFE = re.compile(r"\bunsafe\b")
RESERVED_MODULES = {"Contract", "Proofs", "ProofciAudit"}


class Unsupported(Exception):
    """The crate is outside the supported Rust subset."""


@dataclass
class Extraction:
    module: str          # Lean module name, e.g. "Ledger"
    lean_file: Path      # generated Lean source
    crate_name: str
    log: str


def _check_manifest(cargo_toml: Path):
    try:
        data = tomllib.loads(cargo_toml.read_text())
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise Unsupported(f"Cargo.toml cannot be read: {error}") from None
    package = data.get("package")
    if not isinstance(package, dict) or not isinstance(package.get("name"), str):
        raise Unsupported("Cargo.toml must define [package] with a name")
    if "workspace" in data:
        raise Unsupported("Cargo workspaces are not supported; point `crate` at a single package")
    for key in ("dependencies", "build-dependencies", "dev-dependencies", "target", "patch", "replace"):
        if data.get(key):
            raise Unsupported(f"crates with [{key}] are not supported yet")
    if "build" in package:
        raise Unsupported("build scripts are not supported")
    lib = data.get("lib", {})
    if lib.get("proc-macro"):
        raise Unsupported("procedural macro crates are not supported")
    return package["name"], lib.get("path", "src/lib.rs")


def stage(crate_dir: Path, dest: Path):
    """Copy only the crate manifest and Rust sources into a fresh directory."""
    cargo_toml = crate_dir / "Cargo.toml"
    if not cargo_toml.is_file() or cargo_toml.is_symlink():
        raise Unsupported(f"no Cargo.toml in {crate_dir}")
    name, lib_path = _check_manifest(cargo_toml)
    if (crate_dir / "build.rs").exists():
        raise Unsupported("build scripts (build.rs) are not supported")
    src = crate_dir / "src"
    if not src.is_dir() or src.is_symlink():
        raise Unsupported("the crate must keep its sources in src/")
    dest.mkdir(parents=True)
    shutil.copyfile(cargo_toml, dest / "Cargo.toml")
    if (crate_dir / "Cargo.lock").is_file() and not (crate_dir / "Cargo.lock").is_symlink():
        shutil.copyfile(crate_dir / "Cargo.lock", dest / "Cargo.lock")
    total, count = 0, 0
    for path in sorted(src.rglob("*")):
        if path.is_symlink():
            raise Unsupported(f"symbolic links are not supported: {path.relative_to(crate_dir)}")
        if path.is_dir():
            continue
        if path.suffix != ".rs":
            continue
        count += 1
        data = path.read_bytes()
        total += len(data)
        if count > MAX_SOURCE_FILES or total > MAX_SOURCE_BYTES:
            raise Unsupported("the crate is too large for the MVP limits")
        text = data.decode("utf-8", "replace")
        if UNSAFE.search(re.sub(r"//[^\n]*", "", text)):
            raise Unsupported(f"`unsafe` code is not supported ({path.relative_to(crate_dir)})")
        target = dest / path.relative_to(crate_dir)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    if not (dest / lib_path).is_file():
        raise Unsupported(f"library root {lib_path} not found")
    return name


def lean_module_name(crate_name: str):
    # Aeneas names the file after the crate in UpperCamelCase.
    module = "".join(part[:1].upper() + part[1:] for part in re.split(r"[-_]", crate_name) if part)
    if module in RESERVED_MODULES:
        raise Unsupported(f"crate name {crate_name!r} clashes with a ProofCI module name")
    return module


def extract(crate_dir: Path, work: Path) -> Extraction:
    staged = work / "crate"
    name = stage(crate_dir, staged)
    module = lean_module_name(name)
    out = work / "extract"
    out.mkdir()
    # Aeneas names the generated module after the LLBC file.
    llbc = out / f"{name.replace('-', '_')}.llbc"
    env = {"CARGO_HOME": str(work / "cargo-home"), "CARGO_NET_OFFLINE": "true",
           "CARGO_TARGET_DIR": str(work / "target")}
    (work / "cargo-home").mkdir()
    (work / "target").mkdir()
    charon = sandbox.run(
        ["charon", "cargo", "--preset=aeneas", "--dest-file", llbc, "--", "--offline"],
        writable=[staged, out, work / "cargo-home", work / "target"], cwd=staged, env=env, timeout=600,
    )
    if charon.status != 0 or not (llbc).is_file():
        raise Unsupported("Charon could not translate the crate:\n" + _tail(charon.output))
    aeneas = sandbox.run(
        ["aeneas", "-backend", "lean", "-dest", out, "-abort-on-error", llbc],
        writable=[out], cwd=out, timeout=600,
    )
    lean_file = out / f"{module}.lean"
    if aeneas.status != 0 or not lean_file.is_file():
        raise Unsupported("Aeneas could not translate the crate:\n" + _tail(aeneas.output))
    return Extraction(module, lean_file, name, charon.output + aeneas.output)


PROGRESS = re.compile(r"\[[#-]{5,}\]|^\s*$")


def _tail(text, lines=40):
    cleaned = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", text)
    kept = [line for line in cleaned.splitlines() if not PROGRESS.search(line)]
    return "\n".join(kept[-lines:])
