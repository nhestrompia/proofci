"""Trusted translation of the candidate Rust code into Lean.

ProofCI always regenerates the Lean model itself from the pull request's Rust
source with pinned Charon and Aeneas. Any Lean translation committed in the
repository is ignored, so a pull request cannot supply a convenient model.

What is supported:

- a package on its own or as a member of a Cargo workspace (inherited
  `workspace = true` settings resolve as usual);
- path dependencies inside the repository and crates.io dependencies pinned
  by `Cargo.lock`, vendored beforehand by `fetch` (the only step with network
  access; it downloads and checks sources but runs none of them);
- build scripts and procedural macros, which run while the code compiles,
  offline, in a sandbox where every source file is read-only. A build script
  therefore cannot alter the code that is being translated.

Only what the declared target functions reach is translated (Charon
`--start-from`), so code elsewhere in the crate (async services, FFI, `unsafe`)
does not matter. If a target reaches code Aeneas cannot translate, that target
is reported as unsupported.
"""

import json
import re
import shutil
import tomllib
from dataclasses import dataclass
from pathlib import Path

from . import models, sandbox

MAX_STAGED_BYTES = 64 * 1024 * 1024
MAX_STAGED_FILES = 5000
RESERVED_MODULES = {"Contract", "Proofs", "ProofciAudit", "ProofciSpecs", "ProofciJs"}
SKIP_DIRS = {"target", "node_modules"}
DEP_TABLES = ("dependencies", "build-dependencies")
CARGO_ENV = {"CARGO_NET_OFFLINE": "true", "CARGO_TERM_COLOR": "never"}


class Unsupported(Exception):
    """The code is outside what ProofCI can translate."""


class FetchError(Exception):
    """Dependencies could not be downloaded (network or registry problem)."""


@dataclass
class Extraction:
    module: str          # Lean module name, e.g. "Ledger"
    lean_file: Path      # generated Lean source
    crate_name: str
    log: str
    modelled: list = None   # library functions given ProofCI models
    names: dict = None      # function in the manifest -> Lean name, where they differ
    failures: dict = None   # function in the manifest -> why it can't be translated
    signatures: dict = None # TypeScript: the shape of each translated function
    assumptions: dict = None # TypeScript: the outside calls the policy allows
    assumed: dict = None     # TypeScript: which of them each function relies on
    files: list = None      # TypeScript: the source files translated
    imports: dict = None    # TypeScript: where each of those files' imports resolve


@dataclass
class Staged:
    root: Path           # staged workspace root (or the package itself)
    package: str         # Cargo package name of the target
    crate_name: str      # Rust crate name (package name with `_`)
    has_registry_deps: bool


# --------------------------------------------------------------------- TOML

def _toml_key(key):
    return key if re.fullmatch(r"[A-Za-z0-9_-]+", key) else json.dumps(key)


def _toml_value(value):
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return repr(value)
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(_toml_value(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{" + ", ".join(f"{_toml_key(k)} = {_toml_value(v)}" for k, v in value.items()) + "}"
    raise Unsupported(f"unsupported value in Cargo.toml: {value!r}")


def toml_dumps(data, prefix=()):
    """Serialize parsed Cargo.toml data back to TOML.

    Every nested table is written as a `[a.b]` section, which TOML (and
    Cargo) treat exactly like the inline or dotted forms they came from.
    """
    plain, tables, arrays = [], [], []
    for key, value in data.items():
        if isinstance(value, dict):
            tables.append((key, value))
        elif isinstance(value, list) and value and all(isinstance(v, dict) for v in value):
            arrays.append((key, value))
        else:
            plain.append(f"{_toml_key(key)} = {_toml_value(value)}\n")
    out = "".join(plain)
    for key, value in tables:
        path = ".".join(_toml_key(k) for k in (*prefix, key))
        out += f"\n[{path}]\n" + toml_dumps(value, (*prefix, key))
    for key, items in arrays:
        path = ".".join(_toml_key(k) for k in (*prefix, key))
        for item in items:
            # Array-of-tables entries: nested tables stay inline.
            out += f"\n[[{path}]]\n" + "".join(
                f"{_toml_key(k)} = {_toml_value(v)}\n" for k, v in item.items())
    return out


# ------------------------------------------------------------------ staging

def _read_toml(path: Path):
    if not path.is_file() or path.is_symlink():
        raise Unsupported(f"{path} not found")
    try:
        return tomllib.loads(path.read_text())
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise Unsupported(f"{path.name} cannot be read: {error}") from None


def _within(root: Path, path: Path):
    return root in (path, *path.parents)


def _inside(checkout: Path, path: Path, what: str):
    resolved = path.resolve()
    if not _within(checkout, resolved):
        raise Unsupported(f"{what} leaves the repository: {path}")
    return resolved


def _find_workspace(checkout: Path, package_dir: Path, manifest: dict):
    explicit = manifest.get("package", {}).get("workspace")
    if isinstance(explicit, str):
        root = _inside(checkout, package_dir / explicit, "the workspace")
        return root if (root / "Cargo.toml").is_file() else None
    for directory in (package_dir, *package_dir.parents):
        if not _within(checkout, directory):
            break
        candidate = directory / "Cargo.toml"
        if candidate.is_file() and "workspace" in _read_toml(candidate):
            return directory
    return None


def _dependency_specs(manifest: dict):
    """(name, spec) for every non-dev dependency, including target-specific ones."""
    tables = [manifest.get(t, {}) for t in DEP_TABLES]
    for body in manifest.get("target", {}).values():
        tables += [body.get(t, {}) for t in DEP_TABLES]
    for deps in tables:
        yield from deps.items()


def _strip_dev(manifest: dict):
    """Drop dev-dependencies, which are only needed to build tests."""
    manifest = dict(manifest)
    manifest.pop("dev-dependencies", None)
    if "target" in manifest:
        manifest["target"] = {k: {t: v for t, v in body.items() if t != "dev-dependencies"}
                              for k, body in manifest["target"].items()}
    return manifest


def _copy_package(src: Path, dest: Path, budget):
    """Copy a package directory (sources and data files) without nested packages."""
    for path in sorted(src.rglob("*")):
        rel = path.relative_to(src)
        if any(part in SKIP_DIRS or part.startswith(".") for part in rel.parts):
            continue
        if any((src / Path(*rel.parts[:i]) / "Cargo.toml").is_file() for i in range(1, len(rel.parts))):
            continue  # inside a nested package, which is staged separately if needed
        if path.is_symlink():
            raise Unsupported(f"symbolic links are not supported: {path}")
        if path.is_dir() or rel == Path("Cargo.toml"):
            continue
        budget["files"] += 1
        budget["bytes"] += path.stat().st_size
        if budget["files"] > MAX_STAGED_FILES or budget["bytes"] > MAX_STAGED_BYTES:
            raise Unsupported("the code is too large for the current limits")
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)


def stage(checkout: Path, crate_rel: str, dest: Path) -> Staged:
    """Copy the target package, its path dependencies and its workspace
    manifest into `dest`, without dev-dependencies or unrelated members."""
    checkout = checkout.resolve()
    package_dir = _inside(checkout, checkout / crate_rel, "the crate")
    manifest = _read_toml(package_dir / "Cargo.toml")
    package = manifest.get("package")
    if not isinstance(package, dict) or not isinstance(package.get("name"), str):
        raise Unsupported("Cargo.toml must define [package] with a name")
    if manifest.get("lib", {}).get("proc-macro"):
        raise Unsupported("procedural macro crates are not supported as targets")

    workspace_dir = _find_workspace(checkout, package_dir, manifest)
    workspace = _read_toml(workspace_dir / "Cargo.toml") if workspace_dir else {}
    ws_table = workspace.get("workspace", {})
    ws_deps = ws_table.get("dependencies", {})
    root = (workspace_dir or package_dir).resolve()
    for key in ("patch", "replace"):
        if workspace.get(key) or manifest.get(key):
            raise Unsupported(f"[{key}] sections are not supported yet")

    # Follow path dependencies; note whether anything comes from crates.io.
    staged, queue, registry = {}, [package_dir], False
    while queue:
        directory = queue.pop()
        if directory in staged:
            continue
        if not _within(root, directory):
            raise Unsupported(f"path dependency {directory} is outside the workspace")
        data = _read_toml(directory / "Cargo.toml")
        staged[directory] = data
        for name, spec in _dependency_specs(data):
            base = directory
            if isinstance(spec, dict) and spec.get("workspace") is True:
                spec, base = ws_deps.get(name, {}), root
            if isinstance(spec, str):
                registry = True
            elif "git" in spec:
                raise Unsupported(f"git dependency `{name}` is not supported yet; use a crates.io release")
            elif "path" in spec:
                queue.append(_inside(checkout, base / spec["path"], f"path dependency `{name}`"))
            elif spec.get("registry") not in (None, "crates-io"):
                raise Unsupported(f"dependency `{name}` uses a registry other than crates.io")
            else:
                registry = True

    dest.mkdir(parents=True)
    budget = {"files": 0, "bytes": 0}
    members = []
    for directory, data in staged.items():
        rel = directory.relative_to(root)
        out_dir = dest / rel
        out_dir.mkdir(parents=True, exist_ok=True)
        _copy_package(directory, out_dir, budget)
        if directory != root or not workspace_dir:
            (out_dir / "Cargo.toml").write_text(toml_dumps(_strip_dev(data)))
        if rel != Path("."):
            members.append(rel.as_posix())

    if workspace_dir:
        root_manifest = _strip_dev(staged[root]) if root in staged else {}
        root_manifest["workspace"] = {
            **{k: v for k, v in ws_table.items() if k in ("resolver", "package", "dependencies", "lints")},
            "members": members,
        }
        if "profile" in workspace:
            root_manifest["profile"] = workspace["profile"]
        (dest / "Cargo.toml").write_text(toml_dumps(root_manifest))
    lock = root / "Cargo.lock"
    if lock.is_file() and not lock.is_symlink():
        shutil.copyfile(lock, dest / "Cargo.lock")
    name = package["name"]
    return Staged(dest, name, name.replace("-", "_"), registry)


def lean_module_name(crate_name: str):
    # Aeneas names the file after the crate in UpperCamelCase.
    module = "".join(part[:1].upper() + part[1:] for part in re.split(r"[-_]", crate_name) if part)
    if module in RESERVED_MODULES:
        raise Unsupported(f"crate name {crate_name!r} clashes with a ProofCI module name")
    return module


# ------------------------------------------------------------- dependencies

def _cargo_config(vendor_dir):
    return ('[source.crates-io]\nreplace-with = "vendored-sources"\n\n'
            f'[source.vendored-sources]\ndirectory = "{vendor_dir}"\n')


def fetch(checkout: Path, crate_rel: str, vendor_dir: Path, work: Path):
    """Download the crates.io dependencies pinned by Cargo.lock into `vendor_dir`.

    The only step with network access. `cargo vendor` resolves, downloads and
    checksums sources; it does not compile or run them.
    """
    staged = stage(checkout, crate_rel, work / "fetch")
    vendor_dir.mkdir(parents=True, exist_ok=True)
    if not staged.has_registry_deps:
        return staged
    home = work / "fetch-cargo-home"
    home.mkdir()
    result = sandbox.run(
        ["cargo", "vendor", "--versioned-dirs", "--quiet", str(vendor_dir)],
        writable=[staged.root, vendor_dir, home], cwd=staged.root, network=True,
        env={"CARGO_HOME": str(home), "CARGO_TERM_COLOR": "never"}, timeout=900)
    if result.status != 0:
        raise FetchError("dependencies could not be downloaded:\n" + _tail(result.output))
    return staged


# --------------------------------------------------------------- translation

def extract(checkout: Path, crate_rel: str, work: Path, start_from=(), vendor_dir=None,
            opaque=()) -> Extraction:
    staged = stage(checkout, crate_rel, work / "crate")
    module = lean_module_name(staged.crate_name)
    out = work / "extract"
    out.mkdir()
    home, target = work / "cargo-home", work / "target"
    home.mkdir()
    target.mkdir()
    readable = [staged.root]
    if staged.has_registry_deps:
        if not vendor_dir or not Path(vendor_dir).is_dir():
            raise Unsupported("the crate has crates.io dependencies; run `proofci fetch` first "
                              "(the GitHub Action does this automatically)")
        (home / "config.toml").write_text(_cargo_config(vendor_dir))
        readable.append(Path(vendor_dir))
    env = {**CARGO_ENV, "CARGO_HOME": str(home), "CARGO_TARGET_DIR": str(target)}

    # Settle Cargo.lock (dev-dependencies and unrelated members were removed)
    # without compiling anything.
    meta = sandbox.run(["sh", "-c", "cargo metadata --offline --format-version 1 >/dev/null"],
                       writable=[staged.root, home], readable=readable[1:], cwd=staged.root,
                       env=env, timeout=300)
    if meta.status != 0:
        raise Unsupported("Cargo could not resolve the crate offline:\n" + _tail(meta.output))

    # Compile and translate. Sources are read-only here: build scripts and
    # proc macros run in this step and must not alter the code being translated.
    llbc = out / f"{staged.crate_name}.llbc"
    args = ["charon", "cargo", "--preset=aeneas", "--dest-file", str(llbc)]
    for path in start_from:
        args += ["--start-from-if-exists", path]  # a missing function shows up in the contract check
    for path in opaque:  # kept as declarations only (axioms in Lean)
        args += ["--opaque", path]
    args += ["--", "--offline", "--locked", "-p", staged.package, "--lib"]
    charon = sandbox.run(args, readable=readable, writable=[out, home, target],
                         cwd=staged.root, env=env, timeout=900)
    if charon.status != 0 or not llbc.is_file():
        raise Unsupported("Charon could not translate the crate:\n" + _tail(charon.output))
    aeneas = sandbox.run(["aeneas", "-backend", "lean", "-dest", str(out), "-abort-on-error", str(llbc)],
                         writable=[out], cwd=out, timeout=600)
    lean_file = out / f"{module}.lean"
    if aeneas.status != 0 or not lean_file.is_file():
        raise Unsupported("Aeneas could not translate the code:\n" + _tail(aeneas.output))
    # Library functions Aeneas left as axioms get ProofCI's trusted models.
    source, modelled = models.apply(lean_file.read_text())
    lean_file.write_text(source)
    return Extraction(module, lean_file, staged.crate_name, charon.output + aeneas.output, modelled)


PROGRESS = re.compile(r"\[[#-]{5,}\]|^\s*$|cargo miri setup|rustup component add miri|"
                      r"^(Raised at|Re-raised at|Called from|Fatal error:|Compiler source:|\[Info \])")


def _tail(text, lines=40):
    cleaned = re.sub(r"\x1b\[[0-9;?]*[A-Za-z]", "", text)
    kept = [line for line in cleaned.splitlines() if not PROGRESS.search(line)]
    return "\n".join(kept[-lines:])
