"""Translate a TypeScript package into Lean inside the sandbox.

The translator reads and type-checks the candidate's sources and never runs
them. See `typescript/translate.mjs` for the subset and `lean/ProofciJs.lean`
for what `number` means.
"""

import json
import os
import re
import shutil
from pathlib import Path
from urllib.parse import urlparse

from . import sandbox
from .extract import Extraction, FetchError, Unsupported, lean_module_name


MARKER = "PROOFCI_DIFF "
MAX_CASES = 4000


def translator():
    """The translator sits beside its installed compiler. Tests that mount a
    checkout over the code still use the compiler from the image."""
    installed = Path("/opt/proofci/typescript/translate.mjs")
    default = installed if installed.exists() else Path(__file__).resolve().parent.parent / "typescript" / "translate.mjs"
    return Path(os.environ.get("PROOFCI_TRANSLATOR", default))


def _lean_errors(output):
    return " ".join(line for line in output.splitlines() if not line.startswith(MARKER))[:800]


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


# --------------------------------------------------------------- dependencies
#
# The type checker reads the declarations of the packages a file imports, so a
# project that imports packages needs them installed. Installing is the only step
# with network access, and it never runs the project's code: the package manager
# gets `--ignore-scripts`, the project's own settings and plugins are removed from
# a private copy, and the lockfile may only name the public registry. The
# check itself stays offline and reads the result from `vendor_dir`, the way
# Rust reads its vendored crates.

REGISTRIES = {"registry.npmjs.org", "registry.yarnpkg.com"}
LOCKFILES = (("package-lock.json", "npm"), ("npm-shrinkwrap.json", "npm"),
             ("pnpm-lock.yaml", "pnpm"), ("yarn.lock", "yarn"))
# Files that configure or extend a package manager. A pull request controls
# them, and some run code (`.pnpmfile.cjs`, `yarnPath`), so the install never sees them.
CONFIG_FILES = {".npmrc", ".yarnrc", ".yarnrc.yml", ".pnpmfile.cjs", ".pnp.cjs", ".pnp.loader.mjs"}
CONFIG_DIRS = {".yarn"}
SKIPPED = {".git", "node_modules"}
MODULES = "modules"
INDEX = "dependencies.json"


def _tools():
    """The package managers sit in the image, pinned by lockfile (toolchain/Dockerfile)."""
    tools = Path(os.environ.get("PROOFCI_TS_TOOLS", "/opt/proofci/tools/node_modules"))
    npm = Path(os.environ.get("PROOFCI_NPM", "/opt/node/lib/node_modules/npm/bin/npm-cli.js"))
    return {"npm": npm, "pnpm": tools / "pnpm" / "bin" / "pnpm.cjs", "yarn": tools / "yarn" / "bin" / "yarn.js"}


def find_lockfile(checkout: Path, package_rel: str):
    """The nearest lockfile at or above the package, as (directory, file name, manager)."""
    checkout = checkout.resolve()
    directory = (checkout / package_rel).resolve()
    while checkout in (directory, *directory.parents):
        for name, manager in LOCKFILES:
            if (directory / name).is_file() and not (directory / name).is_symlink():
                return directory, name, manager
        if directory == checkout:
            break
        directory = directory.parent
    return None


def declares_dependencies(checkout: Path, package_rel: str):
    manifest = checkout / package_rel / "package.json"
    try:
        data = json.loads(manifest.read_text())
    except (OSError, ValueError):
        return False
    return any(data.get(key) for key in ("dependencies", "devDependencies", "optionalDependencies", "peerDependencies"))


def stage(checkout: Path, dest: Path):
    """A private copy of the checkout without Git data, installed packages or
    package manager settings. Package managers and the translator may write
    here; the checkout stays untouched."""

    def skip(directory, names):
        return {name for name in names if name in SKIPPED or name in CONFIG_FILES or name in CONFIG_DIRS}

    shutil.copytree(checkout, dest, symlinks=True, ignore=skip)
    return dest


def check_lockfile(path: Path, manager: str):
    """Reject a lockfile that would make the installer contact anything but the
    public registry (a git repository, another host, a local path). The lock's
    integrity hashes then decide what the packages are."""
    text = path.read_text(errors="replace")
    urls, problems = [], []
    if manager == "npm":
        try:
            data = json.loads(text)
        except ValueError as error:
            raise Unsupported(f"{path.name} is not valid JSON: {error}")
        entries = list(data.get("packages", {}).values())
        stack = list(data.get("dependencies", {}).values())
        while stack:
            entry = stack.pop()
            entries.append(entry)
            stack.extend(entry.get("dependencies", {}).values())
        for entry in entries:
            if isinstance(entry, dict) and entry.get("resolved") and not entry.get("link"):
                urls.append(entry["resolved"])
    elif manager == "pnpm":
        urls += re.findall(r"tarball:\s*['\"]?([^\s,}'\"]+)", text)
        if re.search(r"type:\s*git|repo:\s|directory:\s", text):
            problems.append("a git or local dependency")
    else:
        if "__metadata:" in text:
            raise Unsupported("this is a Yarn Berry lockfile (yarn 2 or later), which can run project code while "
                              "installing; ProofCI installs with npm, pnpm or Yarn 1 only")
        urls += re.findall(r'^\s*resolved\s+"?([^"\s]+)', text, re.M)
    for url in urls:
        host = urlparse(url).hostname
        if urlparse(url).scheme != "https" or host not in REGISTRIES:
            problems.append(url if len(url) < 100 else url[:97] + "...")
    if problems:
        raise Unsupported(f"{path.name} names a source other than the public npm registry ({problems[0]}); "
                          "only registry.npmjs.org and registry.yarnpkg.com are installed")


def _install_command(manager: str, cache: Path):
    tools = _tools()
    program = tools[manager]
    if manager == "npm":
        return ["node", str(program), "ci", "--ignore-scripts", "--no-audit", "--no-fund", "--no-update-notifier",
                "--userconfig", "/dev/null", "--globalconfig", "/dev/null", "--registry", "https://registry.npmjs.org/",
                "--cache", str(cache)]
    if manager == "pnpm":
        return ["node", str(program), "install", "--frozen-lockfile", "--ignore-scripts", "--ignore-pnpmfile",
                "--config.manage-package-manager-versions=false", "--store-dir", str(cache),
                "--registry", "https://registry.npmjs.org/"]
    return ["node", str(program), "install", "--frozen-lockfile", "--ignore-scripts", "--ignore-engines",
            "--non-interactive", "--no-progress", "--cache-folder", str(cache),
            "--registry", "https://registry.npmjs.org/", "--use-yarnrc", "/dev/null"]


def _module_dirs(root: Path):
    """Every `node_modules` below `root`, not counting those inside another."""
    found = []
    for directory, names, _ in os.walk(root):
        if "node_modules" in names:
            found.append(Path(directory) / "node_modules")
            names.remove("node_modules")
    return found


def install(checkout: Path, package_rel: str, vendor_dir: Path, work: Path):
    """Install the package's dependencies from its lockfile into `vendor_dir`.

    The only step with network access. Without a lockfile or without
    dependencies there is nothing to install. Packages that stay missing are
    handled by the translator as before: an outside call needs an `assumes` entry."""
    vendor_dir.mkdir(parents=True, exist_ok=True)
    lock = find_lockfile(checkout, package_rel)
    if lock is None or not declares_dependencies(checkout, package_rel):
        return None
    directory, name, manager = lock
    check_lockfile(directory / name, manager)
    staged = stage(checkout, work / "install")
    cwd = staged / directory.relative_to(checkout.resolve())
    cache = work / "install-cache"
    cache.mkdir()
    env = {"CI": "1", "npm_config_update_notifier": "false", "COREPACK_ENABLE_STRICT": "0",
           "PNPM_HOME": str(cache / "pnpm-home")}
    result = sandbox.run(_install_command(manager, cache), writable=[staged, cache], readable=[],
                         cwd=cwd, env=env, network=True, timeout=1800)
    if result.status != 0:
        raise FetchError(f"{manager} could not install the dependencies from {name}:\n" + result.output[-3000:])
    modules = []
    for found in _module_dirs(staged):
        relative = found.parent.relative_to(staged)
        destination = vendor_dir / MODULES / relative / "node_modules"
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(found), str(destination))
        modules.append(relative.as_posix())
    (vendor_dir / INDEX).write_text(json.dumps({"lockfile": name, "manager": manager, "modules": modules}))
    return modules


def link_dependencies(staged: Path, vendor_dir: Path):
    """Point each installed `node_modules` into the private copy of the code."""
    index = Path(vendor_dir) / INDEX
    if not index.is_file():
        return
    for relative in json.loads(index.read_text())["modules"]:
        target = Path(vendor_dir) / MODULES / relative / "node_modules"
        place = staged / relative
        if target.is_dir() and place.is_dir() and not (place / "node_modules").exists():
            (place / "node_modules").symlink_to(target)


def prepare(checkout: Path, work: Path, vendor_dir=None):
    """The code the translator and the comparison with Node read. It is the
    checkout itself unless packages were installed for it, in which case it is a
    private copy with those packages linked in, because the checkout is read-only."""
    if vendor_dir is None or not (Path(vendor_dir) / INDEX).is_file():
        return checkout
    staged = stage(checkout, work / "code")
    link_dependencies(staged, vendor_dir)
    return staged


def extract(checkout: Path, package_rel: str, work: Path, functions, policy_checkout=None, assumes=(),
            vendor_dir=None) -> Extraction:
    checkout = prepare(checkout, work, vendor_dir)
    root = checkout / package_rel
    crate_name = module_name(root)
    module = lean_module_name(crate_name)
    out = work / "translated"
    out.mkdir()
    config = out / "config.json"
    policy = Path(policy_checkout or checkout)
    config.write_text(json.dumps({"root": str(root), "module": module, "out": str(out), "targets": list(functions),
                                  "repository": str(checkout), "policyRoot": str(policy), "requireTypes": True,
                                  "assumes": [{"call": call, "signature": signature} for call, signature in assumes]}))
    program = translator()
    readable = [checkout, policy, program.parent] + ([Path(vendor_dir)] if vendor_dir else [])
    result = sandbox.run(["node", str(program), str(config)], readable=readable, writable=[out], cwd=out, timeout=300)
    if result.status != 0:
        raise Unsupported("the TypeScript translator failed:\n" + result.output[-4000:])
    outcome = json.loads(result.output.splitlines()[-1])
    if outcome.get("fatal"):
        raise Unsupported(outcome["fatal"])
    lean_file = out / f"{module}.lean"
    extraction = Extraction(module, lean_file, crate_name, result.output, [], outcome["names"], outcome["failures"])
    extraction.signatures = outcome["signatures"]
    extraction.assumptions = {call: signature for call, signature in assumes}
    extraction.assumed = outcome["assumed"]
    extraction.files = outcome["files"]
    extraction.imports = outcome["imports"]
    extraction.checkout = checkout
    extraction.vendor_dir = vendor_dir
    return extraction


def differential(checkout: Path, package_rel: str, work: Path, ws, extraction, cases=None, timeout=300):
    checkout = getattr(extraction, "checkout", None) or checkout
    """Compare the translated functions with Node on generated inputs.

    Returns (disagreements, notes). Only code that passed the translator's
    checks runs here, and only in the sandbox: it is the candidate's code, so
    this finds translator bugs and defends against nothing else."""
    out = work / "differential"
    out.mkdir()
    # The model of an assumed call has no body to run, so nothing can be compared.
    signatures = {t: s for t, s in extraction.signatures.items() if not extraction.assumed.get(t)}
    skipped = [f"not compared with Node: {t} relies on an assumed outside call" for t in extraction.signatures if t not in signatures]
    if not signatures:
        return [], skipped
    if cases is None:  # each case takes about 8 ms to replay
        cases = max(25, min(200, MAX_CASES // max(len(signatures), 1)))
    config = out / "config.json"
    config.write_text(json.dumps({
        "root": str(checkout / package_rel), "out": str(out), "module": extraction.module, "cases": cases,
        "signatures": signatures, "files": extraction.files,
        "imports": extraction.imports}))
    program = translator().parent / "differential.mjs"
    vendor = getattr(extraction, "vendor_dir", None)
    node = sandbox.run(["node", str(program), str(config)], readable=[checkout, program.parent] + ([Path(vendor)] if vendor else []),
                       writable=[out], cwd=out, timeout=60)
    if node.status != 0:
        return ["the comparison with Node did not run: " + node.output[-600:]], []
    notes = skipped + [f"not compared with Node: {item}" for item in json.loads(node.output.splitlines()[-1])["skipped"]]
    replay = sandbox.run(["lake", "env", "lean", str(out / "Differential.lean")], readable=[ws.root, out],
                         writable=[ws.root / ".lake"], cwd=ws.root, timeout=timeout)
    if replay.timed_out:
        return [f"the comparison with Node didn't finish in {timeout} seconds"], notes
    counts = {"agree": 0, "differ": 0, "failed": 0}
    disagreements = []
    for line in replay.output.splitlines():
        if line.startswith(MARKER):
            kind, _, label = line[len(MARKER):].partition(" ")
            counts[kind] += 1
            if kind == "differ":
                disagreements.append(label)
    labels = json.loads((out / "cases.json").read_text())
    expected = len(labels)
    disagreements = [labels[int(index)] for index in disagreements]
    if sum(counts.values()) != expected:
        # Every case must report. One that doesn't compile compares nothing.
        return [f"only {sum(counts.values())} of {expected} comparisons ran: " + _lean_errors(replay.output)], notes
    notes.append(f"compared with Node: {counts['agree']} results agree, "
                 f"{counts['failed']} inputs left the safe-integer model")
    return disagreements, notes
