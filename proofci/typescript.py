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


def support_dir():
    """Where the translator's companions (the comparison with Node) sit, whatever `PROOFCI_TRANSLATOR` says."""
    installed = Path("/opt/proofci/typescript")
    return installed if installed.exists() else Path(__file__).resolve().parent.parent / "typescript"


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


def stage(checkout: Path, dest: Path, exclude=None):
    """A private copy of the checkout without Git data, installed packages or
    package manager settings. Package managers and the translator may write
    here; the checkout stays untouched. `exclude` is a directory (the vendor
    output) that must not be copied along: vendored packages sit inside the
    repo on some setups, and copying them back in would copy the repo into
    itself."""
    excluded = Path(exclude).resolve() if exclude else None

    def is_excluded(path):
        if excluded is None:
            return False
        resolved = path.resolve()
        if excluded in (resolved, *resolved.parents):
            return True
        try:
            # A bind mount makes the same directory appear under another path
            # (the vendor dir is mounted inside the checkout in Docker).
            return path.samefile(excluded)
        except OSError:
            return False

    def skip(directory, names):
        found = {name for name in names if name in SKIPPED or name in CONFIG_FILES or name in CONFIG_DIRS}
        if excluded is not None:
            found |= {name for name in names if is_excluded(Path(directory, name))}
        return found

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
        if isinstance(data.get("packages"), dict):
            return  # lockfile version 2 or 3: packages from elsewhere are left out of the install
        stack = list(data.get("dependencies", {}).values())
        while stack:
            entry = stack.pop()
            if isinstance(entry, dict):
                if entry.get("resolved") and not entry.get("link"):
                    urls.append(entry["resolved"])
                stack.extend(entry.get("dependencies", {}).values())
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


def drop_foreign_packages(cwd: Path):
    """Remove from the private copy's npm lockfile the packages that would be
    fetched from anywhere but the public registry (git repositories, other
    hosts, paths), along with the root's dependencies on them. The rest is
    installed, and the dropped names are returned so the report can say that
    their types are unknown. Only the copy changes."""
    lock = cwd / "package-lock.json"
    if not lock.is_file():
        lock = cwd / "npm-shrinkwrap.json"
    data = json.loads(lock.read_text())
    packages = data.get("packages")
    if not isinstance(packages, dict):
        return []  # a lockfile without `packages` (version 1) is checked and installed as it is

    def foreign(entry):
        url = entry.get("resolved") if isinstance(entry, dict) else None
        return bool(url) and not entry.get("link") and not _from_registry(url)

    dropped = sorted(key for key, entry in packages.items() if key and foreign(entry))
    if not dropped:
        return []
    names = {key.rsplit("node_modules/", 1)[-1] for key in dropped}
    for key in [k for k in packages if k and any(k == d or k.startswith(d + "/") for d in dropped)]:
        del packages[key]  # the package and what is nested inside it
    for key, entry in packages.items():
        if not isinstance(entry, dict):
            continue
        own = key == "" or not key.startswith("node_modules/") and "/node_modules/" not in key  # root and workspaces
        for field in ("dependencies", "devDependencies", "optionalDependencies", "peerDependencies"):
            for name in names & set(entry.get(field, {})):
                del entry[field][name]  # the lock's record of what each package needs
                manifest = cwd / key / "package.json"
                if own and manifest.is_file():
                    written = json.loads(manifest.read_text())
                    written.get(field, {}).pop(name, None)
                    manifest.write_text(json.dumps(written))
    lock.write_text(json.dumps(data))
    return sorted(names)


def _from_registry(url: str):
    parsed = urlparse(url)
    return parsed.scheme == "https" and parsed.hostname in REGISTRIES


def _install_command(manager: str, cache: Path):
    tools = _tools()
    program = tools[manager]
    if manager == "npm":
        # Empty settings files, so that nothing but the flags below configures npm.
        user, system = cache / "npmrc-user", cache / "npmrc-global"
        user.write_text("")
        system.write_text("")
        return ["node", str(program), "ci", "--ignore-scripts", "--no-audit", "--no-fund", "--no-update-notifier",
                "--userconfig", str(user), "--globalconfig", str(system), "--registry", "https://registry.npmjs.org/",
                "--cache", str(cache / "npm")]
    if manager == "pnpm":
        return ["node", str(program), "install", "--frozen-lockfile", "--ignore-scripts", "--ignore-pnpmfile",
                "--config.manage-package-manager-versions=false", "--store-dir", str(cache / "pnpm-store"),
                "--registry", "https://registry.npmjs.org/"]
    (cache / "yarnrc").write_text("")
    return ["node", str(program), "install", "--frozen-lockfile", "--ignore-scripts", "--ignore-engines",
            "--non-interactive", "--no-progress", "--cache-folder", str(cache / "yarn"),
            "--registry", "https://registry.npmjs.org/", "--use-yarnrc", str(cache / "yarnrc")]


def _excerpt(output: str, size=1800):
    """The start and the end of a package manager's output: the first error and its summary."""
    if len(output) <= 2 * size:
        return output
    return output[:size] + "\n[...]\n" + output[-size:]


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
    try:
        check_lockfile(directory / name, manager)
    except Unsupported as problem:
        # `check` still runs and says why packages are missing.
        (vendor_dir / INDEX).write_text(json.dumps({"lockfile": name, "manager": manager, "modules": [], "error": str(problem)}))
        raise
    staged = stage(checkout, work / "install", exclude=vendor_dir)
    cwd = staged / directory.relative_to(checkout.resolve())
    skipped = drop_foreign_packages(cwd) if manager == "npm" else []
    cache = work / "install-cache"
    cache.mkdir()
    env = {"CI": "1", "npm_config_update_notifier": "false", "COREPACK_ENABLE_STRICT": "0",
           "PNPM_HOME": str(cache / "pnpm-home")}
    result = sandbox.run(_install_command(manager, cache), writable=[staged, cache], readable=[],
                         cwd=cwd, env=env, network=True, timeout=1800)
    if result.status != 0:
        raise FetchError(f"{manager} could not install the dependencies from {name}:\n" + _excerpt(result.output))
    modules = []
    for found in _module_dirs(staged):
        relative = found.parent.relative_to(staged)
        destination = vendor_dir / MODULES / relative / "node_modules"
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(found), str(destination))
        modules.append(relative.as_posix())
    (vendor_dir / INDEX).write_text(json.dumps({"lockfile": name, "manager": manager, "modules": modules, "skipped": skipped}))
    return modules


def prepare(checkout: Path, work: Path, vendor_dir=None):
    """The code the translator and the comparison with Node read, and the
    directories to mount into it: `(root, binds)`.

    It is the checkout itself unless packages were installed for it. Then it is
    a private copy with an empty `node_modules` where each installed one belongs,
    because the translator only reads declarations that sit inside the code it
    reads, and the checkout is read-only. The sandbox mounts the installed
    packages onto those empty directories."""
    index = Path(vendor_dir) / INDEX if vendor_dir else None
    if index is None or not index.is_file():
        return checkout, []
    staged = stage(checkout, work / "code", exclude=vendor_dir)
    binds = []
    for relative in json.loads(index.read_text())["modules"]:
        source = Path(vendor_dir) / MODULES / relative / "node_modules"
        place = staged / relative
        if source.is_dir() and place.is_dir() and not (place / "node_modules").exists():
            (place / "node_modules").mkdir()
            binds.append((source, place / "node_modules"))
    return staged, binds


HINT = "\nHow to fix: "


def with_note(reason, note):
    """Adds `note` to a translator reason, before its hint."""
    head, mark, hint = reason.partition(HINT)
    return head + "\n" + note + mark + hint


def split_hint(reason):
    """A translator reason and its "How to fix" hint, or None."""
    head, _, hint = reason.partition(HINT)
    return head, hint or None


def missing_packages_hint(checkout: Path, package_rel: str, vendor_dir=None):
    """Why a type from a package may be unknown: they were not installed."""
    index = Path(vendor_dir) / INDEX if vendor_dir else None
    recorded = json.loads(index.read_text()) if index and index.is_file() else {}
    if recorded.get("error"):
        return "This project's packages were not installed: " + recorded["error"]
    if recorded.get("skipped"):
        return ("Not installed, because they do not come from the public npm registry: "
                + ", ".join(recorded["skipped"][:8]) + (", ..." if len(recorded["skipped"]) > 8 else ""))
    if recorded.get("modules") or not declares_dependencies(checkout, package_rel):
        return None
    if find_lockfile(checkout, package_rel) is None:
        return ("This project's packages are not installed, so types from them are unknown. ProofCI installs "
                "them from a lockfile; commit package-lock.json, pnpm-lock.yaml or yarn.lock.")
    return ("This project's packages are not installed, so types from them are unknown. "
            "Run `proofci fetch` and pass its output as --vendor.")


def extract(checkout: Path, package_rel: str, work: Path, functions, policy_checkout=None, assumes=(),
            vendor_dir=None, effects=()) -> Extraction:
    original = checkout
    checkout, binds = prepare(checkout, work, vendor_dir)
    root = checkout / package_rel
    crate_name = module_name(root)
    module = lean_module_name(crate_name)
    out = work / "translated"
    out.mkdir()
    config = out / "config.json"
    policy = Path(policy_checkout or checkout)
    config.write_text(json.dumps({"root": str(root), "module": module, "out": str(out), "targets": list(functions),
                                  "repository": str(checkout), "policyRoot": str(policy), "requireTypes": True,
                                  "assumes": [{"call": call, "signature": signature} for call, signature in assumes],
                                  "effects": [e.entry() for e in effects]}))
    program = translator()
    result = sandbox.run(["node", str(program), str(config)], readable=[checkout, policy, program.parent],
                         binds=binds, writable=[out], cwd=out, timeout=300)
    if result.status != 0:
        raise Unsupported("the TypeScript translator failed:\n" + result.output[-4000:])
    outcome = json.loads(result.output.splitlines()[-1])
    hint = missing_packages_hint(original, package_rel, vendor_dir)
    unknown = re.compile(r"not supported yet|TypeScript error|Cannot find|no source")
    if outcome.get("fatal"):
        raise Unsupported(with_note(outcome["fatal"], hint) if hint and unknown.search(outcome["fatal"]) else outcome["fatal"])
    lean_file = out / f"{module}.lean"
    extraction = Extraction(module, lean_file, crate_name, result.output, [], outcome["names"], outcome["failures"])
    extraction.signatures = outcome["signatures"]
    extraction.assumptions = {call: signature for call, signature in assumes}
    extraction.assumed = outcome["assumed"]
    extraction.effects = outcome.get("effects") or {}
    extraction.arguments_relied = outcome.get("argumentsRelied") or {}
    extraction.constants_relied = outcome.get("constantsRelied") or {}
    extraction.effect_list = outcome.get("effectList") or []
    extraction.effect_text = {e.id: f"{e.kind} {e.target}{e.signature}" + (f", assumed to answer {e.narrowed}" if e.narrowed else "") for e in effects}
    extraction.files = outcome["files"]
    extraction.imports = outcome["imports"]
    for function, reason in list(extraction.failures.items()):
        if hint and unknown.search(reason):
            extraction.failures[function] = with_note(reason, hint)
    extraction.checkout = checkout
    extraction.binds = binds
    # What the bridge generator needs to read the code the same way the translator did.
    extraction.root = root
    extraction.policy = policy
    extraction.effect_entries = [e.entry() for e in effects]
    return extraction


def probe(checkout: Path, package_rel: str, work: Path, assumes=(), effects=(), vendor_dir=None):
    """Which exported functions of the package translate, and why the rest don't.

    The agent-facing scan behind `proofci scan`: same translator and sandbox as
    `extract`, over every exported function rather than only the manifest's
    targets. Returns {"module": name, "functions": [{"function", "translated",
    "reason", "hint"}]}; a refused function's reason is split into its fix-it
    hint the way `check` reports it."""
    checkout, binds = prepare(checkout, work, vendor_dir)
    root = checkout / package_rel
    out = work / "probe"
    out.mkdir(parents=True, exist_ok=True)
    config = out / "config.json"
    config.write_text(json.dumps({
        "root": str(root), "module": lean_module_name(module_name(root)), "repository": str(checkout),
        "assumes": [{"call": call, "signature": signature} for call, signature in assumes],
        "effects": [e.entry() for e in effects]}))
    program = support_dir() / "probe.mjs"
    result = sandbox.run(["node", str(program), str(config)], readable=[checkout, program.parent],
                         binds=binds, writable=[out], cwd=out, timeout=300)
    if result.status != 0 or not result.output.strip():
        raise Unsupported("the scan failed:\n" + result.output[-2000:])
    try:
        outcome = json.loads(result.output.splitlines()[-1])
    except ValueError:
        raise Unsupported("the scan gave no result:\n" + result.output[-2000:])
    if outcome.get("fatal"):
        # A partial inventory would read as the answer; refuse instead.
        raise Unsupported("the scan failed: " + outcome["fatal"])
    for entry in outcome.get("functions", []):
        if entry.get("reason"):
            entry["reason"], entry["hint"] = split_hint(entry["reason"])
    return outcome


def _node_failure(result):
    """Why the Node comparison never ran, with the process's last output: an
    infrastructure failure (crash, OOM, timeout), never a disagreement."""
    tail = " ".join(result.output.strip().split())[-400:]
    if result.timed_out:
        head = "the Node process that runs the comparison did not finish in time"
    elif result.status in (134, 137, -6, -9) or "out of memory" in result.output.lower() or "heap" in result.output.lower():
        head = "the Node process that runs the comparison ran out of memory"
    else:
        head = f"the Node process that runs the comparison exited with status {result.status}"
    return head + (f"; its last output was: {tail}" if tail else " and printed nothing")


def uncalled(checkout: Path, package_rel: str, functions):
    """Target functions nothing else in the repository imports or calls.

    A proof about a copy no shipped file references covers dead code. Returns
    the subset of `functions` (`file.ts::name`, package-relative) with no
    importer: static, and conservative — relative specifiers are resolved over
    the whole checkout, bare specifiers only through each package's published
    name, re-exports are followed, and any doubt means no warning."""
    root = checkout.resolve()
    package_root = package_rel.strip("/")
    sources = {}   # normalized repo-relative extensionless path -> Path
    refs = {}      # source key -> (text, [(resolved key, reexport, names, ns_alias)])
    packages = {}  # published package name -> repo-relative dir (monorepo neighbours)
    for path in sorted(p for ext in ("*.ts", "*.tsx", "*.mts", "*.cts") for p in root.rglob(ext)):
        if not path.is_file() or path.is_symlink():
            continue
        rel = path.relative_to(root)
        if rel.name.endswith(".d.ts") or _TEST_FILE.search(rel.name):
            continue
        if any(p in _SKIP_DIRS for p in rel.parts):
            continue
        key = str(rel.with_suffix(""))
        sources[key] = path
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        refs[key] = (text, _references(text))
    for path in sorted(root.rglob("package.json")):
        rel = path.relative_to(root)
        if any(p in _SKIP_DIRS for p in rel.parts):
            continue
        name = _package_json(path).get("name")
        if isinstance(name, str) and name:
            packages[name] = "" if str(rel.parent) == "." else str(rel.parent)
    resolved = {
        key: (text, [
            (frozenset(_resolve(spec, Path(key).parent, root, packages)), reexport, names, ns)
            for spec, reexport, names, ns in items])
        for key, (text, items) in refs.items()}
    uncalled = []
    for function in functions:
        file_part, _, name = function.rpartition("::")
        target_key = str(Path(package_root) / file_part)
        for ext in _EXTS:
            if target_key.endswith(ext):
                target_key = target_key[: -len(ext)]
        if target_key not in sources:
            continue
        providers = {target_key}
        users = set()
        changed = True
        while changed:   # re-exports make another file provide the same name
            changed = False
            for key, (text, items) in resolved.items():
                if key == target_key or key in users:
                    continue
                for mods, reexport, names, ns in items:
                    if not any(mod in providers or mod + "/index" in providers for mod in mods):
                        continue
                    if names is not None and name not in names:
                        if ns is None or not re.search(rf"\b{re.escape(ns)}\s*\.\s*{re.escape(name)}\b", text):
                            continue
                    users.add(key)
                    if reexport and key not in providers:
                        providers.add(key)
                        changed = True
        if not users:
            uncalled.append(function)
    return uncalled


_SKIP_DIRS = {"node_modules", ".git", "proofci", "__tests__", "__mocks__", "test", "tests", "spec", "e2e"}
_TEST_FILE = re.compile(r"[._-](test|spec|stories|e2e)\.[cm]?tsx?$")


def _package_json(path: Path):
    try:
        return json.loads(path.read_text(errors="replace"))
    except (OSError, json.JSONDecodeError):
        return {}


_REFERENCE = re.compile(r"""(?x)
    \bimport\s+(?:type\s+)?(?P<iclause>[^'";]*?)\s+from\s*['"](?P<ispec>[^'"]+)['"]
    |\bexport\s+(?:type\s+)?(?P<eclause>\{[^}]*\}|\*)\s+from\s*['"](?P<espec>[^'"]+)['"]
    |\bimport\s*['"](?P<sspec>[^'"]+)['"]
    |\b(?:require|import)\s*\(\s*['"](?P<dspec>[^'"]+)['"]\s*\)""")
_EXTS = (".d.ts", ".ts", ".tsx", ".mts", ".cts", ".js", ".mjs", ".cjs", ".jsx")


def _strip_ext(key):
    for ext in _EXTS:
        if key.endswith(ext):
            return key[: -len(ext)]
    return key


def _resolve(spec, base: Path, root: Path, packages):
    """An import specifier to its candidate module keys: relative specifiers
    resolve against the importer's directory; a bare specifier resolves only
    when it names a known package — its entry file or the subpath it names.
    Unresolvable specifiers produce no key (no evidence either way)."""
    if spec.startswith("."):
        return {_strip_ext(os.path.normpath(str(base / spec)))}
    segments = spec.split("/")
    if spec.startswith("@"):
        if len(segments) < 2:
            return set()
        name, sub = "/".join(segments[:2]), "/".join(segments[2:])
    else:
        name, sub = segments[0], "/".join(segments[1:])
    directory = packages.get(name)
    if directory is None:
        return set()
    if sub:
        return {_strip_ext(os.path.normpath(f"{directory}/{sub}"))}
    candidates = set()
    manifest = _package_json(root / directory / "package.json")
    for entry in ("main", "module", "source"):
        value = manifest.get(entry)
        if isinstance(value, str) and value:
            candidates.add(_strip_ext(os.path.normpath(
                f"{directory}/{value}" if directory else value)))
    candidates |= {f"{directory}/index" if directory else "index",
                   f"{directory}/src/index" if directory else "src/index"}
    return candidates


def _names(clause):
    """Imported/exported source names, or None for 'anything in this module'."""
    clause = clause.strip()
    if clause == "*":
        return None, None   # export * — re-exports everything
    named = re.search(r"\{([^}]*)\}", clause)
    if named:
        names = set()
        for part in named.group(1).split(","):
            part = part.strip()
            if part:
                names.add(part.split(" as ")[0].strip())
        return names, None
    ns = re.match(r"\*\s+as\s+(\w+)", clause)
    if ns:
        return set(), ns.group(1)
    return None, None   # a default import may name any export — can't tell, so don't warn


def _references(text):
    """(specifier, reexport?, names, ns alias) per import/export/require in `text`."""
    found = []
    for m in _REFERENCE.finditer(text):
        if m.group("ispec") is not None:
            reexport, spec = False, m.group("ispec")
            names, ns = _names(m.group("iclause"))
        elif m.group("espec") is not None:
            reexport, spec = True, m.group("espec")
            names, ns = _names(m.group("eclause"))
        else:
            reexport, spec, names, ns = False, m.group("sspec") or m.group("dspec"), None, None
        found.append((spec, reexport, names, ns))
    return found


def differential(checkout: Path, package_rel: str, work: Path, ws, extraction, cases=None, timeout=300, detail=None,
                 literals=None):
    """Compare the translated functions with Node on generated inputs.

    Returns (disagreements, notes, infra): notes are informational, infra is a
    reason the comparison itself could not run (Node crash, OOM, timeout, or
    missing replay results) — an infrastructure failure, never a disagreement.
    Only code that passed the translator's checks runs here, and only in the
    sandbox: it is the candidate's code, so this finds translator bugs and
    defends against nothing else.

    With a dict as `detail`, it also says which functions were involved:
    `detail["differ"]` lists the functions with a disagreement and
    `detail["skipped"]` maps a function that wasn't compared to the reason."""
    if detail is None:
        detail = {}
    detail.update(differ=[], skipped={})
    checkout = getattr(extraction, "checkout", None) or checkout  # the copy with packages mounted
    out = work / "differential"
    out.mkdir()
    # The model of an assumed call has no body to run, so nothing can be compared.
    signatures = {t: s for t, s in extraction.signatures.items() if not extraction.assumed.get(t)}
    skipped = [f"not compared with Node: {t} relies on an assumed outside call"
               for t in extraction.signatures if extraction.assumed.get(t)]
    for t in extraction.signatures:
        if extraction.assumed.get(t):
            detail["skipped"][t] = "it relies on an assumed outside call"
    if not signatures:
        return [], skipped, None
    if cases is None:  # each case takes about 8 ms to replay
        cases = max(25, min(200, MAX_CASES // max(len(signatures), 1)))
    config = out / "config.json"
    config.write_text(json.dumps({
        "root": str(checkout / package_rel), "out": str(out), "module": extraction.module, "cases": cases,
        "signatures": signatures, "files": extraction.files,
        "imports": extraction.imports, "effects": extraction.effect_list or [],
        "literals": literals or {}}))
    program = support_dir() / "differential.mjs"
    node = sandbox.run(["node", str(program), str(config)], readable=[checkout, program.parent],
                       binds=getattr(extraction, "binds", ()), writable=[out], cwd=out, timeout=60)
    if node.status != 0 or node.timed_out:
        detail["differ"] = sorted(signatures)
        return [], skipped, _node_failure(node)
    left_out = json.loads(node.output.splitlines()[-1])["skipped"]
    for item in left_out:
        function, _, why = item.partition(": ")
        detail["skipped"][function] = why
    notes = skipped + [f"not compared with Node: {item}" for item in left_out]
    replay = sandbox.run(["lake", "env", "lean", str(out / "Differential.lean")], readable=[ws.root, out],
                         writable=[ws.root / ".lake"], cwd=ws.root, timeout=timeout)
    if replay.timed_out:
        detail["differ"] = sorted(signatures)
        return [], notes, f"replaying the comparison did not finish in {timeout} seconds"
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
    detail["differ"] = sorted({label.split(" ", 1)[0] for label in disagreements})
    if sum(counts.values()) != expected:
        # Every case must report. One that doesn't compile compares nothing.
        detail["differ"] = sorted(signatures)
        return [], notes, (f"only {sum(counts.values())} of {expected} comparisons ran: "
                           + _lean_errors(replay.output))
    notes.append(f"compared with Node: {counts['agree']} results agree, "
                 f"{counts['failed']} inputs left the safe-integer model")
    return disagreements, notes, None
