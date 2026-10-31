#!/usr/bin/env python3
"""Experimental, deliberately narrow source-to-challenge adapter.

Its verdict is diagnostic and is not an authorization to enforce a merge gate.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import threading

from toolchain import tree_digest


LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
LINUX_ARM64_TOOLCHAIN = "ad4f844f85ce90b22e30efee3a1028ea99d15724fe72de7dc4e16ceda971da00"
BWRAP_SHA256 = "b3b829e18a7d43ee589dc37e351cb9480ff7301b493d8227b8c754294638b976"
_verified_toolchains = {}
_toolchain_lock = threading.Lock()
TOKEN = re.compile(r"\s+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|:=|[():+*]")
HEADER = ["def", "target", "(", "x", ":", "Nat", ")", ":", "Nat", ":="]
EXPORT_SHAPES = {
    frozenset(("in", key)) for key in ("str", "num")
} | {
    frozenset(("il", key)) for key in ("succ", "max", "param")
} | {
    frozenset(("ie", key)) for key in
    ("app", "bvar", "const", "forallE", "lam", "letE", "natVal", "proj", "sort", "strVal")
} | {frozenset((key,)) for key in ("def", "thm", "axiom", "opaque", "inductive")}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_input(path, limit):
    with path.open("rb") as source:
        data = source.read(limit + 1)
    if len(data) > limit:
        raise ValueError(f"input exceeds {limit} bytes")
    return data


def check_export(export, challenge):
    lines = export.splitlines()
    if not lines:
        raise ValueError("Lean produced an empty export")
    records = [json.loads(line) for line in lines]
    if set(records[0]) != {"meta"}:
        raise ValueError("malformed Lean export metadata")
    meta = records[0].get("meta", {})
    if meta.get("lean", {}).get("githash") != LEAN_COMMIT or meta.get("format", {}).get("version") != "3.1.0":
        raise ValueError("export was produced by a different Lean version")
    names = {0: ""}
    declarations = set()
    try:
        for record in records[1:]:
            if frozenset(record) not in EXPORT_SHAPES:
                raise ValueError("unsupported Lean export record")
            if "in" in record:
                item = record.get("str") or record["num"]
                part = str(item.get("str", item.get("i")))
                parent = names[item["pre"]]
                names[record["in"]] = f"{parent}.{part}" if parent else part
            for kind in ("def", "thm", "axiom", "opaque"):
                if kind in record:
                    declarations.add(f"{kind} {names[record[kind]['name']]}")
            if "inductive" in record:
                for kind in ("ctors", "recs", "types"):
                    for entry in record["inductive"][kind]:
                        declarations.add(f"{kind} {names[entry['name']]}")
    except (KeyError, TypeError) as error:
        raise ValueError(f"malformed Lean export: {error}") from error
    required = {"def target"}
    if challenge:
        required |= {"thm contract", "axiom sorryAx"}
    allowed = set(json.loads(Path(__file__).with_name("core-dependencies.json").read_bytes())) | required
    if not required.issubset(declarations) or declarations - allowed:
        raise ValueError(f"unexpected export dependencies: {sorted(declarations - allowed)}; missing: {sorted(required - declarations)}")
    return sorted(declarations)


def tokens(source):
    if len(source) > 4096:
        raise ValueError("source is too long")
    result = []
    offset = 0
    while offset < len(source):
        match = TOKEN.match(source, offset)
        if not match:
            raise ValueError(f"unsupported character at offset {offset}")
        word = match.group()
        if not word.isspace():
            result.append(word)
        offset = match.end()
    if len(result) > 256:
        raise ValueError("too many tokens")
    return result


def expression(words):
    """Parse the entire expression; no Lean commands or name resolution escape."""
    position = 0

    def atom(depth):
        nonlocal position
        if depth > 32 or position >= len(words):
            raise ValueError("invalid expression")
        word = words[position]
        position += 1
        if word == "(":
            value = term(depth + 1)
            if position >= len(words) or words[position] != ")":
                raise ValueError("unclosed parenthesis")
            position += 1
            return value
        elif word != "x" and not (word.isascii() and word.isdecimal() and len(word) <= 4):
            raise ValueError(f"unsupported expression token {word!r}")
        return word

    def product(depth):
        nonlocal position
        result = atom(depth)
        while position < len(words) and words[position] == "*":
            position += 1
            result = f"(Nat.mul {result} {atom(depth)})"
        return result

    def term(depth):
        nonlocal position
        result = product(depth)
        while position < len(words) and words[position] == "+":
            position += 1
            result = f"(Nat.add {result} {product(depth)})"
        return result

    canonical = term(0)
    if position != len(words):
        raise ValueError(f"unexpected token {words[position]!r}")
    return " ".join(words), canonical


def candidate_body(source):
    words = tokens(source)
    if words[:len(HEADER)] != HEADER:
        raise ValueError("candidate must be exactly one target definition")
    return expression(words[len(HEADER):])


def load_contract(data):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate contract field {key!r}")
            result[key] = value
        return result

    contract = json.loads(data, object_pairs_hook=unique_object)
    if not isinstance(contract, dict) or set(contract) != {"rhs"} or not isinstance(contract["rhs"], str):
        raise ValueError('contract must contain only a string field "rhs"')
    return expression(tokens(contract["rhs"]))


def verify_toolchain(lean, lake):
    if platform.system() != "Linux" or platform.machine() != "aarch64":
        raise ValueError("the pinned validator supports Linux arm64 only")
    lean_path = Path(lean).resolve(strict=True)
    lake_path = Path(lake).resolve(strict=True)
    root = lean_path.parent.parent
    if lean_path != root / "bin" / "lean" or lake_path != root / "bin" / "lake":
        raise ValueError("Lean and Lake must be the pinned toolchain binaries")
    if not os.statvfs(root).f_flag & os.ST_RDONLY:
        raise ValueError("the pinned toolchain must be mounted read-only")
    with _toolchain_lock:
        if root not in _verified_toolchains:
            actual = tree_digest(root)
            if actual != LINUX_ARM64_TOOLCHAIN:
                raise ValueError("Lean distribution digest does not match the pinned toolchain")
            _verified_toolchains[root] = actual
    bwrap = shutil.which("bwrap", path="/usr/bin:/bin")
    if not bwrap or sha(Path(bwrap).read_bytes()) != BWRAP_SHA256:
        raise ValueError("bubblewrap binary does not match the pinned validator")
    return _verified_toolchains[root]


def run(candidate_path, contract_path, lake, lean, unsafe_no_sandbox=False, _test_solution=None):
    candidate = read_input(candidate_path, 16384)
    contract = read_input(contract_path, 16384)
    body, canonical_body = candidate_body(candidate.decode("utf-8"))
    rhs, _ = load_contract(contract)
    distribution_sha = None if unsafe_no_sandbox else verify_toolchain(lean, lake)
    env = {"PATH": str(Path(lean).resolve().parent) + os.pathsep + "/usr/bin:/bin", "HOME": "/tmp", "LC_ALL": "C.UTF-8"}
    version = subprocess.run([lean, "--version"], env=env, check=True, capture_output=True, text=True).stdout.strip()
    if not version.startswith("Lean (version 4.35.0,") or LEAN_COMMIT not in version:
        raise ValueError(f"wrong Lean toolchain: {version}")
    if Path(lean).resolve().parent != Path(lake).resolve().parent:
        raise ValueError("Lean and Lake must be in the same toolchain directory")

    statement = f"theorem contract (x : Nat) : target x = {rhs} := by "
    config = {
        "challenge_module": "Challenge", "solution_module": "Solution",
        "theorem_names": ["contract", "definition_identity"], "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "external_kernels": {"nanoda": ["nanoda_bin"]},
    }
    with tempfile.TemporaryDirectory(prefix="proofci-adapter-") as tmp:
        root = Path(tmp)
        (root / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage spike\nlean_lib Candidate\nlean_lib CandidateCheck\nlean_lib Challenge\nlean_lib Solution\n")
        (root / "Candidate.lean").write_bytes(candidate)
        identity = f"theorem definition_identity : target = (fun (x : Nat) => {canonical_body}) := by rfl\n"
        (root / "CandidateCheck.lean").write_text("import Candidate\n" + identity)
        challenge = "import CandidateCheck\n" + statement + "sorry\n"
        (root / "Challenge.lean").write_text(challenge)
        solution = "import CandidateCheck\nimport Std.Tactic\n" + statement + "simp [target] <;> omega\n"
        if _test_solution is not None:
            solution = _test_solution
        (root / "Solution.lean").write_text(solution)
        config_json = json.dumps(config)
        (root / "comparator.json").write_text(config_json)
        init = subprocess.run([lake, "update"], cwd=root, env=env, capture_output=True, text=True, timeout=120)
        if init.returncode:
            raise RuntimeError("Lake setup failed: " + init.stdout + init.stderr)
        lake_version = subprocess.run([lake, "env", "lean", "--version"], cwd=root, env=env,
                                      check=True, capture_output=True, text=True, timeout=120).stdout.strip()
        if lake_version != version:
            raise ValueError(f"Lake resolved a different Lean version: {lake_version}")
        subprocess.run([lake, "build", "Candidate"], cwd=root, env=env, check=True,
                       capture_output=True, text=True, timeout=120)
        export = subprocess.run([lake, "env", "leanexport", "Candidate", "--", "target"],
                                cwd=root, env=env, check=True, capture_output=True, timeout=120).stdout
        definition_dependencies = check_export(export, False)
        subprocess.run([lake, "build", "Challenge"], cwd=root, env=env, check=True,
                       capture_output=True, text=True, timeout=120)
        challenge_export = subprocess.run(
            [lake, "env", "leanexport", "Challenge", "--", "contract"],
            cwd=root, env=env, check=True, capture_output=True, timeout=120).stdout
        challenge_dependencies = check_export(challenge_export, True)
        command = [lake, "comparator"]
        if unsafe_no_sandbox:
            command.append("--inadvisably-no-sandbox")
        result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True, timeout=120)
        output = (result.stdout + result.stderr).replace(str(root), "<workspace>")
    return {
        "candidate_sha256": sha(candidate), "contract_sha256": sha(contract),
        "admitted_body": body, "canonical_body": canonical_body,
        "definition_identity_source_sha256": sha(identity.encode()),
        "definition_and_dependency_export_sha256": sha(export),
        "definition_and_dependency_export_bytes": len(export),
        "challenge_and_dependency_export_sha256": sha(challenge_export),
        "challenge_and_dependency_export_bytes": len(challenge_export),
        "definition_dependencies": definition_dependencies,
        "challenge_dependencies": challenge_dependencies,
        "dependency_policy_sha256": sha(Path(__file__).with_name("core-dependencies.json").read_bytes()),
        "statement_sha256": sha(statement.encode()),
        "challenge_source_sha256": sha(challenge.encode()),
        "solution_source_sha256": sha(solution.encode()),
        "comparator_config_sha256": sha(config_json.encode()),
        "adapter_source_sha256": sha(Path(__file__).read_bytes()),
        "supplied_lean_version": version, "lake_env_lean_version": lake_version,
        "comparator_exit": result.returncode,
        "lake_sandbox_disabled": unsafe_no_sandbox,
        "lean_distribution_sha256": distribution_sha,
        "supplied_lean_sha256": sha(Path(lean).read_bytes()),
        "supplied_lake_sha256": sha(Path(lake).read_bytes()),
        "supplied_nanoda_sha256": sha((Path(lean).resolve().parent / "nanoda_bin").read_bytes()),
        "comparator_output": output,
        "decision": "unproven: experimental adapter; independent trust and full corpus not established",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("contract", type=Path)
    parser.add_argument("--lean", required=True, help="absolute path to pinned lean")
    parser.add_argument("--lake", required=True, help="absolute path to matching lake")
    parser.add_argument("--unsafe-no-sandbox", action="store_true", help="disable Lake sandbox for local experiments only")
    args = parser.parse_args()
    try:
        report = run(args.candidate, args.contract, args.lake, args.lean, args.unsafe_no_sandbox)
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        report = {"decision": "unproven", "error": str(error)}
    print(json.dumps(report, indent=2))
    # No experiment result is an authoritative verification result.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
