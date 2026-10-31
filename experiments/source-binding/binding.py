#!/usr/bin/env python3
"""Experimental, deliberately narrow source-to-challenge adapter.

Run only in a disposable environment: Lake's sandbox is disabled by this probe.
Its verdict is diagnostic and is not an authorization to enforce a merge gate.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
TOKEN = re.compile(r"\s+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|:=|[():+*]")
HEADER = ["def", "target", "(", "x", ":", "Nat", ")", ":", "Nat", ":="]


def sha(data):
    return hashlib.sha256(data).hexdigest()


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
            term(depth + 1)
            if position >= len(words) or words[position] != ")":
                raise ValueError("unclosed parenthesis")
            position += 1
        elif word != "x" and not (word.isascii() and word.isdecimal() and len(word) <= 4):
            raise ValueError(f"unsupported expression token {word!r}")

    def product(depth):
        nonlocal position
        atom(depth)
        while position < len(words) and words[position] == "*":
            position += 1
            atom(depth)

    def term(depth):
        nonlocal position
        product(depth)
        while position < len(words) and words[position] == "+":
            position += 1
            product(depth)

    term(0)
    if position != len(words):
        raise ValueError(f"unexpected token {words[position]!r}")
    return " ".join(words)


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


def run(candidate_path, contract_path, lake, lean):
    candidate = candidate_path.read_bytes()
    contract = contract_path.read_bytes()
    body = candidate_body(candidate.decode("utf-8"))
    rhs = load_contract(contract)
    version = subprocess.run([lean, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    if not version.startswith("Lean (version 4.35.0,") or LEAN_COMMIT not in version:
        raise ValueError(f"wrong Lean toolchain: {version}")
    if Path(lean).resolve().parent != Path(lake).resolve().parent:
        raise ValueError("Lean and Lake must be in the same toolchain directory")

    statement = f"theorem contract (x : Nat) : target x = {rhs} := by "
    config = {
        "challenge_module": "Challenge", "solution_module": "Solution",
        "theorem_names": ["contract"], "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "external_kernels": {"nanoda": ["nanoda_bin"]},
    }
    with tempfile.TemporaryDirectory(prefix="proofci-adapter-") as tmp:
        root = Path(tmp)
        (root / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage spike\nlean_lib Candidate\nlean_lib Challenge\nlean_lib Solution\n")
        (root / "Candidate.lean").write_bytes(candidate)
        (root / "Challenge.lean").write_text("import Candidate\n" + statement + "sorry\n")
        (root / "Solution.lean").write_text("import Candidate\nimport Std.Tactic\n" + statement + "simp [target] <;> omega\n")
        (root / "comparator.json").write_text(json.dumps(config))
        env = dict(os.environ)
        # Use the same directory for lake, Lean, and external checkers.
        env["PATH"] = str(Path(lean).resolve().parent) + os.pathsep + env.get("PATH", "")
        init = subprocess.run([lake, "build", "--allow-empty"], cwd=root, env=env, capture_output=True, text=True, timeout=120)
        if init.returncode:
            raise RuntimeError("Lake setup failed: " + init.stdout + init.stderr)
        lake_version = subprocess.run([lake, "env", "lean", "--version"], cwd=root, env=env,
                                      check=True, capture_output=True, text=True, timeout=120).stdout.strip()
        if lake_version != version:
            raise ValueError(f"Lake resolved a different Lean version: {lake_version}")
        result = subprocess.run([lake, "comparator", "--inadvisably-no-sandbox"], cwd=root, env=env, capture_output=True, text=True, timeout=120)
        output = (result.stdout + result.stderr).replace(str(root), "<workspace>")
    return {
        "candidate_sha256": sha(candidate), "contract_sha256": sha(contract),
        "admitted_body": body,
        "statement_sha256": sha(statement.encode()),
        "supplied_lean_version": version, "lake_env_lean_version": lake_version,
        "comparator_exit": result.returncode,
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
    args = parser.parse_args()
    try:
        report = run(args.candidate, args.contract, args.lake, args.lean)
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        report = {"decision": "unproven", "error": str(error)}
    print(json.dumps(report, indent=2))
    # No experiment result is an authoritative verification result.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
