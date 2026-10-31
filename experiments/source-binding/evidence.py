"""Validate submitted proof evidence against the trusted source-binding policy.

The bundle is intentionally data-only. Candidate and contract bytes are supplied
by the trusted caller, while all challenge construction, toolchain selection,
checker commands, and acceptance policy live in this module.
"""

import base64
import binascii
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import tempfile
import threading
import time

from dataclasses import dataclass

import binding


BUNDLE_VERSION = 1
LEAN_COMMIT = binding.LEAN_COMMIT
MAX_SOLUTION_BYTES = 64 * 1024
MAX_EXPORT_BYTES = 8 * 1024 * 1024
PERMITTED_AXIOMS = binding.PERMITTED_AXIOMS
TRUSTED_CHECKER = ("comparator",)
TRUSTED_COMPARATOR_CONFIG = binding.COMPARATOR_CONFIG
MANIFEST_FIELDS = frozenset({
    "version", "candidate_sha256", "contract_sha256", "solution_sha256",
    "challenge_export_sha256", "solution_export_sha256", "claimed_decision",
})
FILES = {
    "manifest": "manifest.json",
    "solution": "solution.lean",
    "challenge_export": "challenge.ndjson",
    "solution_export": "solution.ndjson",
}
CHALLENGE_SCRIPT = "proofci-challenge.sh"
SOLUTION_SCRIPT = "proofci-solution.sh"
CHECKER_SCRIPT = "proofci-check.sh"
CHALLENGE_MARKER = b"PROOFCI_CHALLENGE_BEGIN\n"
SOLUTION_MARKER = b"PROOFCI_SOLUTION_BEGIN\n"
CHECKER_READY_MARKER = "PROOFCI_CHECKER_READY\n"
MAX_PROCESS_OUTPUT = 16 * 1024 * 1024
FORBIDDEN_SOLUTION = re.compile(
    r"\b(?:sorry|axiom|unsafe|native_decide|implemented_by|run_tac|elab|macro)\b"
)


class EvidenceError(ValueError):
    """The submitted bundle cannot be trusted as evidence."""


class ValidationUnavailable(RuntimeError):
    """The pinned validator is not available in this environment."""


class ValidationTimeout(ValidationUnavailable):
    """The fixed validator exceeded its time budget."""


class BuildFailure(RuntimeError):
    """A fixed validation command failed before the checker decision."""


class ProofFailure(RuntimeError):
    """Lean could not construct the submitted proof."""


class CheckerDisagreement(RuntimeError):
    """The independent checker results cannot be reconciled."""


class ContradictoryEvidence(RuntimeError):
    """The checker claims acceptance while its status or output says otherwise."""


@dataclass(frozen=True)
class EvidenceBundle:
    candidate: bytes
    contract: bytes
    solution: bytes
    challenge_export: bytes
    solution_export: bytes
    candidate_sha256: str
    contract_sha256: str
    claimed_decision: str
    witness: int | None
    permitted_axioms: frozenset[str] = PERMITTED_AXIOMS


def sha(data):
    return hashlib.sha256(data).hexdigest()


def _read(path, limit, label):
    try:
        with path.open("rb") as source:
            data = source.read(limit + 1)
    except OSError as error:
        raise EvidenceError(f"cannot read {label}: {error}") from error
    if len(data) > limit:
        raise EvidenceError(f"{label} exceeds {limit} bytes")
    return data


def _json(data, label):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise EvidenceError(f"duplicate {label} field {key!r}")
            result[key] = value
        return result

    try:
        return json.loads(data, object_pairs_hook=unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as error:
        raise EvidenceError(f"malformed {label}") from error


def _manifest(bundle):
    manifest = _json(_read(bundle / FILES["manifest"], 16 * 1024, "manifest"), "manifest")
    if not isinstance(manifest, dict) or set(manifest) not in (MANIFEST_FIELDS, MANIFEST_FIELDS | {"witness"}):
        raise EvidenceError("manifest fields do not match the trusted bundle format")
    if manifest["version"] != BUNDLE_VERSION:
        raise EvidenceError("unsupported evidence bundle version")
    if manifest["claimed_decision"] not in ("verified", "violated"):
        raise EvidenceError("unsupported evidence claim")
    if "witness" in manifest and (manifest["claimed_decision"] != "violated" or type(manifest["witness"]) is not int or not 0 <= manifest["witness"] <= 1000000):
        raise EvidenceError("unsupported witness")
    for field in MANIFEST_FIELDS - {"version", "claimed_decision"}:
        if (not isinstance(manifest[field], str)
                or not re.fullmatch(r"[0-9a-f]{64}", manifest[field])):
            raise EvidenceError(f"manifest field {field} is not a SHA-256 digest")
    return manifest


def load_bundle(bundle_path, candidate_path, contract_path):
    """Load and structurally validate a bundle without invoking Lean."""
    bundle = Path(bundle_path).resolve(strict=True)
    candidate_path = Path(candidate_path).resolve(strict=True)
    contract_path = Path(contract_path).resolve(strict=True)
    if not bundle.is_dir():
        raise EvidenceError("evidence must be an unpacked directory")
    expected_files = set(FILES.values())
    actual_files = {entry.name for entry in bundle.iterdir()}
    if actual_files != expected_files:
        raise EvidenceError("bundle contains unexpected or missing files")
    for name in expected_files:
        entry = bundle / name
        if entry.is_symlink() or not entry.is_file():
            raise EvidenceError(f"bundle member {name} is not a regular file")

    manifest = _manifest(bundle)
    candidate = _read(candidate_path, 16 * 1024, "candidate")
    contract = _read(contract_path, 16 * 1024, "contract")
    solution = _read(bundle / FILES["solution"], MAX_SOLUTION_BYTES, "solution")
    challenge_export = _read(bundle / FILES["challenge_export"], MAX_EXPORT_BYTES,
                             "challenge export")
    solution_export = _read(bundle / FILES["solution_export"], MAX_EXPORT_BYTES, "solution export")
    if (sha(candidate) != manifest["candidate_sha256"]
            or sha(contract) != manifest["contract_sha256"]):
        raise EvidenceError("bundle is bound to different candidate or contract bytes")
    if sha(solution) != manifest["solution_sha256"]:
        raise EvidenceError("solution digest does not match the manifest")
    if sha(challenge_export) != manifest["challenge_export_sha256"]:
        raise EvidenceError("challenge export digest does not match the manifest")
    if sha(solution_export) != manifest["solution_export_sha256"]:
        raise EvidenceError("solution export digest does not match the manifest")

    try:
        binding.candidate_body(candidate.decode("utf-8"))
        binding.load_contract(contract)
        solution.decode("utf-8")
    except (UnicodeDecodeError, ValueError) as error:
        raise EvidenceError(f"source admission failed: {error}") from error
    if FORBIDDEN_SOLUTION.search(solution.decode("utf-8")):
        raise EvidenceError("solution contains a forbidden proof or code escape")

    required = {"def target", "thm contract"}
    try:
        binding.check_export(challenge_export, True, required=required,
                             permitted_axioms=PERMITTED_AXIOMS)
        binding.check_export(solution_export, False, required=required,
                             permitted_axioms=PERMITTED_AXIOMS)
    except ValueError as error:
        raise EvidenceError(f"export policy rejected evidence: {error}") from error
    return EvidenceBundle(candidate, contract, solution, challenge_export, solution_export,
                          manifest["candidate_sha256"], manifest["contract_sha256"],
                          manifest["claimed_decision"], manifest.get("witness"))


def _sources(bundle):
    _, _, identity, statement, challenge = binding.build_sources(bundle.candidate, bundle.contract)
    if bundle.claimed_decision == "violated":
        (rhs, _), precondition = binding.load_contract(bundle.contract)
        property_body = f"target x = {rhs}"
        if precondition:
            property_body = f"({precondition}) → {property_body}"
        proposition = f"¬ (∀ x : Nat, {property_body})"
        if bundle.witness is not None:
            failure = f"¬ (target x = {rhs})"
            if precondition:
                failure = f"({precondition}) ∧ {failure}"
            proposition += f" ∧ (let x : Nat := {bundle.witness}; {failure})"
        statement = f"theorem contract : {proposition} := by "
        challenge = "import CandidateCheck\n" + statement + "sorry\n"
    solution = bundle.solution.decode("utf-8")
    return identity, statement, challenge, solution


def _write_workspace(root, bundle):
    # Each sandbox invocation gets a fresh private build directory.  The
    # validator never consumes build artifacts produced by an earlier command.
    root.joinpath(".lake").mkdir()
    root.joinpath("lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\npackage proofci\n"
        "lean_lib Candidate\nlean_lib CandidateCheck\nlean_lib Challenge\nlean_lib Solution\n"
    )
    root.joinpath("Candidate.lean").write_bytes(bundle.candidate)
    identity, _, challenge, solution = _sources(bundle)
    root.joinpath("CandidateCheck.lean").write_text("import Candidate\n" + identity)
    root.joinpath("Challenge.lean").write_text(challenge)
    root.joinpath("Solution.lean").write_text(solution)
    root.joinpath("comparator.json").write_text(
        json.dumps(TRUSTED_COMPARATOR_CONFIG, sort_keys=True, separators=(",", ":"))
    )
    root.joinpath(CHALLENGE_SCRIPT).write_text(
        "#!/bin/sh\n"
        "set -eu\n"
        "/lean/bin/lake build Candidate Challenge >/dev/null\n"
        "/lean/bin/lake env leanexport Challenge -- contract > /tmp/proofci-challenge.ndjson\n"
        "printf '%s\\n' 'PROOFCI_CHALLENGE_BEGIN'\n"
        "/usr/bin/base64 -w0 /tmp/proofci-challenge.ndjson\n"
    )
    root.joinpath(SOLUTION_SCRIPT).write_text(
        "#!/bin/sh\n"
        "set -eu\n"
        "if ! /lean/bin/lake build Candidate CandidateCheck Solution > /tmp/proofci-build.log 2>&1; then\n"
        "  /bin/cat /tmp/proofci-build.log >&2; exit 1\n"
        "fi\n"
        "/lean/bin/lake env leanexport Solution -- contract > /tmp/proofci-solution.ndjson\n"
        "printf '%s\\n' 'PROOFCI_SOLUTION_BEGIN'\n"
        "/usr/bin/base64 -w0 /tmp/proofci-solution.ndjson\n"
    )
    root.joinpath(CHECKER_SCRIPT).write_text(
        "#!/bin/sh\n"
        "set -eu\n"
        "printf '%s\\n' 'PROOFCI_CHECKER_READY'\n"
        "exec /lean/bin/lake comparator\n"
    )


def _sandbox_prefix(toolchain, workspace, policy_path, read_only_sources,
                    entrypoint=("/lean/bin/lake",)):
    if platform.system() != "Linux" or platform.machine() != "aarch64":
        raise ValidationUnavailable("the pinned validator supports Linux arm64 only")
    bwrap = shutil.which("bwrap", path="/usr/bin:/bin")
    if not bwrap:
        raise ValidationUnavailable("pinned bubblewrap is unavailable")
    runtime_mounts = [
        "--ro-bind", "/usr", "/usr",
        "--ro-bind", "/bin", "/bin",
        "--ro-bind", "/etc", "/etc",
        "--ro-bind", "/lib", "/lib",
    ]
    if Path("/lib64").exists():
        runtime_mounts.extend(("--ro-bind", "/lib64", "/lib64"))
    source_mounts = [
        "--ro-bind", str(workspace / CHALLENGE_SCRIPT), f"/workspace/{CHALLENGE_SCRIPT}",
        "--ro-bind", str(workspace / SOLUTION_SCRIPT), f"/workspace/{SOLUTION_SCRIPT}",
        "--ro-bind", str(workspace / CHECKER_SCRIPT), f"/workspace/{CHECKER_SCRIPT}",
    ]
    if read_only_sources:
        for name in (
                "lakefile.lean", "Candidate.lean", "CandidateCheck.lean",
                "Challenge.lean", "Solution.lean"):
            source_mounts.extend((
                "--ro-bind", str(workspace / name), f"/workspace/{name}"
            ))
    return [
        bwrap, "--die-with-parent", "--unshare-all", "--unshare-net",
        "--ro-bind", str(toolchain), "/lean",
        *runtime_mounts,
        "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
        "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run", "--dir", "/run/user", "--tmpfs", "/var",
        "--bind", str(workspace), "/workspace", "--chdir", "/workspace",
        "--tmpfs", "/workspace/.lake",
        "--ro-bind", str(policy_path), "/workspace/comparator.json",
        *source_mounts,
        "--setenv", "HOME", "/tmp", "--setenv", "LC_ALL", "C.UTF-8",
        "--setenv", "PATH", "/lean/bin:/usr/bin:/bin", "--",
        *entrypoint,
    ]


def _decode(data):
    return data.decode("utf-8", errors="replace")


def _run(toolchain, workspace, policy_path, args, timeout=120, allow_failure=False,
         combined=False, read_only_sources=False, entrypoint=("/lean/bin/lake",)):
    command = _sandbox_prefix(
        toolchain, workspace, policy_path, read_only_sources, entrypoint=entrypoint
    ) + list(args)
    env = {"PATH": "/usr/bin:/bin", "HOME": "/tmp", "LC_ALL": "C.UTF-8"}
    try:
        process = subprocess.Popen(
            command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=True
        )
    except OSError as error:
        raise ValidationUnavailable(f"validator command unavailable: {error}") from error
    captured = {"total": 0}
    captured_lock = threading.Lock()
    overflow = threading.Event()
    streams = {"stdout": bytearray(), "stderr": bytearray()}

    def kill_group():
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def drain(name, stream):
        with stream:
            while True:
                chunk = stream.read(64 * 1024)
                if not chunk:
                    return
                with captured_lock:
                    captured["total"] += len(chunk)
                    exceeded = captured["total"] > MAX_PROCESS_OUTPUT
                if exceeded:
                    overflow.set()
                    kill_group()
                    return
                streams[name].extend(chunk)

    readers = [
        threading.Thread(target=drain, args=(name, stream), daemon=True)
        for name, stream in (("stdout", process.stdout), ("stderr", process.stderr))
    ]
    for reader in readers:
        reader.start()
    deadline = time.monotonic() + timeout
    try:
        process.wait(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        kill_group()
        process.wait()
        for reader in readers:
            reader.join(1)
        raise ValidationTimeout(f"validator command timed out: {error}") from error
    except BaseException:
        kill_group()
        process.wait()
        for reader in readers:
            reader.join(1)
        raise
    for reader in readers:
        reader.join(max(0, deadline - time.monotonic()))
    if any(reader.is_alive() for reader in readers):
        kill_group()
        for reader in readers:
            reader.join(1)
        raise ValidationTimeout("validator output did not close before timeout")
    if overflow.is_set():
        raise BuildFailure(f"{' '.join(args)} exceeded output limit")
    stdout = bytes(streams["stdout"])
    stderr = bytes(streams["stderr"])
    if process.returncode and not allow_failure:
        output = _decode(stdout + stderr)[-64 * 1024:]
        raise BuildFailure(f"{' '.join(args)} failed: {output}")
    if not combined:
        # Exports are compared byte-for-byte.  Do not decode untrusted output
        # before that comparison, and do not let malformed bytes crash the API.
        return process.returncode, stdout
    output = _decode(stdout + stderr)
    return process.returncode, output[-64 * 1024:]


def _run_solution(toolchain, workspace, policy_path, **options):
    try:
        return _run(toolchain, workspace, policy_path, (),
                    entrypoint=("/bin/sh", f"/workspace/{SOLUTION_SCRIPT}"), **options)
    except BuildFailure as error:
        if "error: Solution.lean:" in str(error):
            raise ProofFailure(str(error)) from error
        raise


def _extract_export(output, marker):
    """Decode one fixed script's byte-preserving export channel."""
    try:
        prefix, encoded = output.split(marker, 1)
        if prefix:
            raise ValueError("unexpected replay output before marker")
        return base64.b64decode(b"".join(encoded.split()), validate=True)
    except (ValueError, TypeError, binascii.Error) as error:
        raise BuildFailure("fixed replay did not produce a valid export") from error


def _verify_toolchain(toolchain):
    try:
        toolchain = Path(toolchain).resolve(strict=True)
        lean = toolchain / "bin" / "lean"
        lake = toolchain / "bin" / "lake"
        binding.verify_toolchain(str(lean), str(lake))
    except (OSError, ValueError) as error:
        raise ValidationUnavailable(str(error)) from error
    return toolchain


def _invalid(reason, error):
    return {"decision": "unproven", "reason": reason, "detail": str(error)}


def classify_checker(status, output):
    if status not in (0, 1):
        raise BuildFailure(f"fixed checker exited with infrastructure status {status}")
    lean_accepts = "Lean default kernel accepts the solution" in output
    nanoda_accepts = "nanoda kernel accepts the solution" in output
    if lean_accepts != nanoda_accepts:
        raise CheckerDisagreement("external checker results disagree")
    if status != 0 and lean_accepts and nanoda_accepts:
        raise ContradictoryEvidence("checker output claims acceptance with a failing status")
    rejected = any(marker in output for marker in (
        "Lean default kernel rejects the solution",
        "Lean default kernel rejected the solution",
        "nanoda kernel rejects the solution",
        "nanoda kernel rejected the solution",
        "Your solution is not okay!",
    ))
    if rejected and lean_accepts and nanoda_accepts:
        raise ContradictoryEvidence("checker output contains both acceptance and rejection")
    if status == 1 and not rejected:
        raise BuildFailure("checker exited without a proof judgment")
    if status == 0 and lean_accepts and nanoda_accepts and "Your solution is okay!" in output:
        return "verified"
    if status == 0 or lean_accepts != nanoda_accepts:
        raise CheckerDisagreement("checker status and acceptance output disagree")
    return "unproven"


def validate_bundle(bundle_path, candidate_path, contract_path, toolchain=None):
    """Return the only authoritative decision for a submitted proof bundle."""
    try:
        bundle = load_bundle(bundle_path, candidate_path, contract_path)
    except (EvidenceError, OSError, ValueError, RecursionError) as error:
        return _invalid("invalid_evidence", error)
    if toolchain is None:
        return _invalid(
            "validation_unavailable",
            "no pinned toolchain was supplied by the trusted runner",
        )

    try:
        toolchain = _verify_toolchain(toolchain)
        with tempfile.TemporaryDirectory(prefix="proofci-policy-") as policy_dir:
            policy_path = Path(policy_dir) / "comparator.json"
            policy_path.write_text(json.dumps(TRUSTED_COMPARATOR_CONFIG, sort_keys=True,
                                              separators=(",", ":")))
            with tempfile.TemporaryDirectory(prefix="proofci-construction-") as construction_dir:
                construction = Path(construction_dir)
                _write_workspace(construction, bundle)
                _, challenge_output = _run(
                    toolchain, construction, policy_path, (),
                    entrypoint=("/bin/sh", f"/workspace/{CHALLENGE_SCRIPT}")
                )
                _extract_export(challenge_output, CHALLENGE_MARKER)
                _, solution_output = _run_solution(toolchain, construction, policy_path)
                _extract_export(solution_output, SOLUTION_MARKER)

            with tempfile.TemporaryDirectory(prefix="proofci-validation-") as validation_dir:
                validation = Path(validation_dir)
                _write_workspace(validation, bundle)
                run_options = {"read_only_sources": True}
                _, challenge_output = _run(
                    toolchain, validation, policy_path, (),
                    entrypoint=("/bin/sh", f"/workspace/{CHALLENGE_SCRIPT}"), **run_options
                )
                challenge_export = _extract_export(challenge_output, CHALLENGE_MARKER)
                _, solution_output = _run_solution(toolchain, validation, policy_path, **run_options)
                solution_export = _extract_export(solution_output, SOLUTION_MARKER)
                if challenge_export != bundle.challenge_export:
                    raise EvidenceError("fresh challenge export differs from submitted evidence")
                if solution_export != bundle.solution_export:
                    raise EvidenceError("fresh solution export differs from submitted evidence")
                checker_status, checker_output = _run(
                    toolchain, validation, policy_path, (),
                    entrypoint=("/bin/sh", f"/workspace/{CHECKER_SCRIPT}"),
                    allow_failure=True, combined=True, **run_options
                )
                if CHECKER_READY_MARKER not in checker_output:
                    raise BuildFailure("fixed checker did not reach its comparison stage")
                checker_output = checker_output.split(CHECKER_READY_MARKER, 1)[1]
    except EvidenceError as error:
        return _invalid("invalid_evidence", error)
    except CheckerDisagreement as error:
        return _invalid("checker_disagreement", error)
    except ContradictoryEvidence as error:
        return _invalid("contradictory_evidence", error)
    except ProofFailure as error:
        return _invalid("proof_failed", error)
    except BuildFailure as error:
        return _invalid("build_failure", error)
    except ValidationTimeout as error:
        return _invalid("timeout", error)
    except ValidationUnavailable as error:
        return _invalid("validation_unavailable", error)
    except OSError as error:
        return _invalid("validation_unavailable", error)

    try:
        decision = classify_checker(checker_status, checker_output)
    except CheckerDisagreement as error:
        return _invalid("checker_disagreement", error)
    except ContradictoryEvidence as error:
        return _invalid("contradictory_evidence", error)
    except BuildFailure as error:
        return _invalid("build_failure", error)
    if decision != "verified":
        return _invalid("unproven", "the fixed checker did not accept the proof")
    return {
        "decision": bundle.claimed_decision,
        "reason": "accepted by the reconstructed challenge and independent checkers",
        "statement_sha256": sha(_sources(bundle)[1].encode()),
        "candidate_sha256": bundle.candidate_sha256,
        "contract_sha256": bundle.contract_sha256,
        "permitted_axioms": sorted(PERMITTED_AXIOMS),
        "checker": list(TRUSTED_CHECKER),
        "policy": "fixed source-binding validator",
        **({"witness": bundle.witness} if bundle.witness is not None else {}),
    }


def main():
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("contract", type=Path)
    parser.add_argument("--toolchain", type=Path, required=True)
    args = parser.parse_args()
    result = validate_bundle(args.bundle, args.candidate, args.contract, args.toolchain)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["decision"] in ("verified", "violated") else 1


if __name__ == "__main__":
    raise SystemExit(main())
