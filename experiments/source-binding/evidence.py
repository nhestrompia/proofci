"""Validate submitted proof evidence against the trusted source-binding policy.

The bundle is intentionally data-only. Candidate and contract bytes are supplied
by the trusted caller, while all challenge construction, toolchain selection,
checker commands, and acceptance policy live in this module.
"""

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile

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
FORBIDDEN_SOLUTION = re.compile(
    r"\b(?:sorry|axiom|unsafe|native_decide|implemented_by|run_tac|elab|macro)\b"
)


class EvidenceError(ValueError):
    """The submitted bundle cannot be trusted as evidence."""


class ValidationUnavailable(RuntimeError):
    """The pinned validator is not available in this environment."""


class BuildFailure(RuntimeError):
    """A fixed validation command failed before the checker decision."""


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
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise EvidenceError(f"malformed {label}") from error


def _manifest(bundle):
    manifest = _json(_read(bundle / FILES["manifest"], 16 * 1024, "manifest"), "manifest")
    if not isinstance(manifest, dict) or set(manifest) != MANIFEST_FIELDS:
        raise EvidenceError("manifest fields do not match the trusted bundle format")
    if manifest["version"] != BUNDLE_VERSION:
        raise EvidenceError("unsupported evidence bundle version")
    if manifest["claimed_decision"] != "verified":
        raise EvidenceError("only a claimed verified result can be submitted as proof evidence")
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
                          manifest["candidate_sha256"], manifest["contract_sha256"])


def _sources(bundle):
    _, _, identity, statement, challenge = binding.build_sources(bundle.candidate, bundle.contract)
    solution = bundle.solution.decode("utf-8")
    return identity, statement, challenge, solution


def _write_workspace(root, bundle):
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


def _sandbox_prefix(toolchain, workspace, policy_path, read_only_sources):
    if platform.system() != "Linux" or platform.machine() != "aarch64":
        raise ValidationUnavailable("the pinned validator supports Linux arm64 only")
    bwrap = shutil.which("bwrap", path="/usr/bin:/bin")
    if not bwrap:
        raise ValidationUnavailable("pinned bubblewrap is unavailable")
    source_mounts = []
    if read_only_sources:
        for name in (
                "lakefile.lean", "Candidate.lean", "CandidateCheck.lean",
                "Challenge.lean", "Solution.lean"):
            source_mounts.extend((
                "--ro-bind", f"/workspace/{name}", f"/workspace/{name}"
            ))
    return [
        bwrap, "--die-with-parent", "--unshare-all", "--unshare-net",
        "--ro-bind", str(toolchain), "/lean",
        "--ro-bind", "/usr", "/usr", "--ro-bind", "/bin", "/bin",
        "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
        "--bind", str(workspace), "/workspace", "--chdir", "/workspace",
        "--ro-bind", str(policy_path), "/workspace/comparator.json",
        *source_mounts,
        "--setenv", "HOME", "/tmp", "--setenv", "LC_ALL", "C.UTF-8",
        "--setenv", "PATH", "/lean/bin:/usr/bin:/bin", "--",
        "/lean/bin/lake",
    ]


def _run(toolchain, workspace, policy_path, args, timeout=120, allow_failure=False,
         combined=False, read_only_sources=False):
    command = _sandbox_prefix(toolchain, workspace, policy_path, read_only_sources) + list(args)
    env = {"PATH": "/usr/bin:/bin", "HOME": "/tmp", "LC_ALL": "C.UTF-8"}
    try:
        result = subprocess.run(command, env=env, capture_output=True, text=True,
                                timeout=timeout, check=False, start_new_session=True)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ValidationUnavailable(f"validator command unavailable: {error}") from error
    if result.returncode and not allow_failure:
        output = (result.stdout + result.stderr)[-64 * 1024:]
        raise BuildFailure(f"{' '.join(args)} failed: {output}")
    output = result.stdout if not combined else result.stdout + result.stderr
    return result.returncode, output if not combined else output[-64 * 1024:]


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
        "nanoda kernel rejects the solution",
        "Your solution is not okay!",
    ))
    if rejected and lean_accepts and nanoda_accepts:
        raise ContradictoryEvidence("checker output contains both acceptance and rejection")
    if status == 0 and lean_accepts and nanoda_accepts and "Your solution is okay!" in output:
        return "verified"
    if status == 0 or lean_accepts != nanoda_accepts:
        raise CheckerDisagreement("checker status and acceptance output disagree")
    return "unproven"


def validate_bundle(bundle_path, candidate_path, contract_path, toolchain=None):
    """Return the only authoritative decision for a submitted proof bundle."""
    try:
        bundle = load_bundle(bundle_path, candidate_path, contract_path)
    except (EvidenceError, OSError, ValueError) as error:
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
                _run(toolchain, construction, policy_path, ("build", "Candidate"))
                _run(toolchain, construction, policy_path, ("build", "Challenge"))
                _run(toolchain, construction, policy_path, ("build", "Solution"))
                _run(toolchain, construction, policy_path,
                     ("env", "leanexport", "Challenge", "--", "contract"))
                _run(toolchain, construction, policy_path,
                     ("env", "leanexport", "Solution", "--", "contract"))

            with tempfile.TemporaryDirectory(prefix="proofci-validation-") as validation_dir:
                validation = Path(validation_dir)
                _write_workspace(validation, bundle)
                run_options = {"read_only_sources": True}
                _run(toolchain, validation, policy_path, ("build", "Candidate"), **run_options)
                _run(toolchain, validation, policy_path, ("build", "Challenge"), **run_options)
                _run(toolchain, validation, policy_path, ("build", "Solution"), **run_options)
                _, challenge_export = _run(
                    toolchain, validation, policy_path,
                    ("env", "leanexport", "Challenge", "--", "contract"), **run_options
                )
                _, solution_export = _run(
                    toolchain, validation, policy_path,
                    ("env", "leanexport", "Solution", "--", "contract"), **run_options
                )
                if challenge_export.encode() != bundle.challenge_export:
                    raise EvidenceError("fresh challenge export differs from submitted evidence")
                if solution_export.encode() != bundle.solution_export:
                    raise EvidenceError("fresh solution export differs from submitted evidence")
                checker_status, checker_output = _run(
                    toolchain, validation, policy_path, TRUSTED_CHECKER,
                    allow_failure=True, combined=True, **run_options
                )
    except EvidenceError as error:
        return _invalid("invalid_evidence", error)
    except CheckerDisagreement as error:
        return _invalid("checker_disagreement", error)
    except ContradictoryEvidence as error:
        return _invalid("contradictory_evidence", error)
    except BuildFailure as error:
        return _invalid("build_failure", error)
    except ValidationUnavailable as error:
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
        "decision": "verified",
        "reason": "accepted by the reconstructed challenge and independent checkers",
        "candidate_sha256": bundle.candidate_sha256,
        "contract_sha256": bundle.contract_sha256,
        "permitted_axioms": sorted(PERMITTED_AXIOMS),
        "checker": list(TRUSTED_CHECKER),
        "policy": "fixed source-binding validator",
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
    return 0 if result["decision"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
