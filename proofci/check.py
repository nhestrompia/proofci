"""Check a candidate commit against the protected policy of a base commit.

Inputs are two checkouts: `base` (trusted, e.g. the PR's target branch) and
`head` (the candidate). By default the policy -- `proofci.yaml` and the
contract -- is read from `base`; only the Rust code and the proofs come from
`head`. A pull request therefore cannot weaken its own requirements: any
policy change is reported and blocks until it is approved, in which case the
caller re-runs with `policy="head"`.
"""

import hashlib
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import extract, lean, manifest as manifest_mod

VERIFIED = "verified"
UNPROVEN = "unproven"
UNSUPPORTED = "unsupported"
CONTRACT_STALE = "contract-stale"
ERROR = "error"


class ConfigError(Exception):
    """The repository is not configured for ProofCI."""


@dataclass
class Outcome:
    target: str
    guarantee: str
    function: str
    theorem: str
    required: bool
    status: str
    reason: str = ""


@dataclass
class Report:
    outcomes: list = field(default_factory=list)
    policy_source: str = "base"
    policy_changes: list = field(default_factory=list)
    notes: list = field(default_factory=list)
    timings: dict = field(default_factory=dict)

    @property
    def passed(self):
        required = [o for o in self.outcomes if o.required]
        policy_ok = not self.policy_changes or self.policy_source == "head"
        return policy_ok and bool(required) and all(o.status == VERIFIED for o in required)

    def to_json(self):
        return {
            "version": 1,
            "passed": self.passed,
            "policy_source": self.policy_source,
            "policy_changes": self.policy_changes,
            "guarantees": [o.__dict__ for o in self.outcomes],
            "notes": self.notes,
            "timings_seconds": self.timings,
        }


def load_manifest(checkout: Path):
    path = checkout / manifest_mod.MANIFEST_NAME
    if not path.is_file() or path.is_symlink():
        raise ConfigError(f"{manifest_mod.MANIFEST_NAME} not found in {checkout}")
    return manifest_mod.parse(path.read_bytes())


def _tree_digest(checkout: Path, lean_dir: str, module: str):
    root = checkout / lean_dir
    files = [root / f"{module}.lean"]
    if (root / module).is_dir():
        files += sorted((root / module).rglob("*.lean"))
    digest = hashlib.sha256()
    for path in files:
        if path.is_file():
            digest.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes() + b"\0")
        else:
            digest.update(str(path.relative_to(root)).encode() + b"\0<missing>\0")
    return digest.hexdigest()


def policy_changes(base_checkout, base, head_checkout, head):
    """Human-readable list of differences between the base and head policy."""
    if head is None:
        return ["proofci.yaml was removed or is invalid in the pull request"]
    changes = []
    old, new = base.summary(), head.summary()
    for key in ("crate", "lean"):
        if old[key] != new[key]:
            changes.append(f"`{key}` changed from `{old[key]}` to `{new[key]}`")
    for gid, spec in old["guarantees"].items():
        if gid not in new["guarantees"]:
            changes.append(f"guarantee `{gid}` was removed")
        elif new["guarantees"][gid] != spec:
            after = new["guarantees"][gid]
            if spec["required"] and not after["required"]:
                changes.append(f"guarantee `{gid}` was made optional")
            else:
                changes.append(f"guarantee `{gid}` changed")
    for gid in new["guarantees"]:
        if gid not in old["guarantees"]:
            changes.append(f"guarantee `{gid}` was added")
    if _tree_digest(base_checkout, base.lean, "Contract") != _tree_digest(head_checkout, head.lean, "Contract"):
        changes.append(f"the contract `{head.contract}` changed")
    return changes


def check(base_checkout: Path, head_checkout: Path, policy="base", work_dir=None):
    started = time.monotonic()
    report = Report(policy_source=policy)
    base = load_manifest(base_checkout)
    try:
        head = load_manifest(head_checkout)
    except (ConfigError, manifest_mod.ManifestError):
        head = None
    report.policy_changes = policy_changes(base_checkout, base, head_checkout, head)
    if policy == "head":
        if head is None:
            raise ConfigError("the candidate has no valid proofci.yaml")
        active, policy_checkout = head, head_checkout
    else:
        active, policy_checkout = base, base_checkout

    outcomes = {}
    for target, guarantee in active.guarantees():
        outcomes[guarantee.theorem] = Outcome(
            target.id, guarantee.id, target.function, guarantee.theorem, guarantee.required, ERROR)
    report.outcomes = list(outcomes.values())

    def mark(status, reason, only=None):
        for o in report.outcomes:
            if only is None or o.theorem in only:
                o.status, o.reason = status, reason

    with tempfile.TemporaryDirectory(prefix="proofci-", dir=work_dir) as tmp:
        work = Path(tmp)
        # 1. Trusted translation of the candidate's Rust code.
        t0 = time.monotonic()
        try:
            extraction = extract.extract(head_checkout / active.crate, work)
        except extract.Unsupported as error:
            mark(UNSUPPORTED, str(error))
            report.timings["extract"] = round(time.monotonic() - t0, 1)
            return report
        report.timings["extract"] = round(time.monotonic() - t0, 1)

        # 2. Workspace: extracted model + protected contract + candidate proofs.
        ws = lean.assemble(work / "lean", extraction.lean_file, extraction.module,
                           policy_checkout / active.lean, head_checkout / active.lean)
        if not (ws.root / "Proofs.lean").is_file():
            mark(UNPROVEN, f"no proofs found at `{active.proofs}`")
            return report

        # 3. The contract must still elaborate against the new code.
        t0 = time.monotonic()
        try:
            lean.build_contract(ws)
            audit = lean.audit(ws, [(o.theorem, lean_function(o.function)) for o in report.outcomes])
        except lean.ContractError as error:
            mark(CONTRACT_STALE, "the protected contract no longer elaborates against this code; "
                 "a maintainer must update it:\n" + str(error))
            report.timings["contract"] = round(time.monotonic() - t0, 1)
            return report
        report.timings["contract"] = round(time.monotonic() - t0, 1)

        candidates = []
        for o in report.outcomes:
            item = audit[o.theorem]
            if not item["function_found"]:
                o.status, o.reason = UNSUPPORTED, f"`{o.function}` is not in the translated code"
            elif item["kind"] != "theorem":
                o.status, o.reason = CONTRACT_STALE, f"`{o.theorem}` is not a theorem in the contract"
            elif not item["mentions_function"]:
                o.status, o.reason = CONTRACT_STALE, (
                    f"the statement of `{o.theorem}` does not mention `{o.function}`, "
                    "so it would not constrain the implementation")
            elif set(item["function_axioms"]) - set(lean.PERMITTED_AXIOMS):
                extra = sorted(set(item["function_axioms"]) - set(lean.PERMITTED_AXIOMS))
                o.status, o.reason = UNSUPPORTED, (
                    f"`{o.function}` depends on code without a verified model: " + ", ".join(extra))
            else:
                candidates.append(o)

        # 4. Judge the proofs: once for everything, then one by one to attribute.
        # `ws` has only built trusted code so far. Proof code runs in copies.
        t0 = time.monotonic()
        trial = lean.clone(ws, work / "proofs-build")
        if candidates:
            removed = lean.build_proofs(trial)
            if removed is None:
                for o in candidates:
                    o.status, o.reason = UNPROVEN, "the proofs do not build (see the job log)"
                candidates = []
            else:
                for o in list(candidates):
                    if o.theorem in removed:
                        o.status, o.reason = UNPROVEN, "the proof does not check:\n" + removed[o.theorem]
                        candidates.remove(o)
                if removed:
                    report.notes.append("removed failing declarations from Proofs.lean: "
                                        + ", ".join(sorted(removed)))
        runs = iter(range(1, 1000))

        def judge(theorems):
            return lean.comparator(lean.clone(ws, work / f"judge-{next(runs)}", proofs_from=trial), theorems)

        if candidates:
            verdict = judge([o.theorem for o in candidates])
            if verdict.accepted:
                for o in candidates:
                    o.status, o.reason = VERIFIED, ""
            else:
                for o in candidates:
                    single = judge([o.theorem])
                    o.status = VERIFIED if single.accepted else UNPROVEN
                    o.reason = single.reason
        report.timings["proofs"] = round(time.monotonic() - t0, 1)
    report.timings["total"] = round(time.monotonic() - started, 1)
    return report


def lean_function(rust_path: str):
    """`ledger::calculate_fee` -> `ledger.calculate_fee` (Aeneas naming)."""
    return ".".join(rust_path.split("::"))
