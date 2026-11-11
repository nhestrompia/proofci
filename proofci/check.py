"""Check a candidate commit against the protected policy of a base commit.

Inputs are two checkouts: `base` (trusted, e.g. the PR's target branch) and
`head` (the candidate). By default the policy -- `proofci.yaml` and the
contract -- is read from `base`; only the Rust code and the proofs come from
`head`. A pull request therefore cannot weaken its own requirements: any
policy change is reported and blocks until it is approved, in which case the
caller re-runs with `policy="head"`.
"""

import hashlib
import itertools
import os
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

from . import extract, lean, manifest as manifest_mod, typescript

VERIFIED = "verified"
UNPROVEN = "unproven"
UNSUPPORTED = "unsupported"
CONTRACT_STALE = "contract-stale"
ERROR = "error"

PARALLEL_JUDGES = int(os.environ.get("PROOFCI_PARALLEL_JUDGES") or max(1, (os.cpu_count() or 2) // 2))


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
    assumes: list = field(default_factory=list)    # ProofCI models the function relies on
    warnings: list = field(default_factory=list)   # contract shape warnings
    assumed: list = field(default_factory=list)    # outside calls the proof rests on


@dataclass
class Report:
    outcomes: list = field(default_factory=list)
    policy_source: str = "base"
    language: str = "rust"
    policy_changes: list = field(default_factory=list)
    policy_approvers: object = None   # from the protected base policy
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
            "language": self.language,
            "policy_source": self.policy_source,
            "policy_changes": self.policy_changes,
            "policy_approvers": None if self.policy_approvers is None else list(self.policy_approvers),
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
    for key in ("language", "crate", "lean"):
        if old[key] != new[key]:
            changes.append(f"`{key}` changed from `{old[key]}` to `{new[key]}`")
    if old["approvers"] != new["approvers"]:
        changes.append("`policy.approvers` changed")
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


def check(base_checkout: Path, head_checkout: Path, policy="base", work_dir=None, vendor_dir=None):
    started = time.monotonic()
    report = Report(policy_source=policy)
    base = load_manifest(base_checkout)
    try:
        head = load_manifest(head_checkout)
    except (ConfigError, manifest_mod.ManifestError):
        head = None
    report.policy_changes = policy_changes(base_checkout, base, head_checkout, head)
    report.policy_approvers = base.approvers
    report.language = base.language
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
        # 1. Trusted translation of the candidate's Rust code: only what the
        # target functions reach. If that fails, find out which targets
        # reach untranslatable code and translate the others without them.
        t0 = time.monotonic()
        functions = sorted({o.function for o in report.outcomes})
        attempts = itertools.count(1)

        def translate(paths, opaque=()):
            sub = work / f"translate-{next(attempts)}"
            sub.mkdir()
            return extract.extract(head_checkout, active.crate, sub, start_from=paths,
                                   vendor_dir=vendor_dir, opaque=opaque)

        extraction, failures = None, {}
        if active.language == "typescript":
            try:
                extraction = typescript.extract(head_checkout, active.crate, work, functions, policy_checkout, active.assumes, vendor_dir)
                failures = extraction.failures
                if len(failures) == len(functions):
                    extraction = None
            except extract.Unsupported as error:
                failures = dict.fromkeys(functions, str(error))
        else:
            try:
                extraction = translate(functions)
            except extract.Unsupported as error:
                if len(functions) > 1:
                    for function in functions:
                        try:
                            translate([function])
                        except extract.Unsupported as single:
                            failures[function] = str(single)
                if failures and len(failures) < len(functions):
                    # Keep the failing functions as bare declarations so the
                    # contract still elaborates and the other targets are judged.
                    try:
                        extraction = translate(functions, opaque=sorted(failures))
                    except extract.Unsupported:
                        extraction = None
                if extraction is None and len(failures) != len(functions):
                    failures = dict.fromkeys(functions, str(error))
        for o in report.outcomes:
            if o.function in failures:
                o.status, o.reason = UNSUPPORTED, failures[o.function]
        report.timings["extract"] = round(time.monotonic() - t0, 1)
        if extraction is None:
            return report
        pending = [o for o in report.outcomes if o.function not in failures]

        # 2. Workspace: extracted model + protected contract + candidate proofs.
        ws = lean.assemble(work / "lean", extraction.lean_file, extraction.module,
                           policy_checkout / active.lean, head_checkout / active.lean)
        if active.language == "typescript":
            problem = lean.build_translation(ws)
            if problem:
                reason = "ProofCI translated this code but the result does not compile; please report it:\n" + problem
                for o in pending:
                    o.status, o.reason = UNSUPPORTED, reason
                return report
            disagreements, notes = typescript.differential(head_checkout, active.crate, work, ws, extraction)
            report.notes += notes
            if disagreements:
                reason = ("ProofCI's model of this code disagrees with Node, so a proof about it would mean "
                          "nothing; please report it. First disagreement: " + disagreements[0])
                for o in pending:
                    o.status, o.reason = UNSUPPORTED, reason
                return report
        if not (ws.root / "Proofs.lean").is_file():
            mark(UNPROVEN, f"no proofs found at `{active.proofs}`", only={o.theorem for o in pending})
            return report

        # 3. The contract must still elaborate against the new code.
        t0 = time.monotonic()
        try:
            lean.build_contract(ws)
            model_names = {f"{extraction.crate_name}.{name}": path for path, name in (extraction.modelled or [])}
            names = extraction.names or {}
            audit = lean.audit(ws, [(o.theorem, names.get(o.function, lean_function(o.function))) for o in pending],
                               list(model_names))
        except lean.ContractError as error:
            names = {o.theorem for o in pending}
            mark(CONTRACT_STALE, "the protected contract no longer elaborates against this code; "
                 "a maintainer must update it:\n" + str(error), only=names)
            report.timings["contract"] = round(time.monotonic() - t0, 1)
            return report
        report.timings["contract"] = round(time.monotonic() - t0, 1)

        candidates = []
        for o in pending:
            item = audit[o.theorem]
            o.assumes = [model_names[n] for n in item.get("models", []) if n in model_names]
            if extraction.assumed:
                o.assumed = [f"{call}: {extraction.assumptions[call]}" for call in extraction.assumed.get(o.function, [])]
            if item.get("hypothesis_mentions_function"):
                o.warnings.append(f"a hypothesis of `{o.theorem}` mentions `{o.function}`, so the statement "
                                  "may assume what it should prove")
            if item.get("trivial_conclusion"):
                o.warnings.append(f"the conclusion of `{o.theorem}` is trivially true")
            if item.get("post_ignores_result"):
                o.warnings.append(f"the postcondition of `{o.theorem}` does not depend on the result, "
                                  "so it only restates facts about the inputs")
            if not item["function_found"]:
                o.status, o.reason = UNSUPPORTED, f"`{o.function}` is not in the translated code"
            elif item["kind"] != "theorem":
                o.status, o.reason = CONTRACT_STALE, f"`{o.theorem}` is not a theorem in the contract"
            elif not item["conclusion_mentions_function"]:
                o.status, o.reason = CONTRACT_STALE, (
                    f"the conclusion of `{o.theorem}` does not mention `{o.function}`, "
                    "so it would not constrain the implementation")
            elif set(item["function_axioms"]) - set(lean.PERMITTED_AXIOMS):
                extra = sorted(set(item["function_axioms"]) - set(lean.PERMITTED_AXIOMS))
                o.status, o.reason = UNSUPPORTED, (
                    f"`{o.function}` depends on code without a verified model: " + ", ".join(extra))
            else:
                candidates.append(o)

        # 4. Judge the proofs. `ws` has only built trusted code; proof code
        # only ever runs in disposable copies of it.
        #   a. The comparator judges the proofs as submitted. If it accepts,
        #      every candidate is verified (the common case: one proof build).
        #   b. Otherwise, remove declarations that do not elaborate, judge what
        #      remains, and if that is rejected too, judge each theorem alone
        #      (in parallel) to attribute the failure.
        t0 = time.monotonic()
        runs = itertools.count(1)

        def judge(theorems, proofs_from=None):
            return lean.comparator(
                lean.clone(ws, work / f"judge-{next(runs)}", proofs_from=proofs_from), theorems)

        def judge_each(items, proofs_from):
            with ThreadPoolExecutor(max_workers=min(len(items), PARALLEL_JUDGES)) as pool:
                names = [[o.theorem] for o in items]
                for o, single in zip(items, list(pool.map(lambda n: judge(n, proofs_from), names))):
                    o.status = VERIFIED if single.accepted else UNPROVEN
                    o.reason = single.reason

        first = judge([o.theorem for o in candidates]) if candidates else None
        if first and first.accepted:
            for o in candidates:
                o.status, o.reason = VERIFIED, ""
            candidates = []
        if candidates:
            trial = lean.clone(ws, work / "proofs-build")
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
            if candidates and not removed:
                # The proofs build as submitted, so the first verdict stands
                # for the set; judge each theorem to attribute it.
                if len(candidates) == 1:
                    candidates[0].status, candidates[0].reason = UNPROVEN, first.reason
                else:
                    judge_each(candidates, trial)
            elif candidates:
                verdict = judge([o.theorem for o in candidates], trial)
                if verdict.accepted:
                    for o in candidates:
                        o.status, o.reason = VERIFIED, ""
                elif len(candidates) == 1:
                    candidates[0].status, candidates[0].reason = UNPROVEN, verdict.reason
                else:
                    judge_each(candidates, trial)
        report.timings["proofs"] = round(time.monotonic() - t0, 1)
    if active.language == "typescript":
        for o in report.outcomes:
            if o.status == UNPROVEN and o.reason and not o.reason.startswith("no proofs found"):
                o.reason += ("\nIf the code changed, its translation changed with it. Compare "
                             "`proofci dev --show` with the proof: either the proof needs to follow the code, "
                             "or the change broke what the guarantee says.")
    report.timings["total"] = round(time.monotonic() - started, 1)
    return report


def fetch(base_checkout: Path, head_checkout: Path, vendor_dir: Path, policy="base"):
    """Vendor the candidate's crates.io dependencies (the step with network)."""
    active = load_manifest(head_checkout if policy == "head" else base_checkout)
    if active.language == "typescript":
        # Package declarations are installed for the type checker; no package code runs.
        with tempfile.TemporaryDirectory(prefix="proofci-fetch-", dir=vendor_dir) as tmp:
            typescript.install(head_checkout, active.crate, vendor_dir, Path(tmp))
        return
    with tempfile.TemporaryDirectory(prefix="proofci-fetch-") as tmp:
        extract.fetch(head_checkout, active.crate, vendor_dir, Path(tmp))


def lean_function(rust_path: str):
    """`ledger::calculate_fee` -> `ledger.calculate_fee` (Aeneas naming)."""
    return ".".join(rust_path.split("::"))
