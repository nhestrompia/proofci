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

from . import bridge, extract, lean, manifest as manifest_mod, typescript

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
    effects: list = None            # `async` code only: the effects the proof ranges over
    arguments_stable: list = None   # `async` code only: reads that rest on arguments staying unchanged
    constants_stable: list = None   # `async` code only: exported tables read after an `await`, assumed unchanged by code outside the program
    bridge: str = None              # TypeScript only: how the function's view relates to JavaScript (proved, tested or failed)
    hint: str = None                # TypeScript only: the smallest rewrite the translator accepts, when unsupported


@dataclass
class Report:
    outcomes: list = field(default_factory=list)
    policy_source: str = "base"
    language: str = "rust"
    policy_changes: list = field(default_factory=list)
    policy_approvers: object = None   # from the protected base policy
    notes: list = field(default_factory=list)
    timings: dict = field(default_factory=dict)
    functions: list = field(default_factory=list)   # TypeScript only: one bridge.FunctionStatus per translated function
    disagreements: list = field(default_factory=list)  # TypeScript only: inputs where Node and the Lean view differ
    downgrades: list = field(default_factory=list)  # TypeScript only: proved on the base branch, not proved now
    stale_accepts: list = field(default_factory=list)  # `accept_downgrades` entries that are no downgrade here

    @property
    def passed(self):
        required = [o for o in self.outcomes if o.required]
        policy_ok = not self.policy_changes or self.policy_source == "head"
        return (policy_ok and bool(required) and all(o.status == VERIFIED for o in required)
                and all(d["accepted"] for d in self.downgrades))

    def to_json(self):
        return {
            "version": 1,
            "passed": self.passed,
            "language": self.language,
            "policy_source": self.policy_source,
            "policy_changes": self.policy_changes,
            "policy_approvers": None if self.policy_approvers is None else list(self.policy_approvers),
            "guarantees": [o.__dict__ | {"errors": lean.structured_errors(o.reason)} for o in self.outcomes],
            "disagreements": self.disagreements,
            "functions": [f.entry() for f in self.functions],
            "bridge_summary": {status: sum(f.status == status for f in self.functions)
                               for status in (bridge.PROVED, bridge.TESTED, bridge.FAILED)},
            "downgrades": self.downgrades,
            "stale_accepts": self.stale_accepts,
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
    for call, signature in old["assumes"].items():
        if call not in new["assumes"]:
            changes.append(f"the assumed call `{call}` was removed")
        elif new["assumes"][call] != signature:
            changes.append(f"the assumed call `{call}` changed its signature")
    for call in new["assumes"]:
        if call not in old["assumes"]:
            changes.append(f"the call `{call}` was assumed")
    # Outside operations are what a proof about `async` code may lean on, so every difference
    # counts, in either direction: a looser signature or a different `kind` changes the claim.
    for effect_id, entry in old["effects"].items():
        if effect_id not in new["effects"]:
            changes.append(f"effect `{effect_id}` was removed")
        elif new["effects"][effect_id] != entry:
            changes.append(f"effect `{effect_id}` changed")
    for effect_id in new["effects"]:
        if effect_id not in old["effects"]:
            changes.append(f"effect `{effect_id}` was added")
    if old["require_bridge"] != new["require_bridge"]:
        changes.append(f"`require_bridge` changed from `{old['require_bridge']}` to `{new['require_bridge']}`")
    if old["accept_downgrades"] != new["accept_downgrades"]:
        added = ", ".join(f"`{f}`" for f in sorted(set(new["accept_downgrades"]) - set(old["accept_downgrades"])))
        removed = ", ".join(f"`{f}`" for f in sorted(set(old["accept_downgrades"]) - set(new["accept_downgrades"])))
        changes.append(f"`accept_downgrades` changed (added: {added or 'none'}; removed: {removed or 'none'})")
    if _tree_digest(base_checkout, base.lean, "Contract") != _tree_digest(head_checkout, head.lean, "Contract"):
        changes.append(f"the contract `{head.contract}` changed")
    return changes


def check(base_checkout: Path, head_checkout: Path, policy="base", work_dir=None, vendor_dir=None,
          bridge_timeout=None, bridge_budget=None):
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
                extraction = typescript.extract(head_checkout, active.crate, work, functions, policy_checkout, active.assumes, vendor_dir, active.effects)
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
                o.status, (o.reason, o.hint) = UNSUPPORTED, typescript.split_hint(failures[o.function])
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
            detail = {}
            disagreements, notes = typescript.differential(head_checkout, active.crate, work, ws, extraction, detail=detail)
            report.notes += notes
            if disagreements:
                report.disagreements = disagreements
                reason = ("ProofCI's model of this code disagrees with Node, so a proof about it would mean "
                          "nothing; please report it. First disagreement: " + disagreements[0])
                for o in pending:
                    o.status, o.reason = UNSUPPORTED, reason
                differ = set(detail.get("differ", []))
                report.functions = [bridge.FunctionStatus(
                    f, bridge.FAILED, reason if f in differ or not differ else
                    "not checked: the model of another function disagrees with Node, which blocks the whole check")
                    for f in functions if f not in failures]
                _attach(report)
                return report

            # 3. The bridge: is the view the same as the JavaScript semantics, or only tested against Node?
            t0 = time.monotonic()
            report.functions = _bridge(report, extraction, active, work, [f for f in functions if f not in failures],
                                       bridge_timeout, bridge_budget)
            pending = [o for o in pending if o.status == ERROR]
            report.timings["bridge"] = round(time.monotonic() - t0, 1)

            # 3b. The ratchet: a function proved on the base branch must not silently drop to
            # tested, unsupported, failed or removed. The base side is re-derived below.
            t0 = time.monotonic()
            budget = (None if bridge_budget is None
                      else max(0, bridge_budget - report.timings["bridge"]))
            report.downgrades, report.stale_accepts = _ratchet(
                report, base_checkout, head_checkout, base, active, work, functions,
                failures, vendor_dir, bridge_timeout, budget)
            if report.downgrades:
                report.timings["ratchet"] = round(time.monotonic() - t0, 1)
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
            if extraction.effects is not None and o.function in extraction.effects:
                o.effects = [f"{e}: {extraction.effect_text[e]}" for e in extraction.effects[o.function]]
                o.arguments_stable = list(extraction.arguments_relied.get(o.function, []))
                o.constants_stable = list((extraction.constants_relied or {}).get(o.function, []))
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


def _attach(report):
    """Record on each guarantee how its function's view stands."""
    by_function = {f.function: f for f in report.functions}
    for f in report.functions:
        f.guarantees = [f"{o.target}/{o.guarantee}" for o in report.outcomes if o.function == f.function]
    for o in report.outcomes:
        if o.function in by_function:
            o.bridge = by_function[o.function].status


def _bridge(report, extraction, active, work, functions, timeout, budget):
    """Bridge every translated function and block the guarantees that depend on one whose status the
    policy doesn't accept. Returns the per-function statuses."""
    results = bridge.run(extraction, work, functions, timeout, budget)
    for f in functions:
        status = results[f]
        refused = None
        if status.status == bridge.FAILED:
            refused = status.reason
        elif status.status == bridge.TESTED and active.bridge_required(f):
            refused = ("`require_bridge` is set in proofci.yaml, and the bridge theorem for this function did not check "
                       f"({status.reason}). Its view is only tested against Node, not proved to match JavaScript.")
        if refused:
            for o in report.outcomes:
                if o.function == f and o.status == ERROR:
                    o.status, o.reason = UNSUPPORTED, refused
    ordered = [results[f] for f in functions]
    report.functions = ordered
    _attach(report)
    return ordered


# Dependency declarations and manager config a pull request can rewrite to change what
# the base re-check sees; any of them changing makes a non-proved base result inconclusive.
_DEP_FILES = ("package.json", "package-lock.json", "npm-shrinkwrap.json", "yarn.lock",
              "pnpm-lock.yaml", "pnpm-workspace.yaml") + tuple(sorted(typescript.CONFIG_FILES))

# Bridge reasons that mean the check never reached a verdict, which is no evidence either way.
_INCOMPLETE = ("time budget", "did not finish", "could not be run", "out of memory",
               "is not installed", "generator failed")


def _incomplete(reason):
    return any(m in (reason or "") for m in _INCOMPLETE)


def _deps_changed(base_checkout, head_checkout, package_rel):
    """Any dependency file changed between the base and head checkouts, in the package
    directory or an ancestor of it — the vendored install reads the nearest lockfile and
    manager config at or above the package (see typescript.find_lockfile/CONFIG_FILES)."""
    root = base_checkout.resolve()
    directory = (root / package_rel).resolve()
    while root in (directory, *directory.parents):
        rel = directory.relative_to(root)
        for name in _DEP_FILES:
            old, new = directory / name, head_checkout / rel / name
            if old.is_file() != new.is_file() or (old.is_file() and old.read_bytes() != new.read_bytes()):
                return True
        if directory == root:
            break
        directory = directory.parent
    return False


def _base_statuses(base_checkout, base, work, functions, vendor_dir, timeout, budget, now,
                   deps_changed):
    """Bridge status of each of `functions` on the base checkout, re-derived with the same
    toolchain. `proved`, `tested` or `failed` are verdicts; "not proved" only for a function
    whose file does not exist on the base, or — when the pull request left the dependency
    files untouched — for one the base could not translate, which could not have been proved
    there either. Everything else is "unknown": a base result the pull request's vendored
    dependencies or budget could influence, or one that never reached a verdict, can hide a
    proved function, so it blocks like a downgrade. The comparison with Node is skipped on
    purpose: it can only turn a status into `failed`, never into or out of `proved`."""
    sub = work / "base-check"
    sub.mkdir(exist_ok=True)
    missing = {f for f in functions
               if not (base_checkout / base.crate / f.rsplit("::", 1)[0]).is_file()}
    todo = [f for f in functions if f not in missing]
    statuses = dict.fromkeys(missing, "not proved")
    if not todo:
        return statuses
    try:
        extraction = typescript.extract(base_checkout, base.crate, sub, todo, base_checkout,
                                        base.assumes, vendor_dir, base.effects)
    except Exception:
        statuses.update(dict.fromkeys(todo, "unknown"))
        return statuses
    inconclusive = "unknown" if deps_changed else "not proved"
    statuses.update(dict.fromkeys(extraction.failures, inconclusive))
    todo = [f for f in todo if f not in extraction.failures]
    if not todo:
        return statuses

    inputs = sub / "inputs"
    inputs.mkdir(exist_ok=True)
    files, reasons = bridge.generate(extraction, todo, inputs)
    statuses.update(dict.fromkeys(reasons, inconclusive))
    for function, name in files.items():
        head_file = work / "bridge" / name
        if head_file.is_file() and head_file.read_bytes() == (inputs / name).read_bytes():
            # Byte-identical bridge input: the base result is the head result. A finished
            # head run means the function was not proved on the base either; a head run
            # that timed out is inconclusive, and re-checking it can only time out again.
            statuses[function] = "not proved" if not _incomplete(now[function][1]) else "unknown"
    todo = [f for f in files if f not in statuses]
    results = bridge.run(extraction, sub, todo, timeout, budget) if todo else {}
    for function, status in results.items():
        if status.status != bridge.PROVED and (deps_changed or _incomplete(status.reason)):
            statuses[function] = "unknown"
        else:
            statuses[function] = status.status
    return statuses


def _downgrades(now, was, accepted):
    """One entry per function not proved here that was proved on the base (or whose base
    status could not be determined — fail closed). `now` maps function -> (status, reason)."""
    out = []
    for function in sorted(now):
        status, reason = now[function]
        if status == bridge.PROVED:
            continue
        if was.get(function) == bridge.PROVED:
            out.append({"function": function, "was": bridge.PROVED, "now": status,
                        "reason": reason or "the bridge no longer proves this function",
                        "accepted": function in accepted})
        elif was.get(function) == "unknown":
            out.append({"function": function, "was": "unknown", "now": status,
                        "reason": "the base branch could not be checked, so whether this function "
                                  "was proved there is unknown", "accepted": function in accepted})
    return out


def _ratchet(report, base_checkout, head_checkout, base, active, work, functions, failures,
             vendor_dir, bridge_timeout, bridge_budget):
    """Downgrades of functions the base branch had proved (see `_downgrades`).

    Only functions still named by a target are compared: a function whose target was removed
    is a policy change, judged like every other one. The base statuses come from re-running
    the same toolchain on the base checkout — trusted inputs, never the pull request's view
    of them — and only for the functions that could be a downgrade."""
    tracked = {t.function for t in base.targets} & set(functions)
    now = {}
    for status in report.functions:
        if status.function in tracked:
            now[status.function] = (status.status, status.reason)
    for function, reason in failures.items():
        if function in tracked:
            head, _ = typescript.split_hint(reason)
            now[function] = ("unsupported", head.strip())
    for function in tracked - set(now):
        now[function] = ("removed", "the function is not in the pull request's code")
    todo = sorted(f for f, (status, _) in now.items() if status != bridge.PROVED)
    accepted = set(active.accept_downgrades or ())
    if not todo:
        return [], sorted(accepted)
    deps_changed = _deps_changed(base_checkout, head_checkout, base.crate)
    was = _base_statuses(base_checkout, base, work, todo, vendor_dir, bridge_timeout,
                         bridge_budget, now, deps_changed)
    downgrades = _downgrades({f: now[f] for f in todo}, was, accepted)
    return downgrades, sorted(accepted - {d["function"] for d in downgrades})


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
