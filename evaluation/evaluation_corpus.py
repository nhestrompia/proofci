"""Load, check and lock the frozen evaluation corpus."""
import hashlib
import json
from pathlib import Path

import oracle

ROOT = Path(__file__).resolve().parent / "corpus"
LOCK = ROOT / "lock.json"
PACKAGES = ("arithmetic", "collections", "state")
REQUIRED_DOMAINS = {"arithmetic", "collections", "state transitions"}
CATEGORIES = {
    "correct_change", "obsolete_proof", "intentional_violation", "contract_mutation",
    "source_substitution", "forbidden_axiom", "forged_evidence", "invalid_submission",
    "unsupported_input", "timeout", "persistence",
}
# Scenarios in these categories must never yield a false verified result or a
# passing gate that the scenario forbids. The aggregate reports every category,
# but a release is blocked by a false acceptance anywhere.
SOUNDNESS = {"intentional_violation", "contract_mutation", "source_substitution", "forbidden_axiom",
             "forged_evidence", "invalid_submission"}
PERSISTENCE = {"persistence"}
EVIDENCE_KINDS = {"fresh", "stale", "missing", "refute"}
FORGERIES = {
    "mutated_contract", "shadow_source", "custom_axiom", "sorry", "indirect_axiom", "weakened_statement",
    "shadow_definition", "candidate_digest", "flipped_claim", "edited_solution", "tampered_witness",
    "replayed_refutation", "extra_file", "malformed_manifest",
}
CANDIDATE = "Target.lean"
MANIFEST = "contracts.json"


def contract_bytes(contract):
    """Canonical contract encoding shared with the local baseline store."""
    return (json.dumps(contract, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def files():
    return sorted(p for p in ROOT.rglob("*") if p.is_file() and p != LOCK and "__pycache__" not in p.parts)


def digest_files():
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files()}


def corpus_digest(file_digests):
    return hashlib.sha256(json.dumps(file_digests, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def load():
    packages = {}
    for name in PACKAGES:
        data = json.loads((ROOT / "packages" / name / "package.json").read_text())
        data["root"] = ROOT / "packages" / name
        packages[name] = data
    scenarios = json.loads((ROOT / "scenarios.json").read_text())["scenarios"]
    return packages, scenarios


def properties(package, scenario):
    chosen = scenario["properties"]
    every = [p["id"] for p in package["properties"]]
    return every if chosen == "all" else list(chosen)


def head_candidate(package, scenario):
    head = scenario["head"]
    if "candidate_text" in head:
        return head["candidate_text"]
    return package["candidates"][head["candidate"]]


def spec_for(mapping, prop):
    if not mapping:
        return None
    return mapping.get(prop, mapping.get("*"))


def check(packages, scenarios):
    """Return a list of problems; an empty list means the corpus is well formed."""
    problems = []
    total = 0
    domains = set()
    for name, package in packages.items():
        domains.add(package["domain"])
        ids = [p["id"] for p in package["properties"]]
        if len(set(ids)) != len(ids):
            problems.append(f"{name}: duplicate property identifiers")
        total += len(ids)
        companion = package["root"] / package["companion"]["path"]
        if not companion.is_file():
            problems.append(f"{name}: missing companion module")
        for kind, text in package["candidates"].items():
            try:
                oracle.candidate_expression(text)
            except ValueError as error:
                problems.append(f"{name}/{kind}: {error}")
        for prop in package["properties"]:
            for kind, expected in prop["truth"].items():
                holds, _ = oracle.judge(package["candidates"][kind], prop["contract"])
                if holds != expected:
                    problems.append(f"{name}/{prop['id']}/{kind}: reviewed truth {expected} disagrees with oracle")
            if not prop["truth"].get("base"):
                problems.append(f"{name}/{prop['id']}: reviewed properties must hold for the base target")
            if not oracle.judge(package["candidates"]["shadow"], prop["contract"])[0]:
                problems.append(f"{name}/{prop['id']}: shadow target must satisfy every property")
    if total < 30:
        problems.append(f"corpus has {total} properties; at least 30 are required")
    if not REQUIRED_DOMAINS <= domains:
        problems.append("corpus must cover arithmetic, collections and state transitions")
    seen = set()
    for scenario in scenarios:
        sid = scenario["id"]
        if sid in seen:
            problems.append(f"duplicate scenario {sid}")
        seen.add(sid)
        if scenario["category"] not in CATEGORIES:
            problems.append(f"{sid}: unknown category")
        package = packages.get(scenario["package"])
        if package is None:
            problems.append(f"{sid}: unknown package")
            continue
        known = {p["id"]: p for p in package["properties"]}
        chosen = properties(package, scenario)
        if not chosen or any(p not in known for p in chosen):
            problems.append(f"{sid}: unknown properties")
            continue
        head = scenario["head"]
        candidate = head_candidate(package, scenario)
        for prop in chosen:
            for slot in ("evidence", "refutation"):
                spec = spec_for(head.get(slot), prop)
                if spec is None:
                    continue
                kind = spec["forge"] if isinstance(spec, dict) else spec
                if kind not in EVIDENCE_KINDS | FORGERIES:
                    problems.append(f"{sid}/{prop}: unknown evidence kind {kind}")
                    continue
                try:
                    holds, _ = oracle.judge(candidate, known[prop]["contract"])
                except ValueError:
                    holds = None
                if kind == "fresh" and holds is not True:
                    problems.append(f"{sid}/{prop}: fresh proof requested for a property that does not hold")
                if kind == "refute" and holds is not False:
                    problems.append(f"{sid}/{prop}: refutation requested for a property that holds")
        if "store" in scenario:
            if scenario["category"] != "persistence":
                problems.append(f"{sid}: only persistence scenarios use the baseline store")
            if any("precondition" in known[p]["contract"] for p in chosen):
                problems.append(f"{sid}: the local baseline manifest cannot express preconditions")
    missing = CATEGORIES - {s["category"] for s in scenarios}
    if missing:
        problems.append("scenario categories missing: " + ", ".join(sorted(missing)))
    return problems


def read_lock():
    if not LOCK.is_file():
        return None
    return json.loads(LOCK.read_text())


def verify_lock():
    """Return (lock, problems). The corpus is frozen only if it matches its lock."""
    lock = read_lock()
    if lock is None:
        return None, ["corpus is not frozen: evaluation/corpus/lock.json is missing"]
    current = digest_files()
    problems = []
    for path in sorted(set(current) | set(lock["files"])):
        if current.get(path) != lock["files"].get(path):
            problems.append(f"corpus file differs from the frozen lock: {path}")
    if corpus_digest(lock["files"]) != lock["corpus_sha256"]:
        problems.append("lock digest does not match its file list")
    return lock, problems


def freeze(frozen_at, reviewer):
    current = digest_files()
    lock = {"version": 1, "frozen_at": frozen_at, "reviewer": reviewer,
            "statement": "Frozen before any assisted measurement. Changing a property, scenario or "
                         "expectation requires a new lock and invalidates comparisons with earlier runs.",
            "corpus_sha256": corpus_digest(current), "files": current}
    LOCK.write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n")
    return lock
