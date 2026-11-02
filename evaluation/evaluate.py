#!/usr/bin/env python3
"""Run the frozen ProofCI evaluation corpus through the public verifier commands.

Subcommands:
  check    validate the corpus and its freeze lock without Docker
  freeze   record the reviewed corpus digest before any assisted measurement
  run      execute scenarios and write evaluation.json and evaluation.md
  render   rebuild evaluation.md from an existing evaluation.json

Exit status of `run`: 0 when the complete or selected scenarios produced no
false acceptance and met every deterministic expectation, 1 when a false
acceptance or unmet expectation was recorded (release blocked), 2 when the
evaluation itself could not run.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
import uuid

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
PORTABLE = REPO / "portable"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(PORTABLE))

import aggregate  # noqa: E402
import evaluation_corpus as corpus  # noqa: E402
import oracle  # noqa: E402
import proofci  # noqa: E402
from container import IMAGE_ID  # noqa: E402

REPOSITORY = "https://example.invalid/proofci-evaluation.git"
APPROVER = "evaluation-maintainer"
RESOURCE_POLICY = {"timeout_seconds": 900, "cpu_seconds": 900, "memory_bytes": 2147483648,
                   "file_bytes": 2147483648, "processes": 256}
COMMAND_TIMEOUT = 1500
SOLUTIONS = {
    "custom_axiom": "import CandidateCheck\naxiom cheat : False\n{statement}exact cheat.elim\n",
    "sorry": "import CandidateCheck\n{statement}sorry\n",
    "indirect_axiom": ("import CandidateCheck\naxiom helper : ∀ n : Nat, n = n + 1\n"
                       "theorem bridge : False := by have h := helper 0; omega\n{statement}exact bridge.elim\n"),
    "weakened_statement": "import CandidateCheck\ntheorem contract (x : Nat) : target x = target x := rfl\n",
    "shadow_definition": ("import CandidateCheck\nnamespace Shadow\ndef target (x : Nat) : Nat := {rhs}\nend Shadow\n"
                          "theorem contract (x : Nat) : Shadow.target x = {rhs} := rfl\n"),
}
EDITED_SOLUTION = b"import CandidateCheck\ntheorem contract (x : Nat) : target x = target x := rfl\n"
GIT_IDENTITY = {"GIT_AUTHOR_NAME": "ProofCI Evaluation", "GIT_AUTHOR_EMAIL": "evaluation@example.invalid",
                "GIT_COMMITTER_NAME": "ProofCI Evaluation", "GIT_COMMITTER_EMAIL": "evaluation@example.invalid",
                "GIT_AUTHOR_DATE": "2026-11-01T00:00:00Z", "GIT_COMMITTER_DATE": "2026-11-01T00:00:00Z",
                "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
TEMPERATURE = ("Repetition 1 of each scenario is cold: the first execution in this invocation, starting a "
               "fresh verifier container. Later repetitions are warm: the pinned image, host page cache and "
               "prepared evidence are already present. The verifier itself never reuses proof results.")


def sha(data):
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Evidence plans and construction

def substitute(expression, value):
    """Replace the variable `x` in a restricted expression."""
    return re.sub(r"\bx\b", f"({value})", expression)


def positive_bodies(contract):
    """Reviewed proof shapes that stay inside the validator's dependency policy.

    `rfl` covers properties definitionally equal to the target. Point and bounded
    preconditions use explicit `Eq.ndrec` and `Nat.casesOn` terms, because the
    `cases`, `simp`, `omega` and `decide` tactics introduce declarations that the
    fixed export policy rejects.
    """
    bodies = ["rfl"]
    pre = contract.get("precondition")
    if pre is None:
        return bodies
    rhs = contract["rhs"]
    bound = int(pre["rhs"])
    if pre["op"] == "=":
        bodies.append(f"exact Eq.ndrec (motive := fun y => target y = {substitute(rhs, 'y')}) rfl (Eq.symm h)")
        return bodies
    size = bound if pre["op"] == "<" else bound + 1
    op = pre["op"]

    def proposition(value):
        return f"{value} {op} {bound} → target ({value}) = {substitute(rhs, value)}"

    def succ_branch(level):
        offset = "m + 1" if level == 0 else f"m + 1 + {level}"
        if level + 1 >= size:
            stripped = "hm"
            for _ in range(bound):
                stripped = f"Nat.le_of_succ_le_succ ({stripped})"
            return (f"(fun m hm => False.rec (fun _ => target ({offset}) = {substitute(rhs, offset)}) "
                    f"(Nat.not_succ_le_zero m ({stripped})))")
        following = level + 1
        return (f"(fun n => Nat.casesOn (motive := fun z => {proposition(f'z + {following}')}) n "
                f"(fun _ => rfl) {succ_branch(following)})")

    bodies.append(f"exact Nat.casesOn (motive := fun y => {proposition('y')}) x (fun _ => rfl) {succ_branch(0)} h")
    return bodies


def refutation_body(contract, witness, left, right):
    """A policy-admissible refutation at a concrete witness."""
    def contradiction(equation):
        if left < right:
            return (f"Nat.lt_irrefl {left} (Eq.ndrec (motive := fun y => {left} < y) "
                    f"(Nat.le_of_ble_eq_true rfl : {left} < {right}) (Eq.symm ({equation} : {left} = {right})))")
        return (f"Nat.lt_irrefl {right} (Eq.ndrec (motive := fun y => {right} < y) "
                f"(Nat.le_of_ble_eq_true rfl : {right} < {left}) ({equation} : {left} = {right}))")
    pre = contract.get("precondition")
    if pre is None:
        return f"exact ⟨fun h => {contradiction(f'h {witness}')}, fun hw => {contradiction('hw')}⟩"
    holds = "rfl" if pre["op"] == "=" else "(Nat.le_of_ble_eq_true rfl)"
    return (f"exact ⟨fun h => {contradiction(f'h {witness} {holds}')}, "
            f"⟨{holds}, fun hw => {contradiction('hw')}⟩⟩")


def positive_job(candidate, contract):
    return {"candidate": candidate, "contract": corpus.contract_bytes(contract).decode(),
            "bodies": positive_bodies(contract), "validate": True}


def refutation_job(candidate, contract):
    holds, witness = oracle.judge(candidate, contract)
    if holds:
        raise ValueError("cannot refute a property that holds")
    left = oracle.evaluate(oracle.polynomial(oracle.candidate_expression(candidate)), witness)
    right = oracle.evaluate(oracle.polynomial(contract["rhs"]), witness)
    return {"candidate": candidate, "contract": corpus.contract_bytes(contract).decode(), "claim": "violated",
            "witness": witness, "bodies": [refutation_body(contract, witness, left, right)], "validate": True}


def evidence_plan(package, prop, spec, head_text):
    """Return (job, post) for one evidence slot, or (None, None) when absent."""
    base = package["candidates"]["base"]
    contract = prop["contract"]
    if spec is None or spec == "missing":
        return None, None
    if spec == "fresh":
        return positive_job(head_text, contract), None
    if spec == "stale":
        return positive_job(base, contract), None
    if spec == "refute":
        return refutation_job(head_text, contract), None
    kind = spec["forge"]
    if kind == "mutated_contract":
        return positive_job(head_text, spec["contract"]), None
    if kind == "shadow_source":
        return positive_job(package["candidates"]["shadow"], contract), None
    if kind in ("custom_axiom", "sorry", "indirect_axiom", "weakened_statement", "shadow_definition"):
        if kind == "shadow_definition" and "precondition" in contract:
            raise ValueError("shadow definition forgery requires an unconditional property")
        solution = SOLUTIONS[kind].replace("{rhs}", contract["rhs"])
        return {"candidate": head_text, "contract": corpus.contract_bytes(contract).decode(),
                "solution": solution, "allow_forbidden": True}, None
    if kind == "candidate_digest":
        return positive_job(base, contract), {"manifest": {"candidate_sha256": sha(head_text.encode())}}
    if kind == "flipped_claim":
        return refutation_job(head_text, contract), {"manifest": {"claimed_decision": "verified"}, "drop": ["witness"]}
    if kind == "tampered_witness":
        return refutation_job(head_text, contract), {"manifest": {"witness": spec["witness"]}}
    if kind == "edited_solution":
        return positive_job(base, contract), {"solution": EDITED_SOLUTION}
    if kind == "replayed_refutation":
        return refutation_job(package["candidates"]["violating"], contract), None
    if kind == "extra_file":
        holds, _ = oracle.judge(head_text, contract)
        return positive_job(head_text if holds else base, contract), {"extra": {"notes.txt": b"reviewer notes\n"}}
    if kind == "malformed_manifest":
        return positive_job(base, contract), {"replace_manifest": b"{not json"}
    raise ValueError("unknown evidence kind " + kind)


class EvidenceCache:
    """Content-addressed store of bundles built by the pinned image."""

    def __init__(self, root, image_id):
        self.root = Path(root)
        self.root.mkdir(parents=True, exist_ok=True)
        self.image_id = image_id
        self.builder = sha((HERE / "build_evidence.py").read_bytes())
        self.reused = 0
        self.built = 0
        self.build_seconds = 0.0
        self.built_keys = set()

    def key(self, job):
        material = json.dumps({"job": job, "image": self.image_id, "builder": self.builder}, sort_keys=True)
        return sha(material.encode())

    def path(self, job):
        return self.root / self.key(job)

    def ensure(self, jobs):
        pending = {}
        for job in jobs:
            key = self.key(job)
            if (self.root / key / "manifest.json").is_file():
                continue
            pending[key] = job
        self.reused += len({self.key(job) for job in jobs}) - len(pending)
        if not pending:
            return
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix="proofci-eval-jobs-") as temp:
            temp = Path(temp)
            os.chmod(temp, 0o755)
            (temp / "jobs.json").write_text(json.dumps(pending))
            out = temp / "out"
            out.mkdir(mode=0o777)
            os.chmod(out, 0o777)
            command = ["docker", "run", "--rm", "--network", "none", "--platform", "linux/arm64",
                       "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
                       "--security-opt", "seccomp=unconfined", "--security-opt", "systempaths=unconfined",
                       "--user", f"{os.getuid()}:{os.getgid()}", "--read-only", "--memory", "2g", "--cpus", "1",
                       "--tmpfs", "/tmp:rw,size=2g,mode=1777",
                       "--mount", f"type=bind,src={HERE / 'build_evidence.py'},dst=/eval/build_evidence.py,readonly",
                       "--mount", f"type=bind,src={temp / 'jobs.json'},dst=/eval/jobs.json,readonly",
                       "--mount", f"type=bind,src={out},dst=/out",
                       "--entrypoint", "python3", self.image_id, "/eval/build_evidence.py", "/eval/jobs.json", "/out"]
            subprocess.run(command, check=True, stdout=subprocess.DEVNULL, timeout=60 + 150 * len(pending))
            results = json.loads((out / "build-results.json").read_text())
            built = [key for key in pending if results.get(key, {}).get("status") == "built"]
            for key in built:
                destination = self.root / key
                if destination.exists():
                    shutil.rmtree(destination)
                shutil.copytree(out / key, destination)
            self.built += len(built)
            self.built_keys.update(built)
            self.build_seconds += time.monotonic() - started
            failed = {key: results.get(key, {"status": "missing"}) for key in pending if key not in built}
            if failed:
                raise RuntimeError("evidence construction failed: " + json.dumps(failed)[:4000])

    def materialize(self, job, post):
        files = {p.name: p.read_bytes() for p in sorted(self.path(job).iterdir())}
        if not post:
            return files
        if "manifest" in post or "drop" in post:
            manifest = json.loads(files["manifest.json"])
            manifest.update(post.get("manifest", {}))
            for name in post.get("drop", ()):
                manifest.pop(name, None)
            files["manifest.json"] = json.dumps(manifest, sort_keys=True).encode()
        if "solution" in post:
            files["solution.lean"] = post["solution"]
            manifest = json.loads(files["manifest.json"])
            manifest["solution_sha256"] = sha(post["solution"])
            files["manifest.json"] = json.dumps(manifest, sort_keys=True).encode()
        if "replace_manifest" in post:
            files["manifest.json"] = post["replace_manifest"]
        files.update(post.get("extra", {}))
        return files


# ---------------------------------------------------------------------------
# Scenario construction

def manifest_for(package, props):
    contracts = []
    for prop in props:
        contracts.append({"id": prop["id"], "explanation": prop["explanation"], "owner": APPROVER,
                          "formal_statement": prop["contract"]["rhs"], "assumptions": [],
                          "specification_closure": [], "implementation_bindings": ["target"],
                          "policy": "required", "evidence": "proofs/" + prop["id"]})
    return {"version": 1, "candidate": corpus.CANDIDATE, "contracts": contracts}


def encode_manifest(manifest):
    return (json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode()


class Scenario:
    def __init__(self, spec, packages):
        self.spec = spec
        self.id = spec["id"]
        self.category = spec["category"]
        self.package = packages[spec["package"]]
        known = {p["id"]: p for p in self.package["properties"]}
        self.props = [known[p] for p in corpus.properties(self.package, spec)]
        self.head_text = corpus.head_candidate(self.package, spec)
        self.base_text = self.package["candidates"]["base"]
        self.store = spec.get("store")
        self.assisted = spec.get("assisted", True) and self.store is None

    def plans(self):
        """Evidence slots for the base and head commits."""
        base = {f"proofs/{p['id']}": evidence_plan(self.package, p, "fresh", self.base_text) for p in self.props}
        head = {}
        for p in self.props:
            for slot, folder in (("evidence", "proofs"), ("refutation", "refutations")):
                spec = corpus.spec_for(self.spec["head"].get(slot), p["id"])
                job, post = evidence_plan(self.package, p, spec, self.head_text)
                if job is not None:
                    head[f"{folder}/{p['id']}"] = (job, post)
        return base, head

    def jobs(self):
        base, head = self.plans()
        return [job for job, _ in list(base.values()) + list(head.values())]

    def trees(self, cache):
        base_plans, head_plans = self.plans()
        base = {corpus.CANDIDATE: self.base_text.encode()}
        for folder, (job, post) in base_plans.items():
            for name, data in cache.materialize(job, post).items():
                base[f"{folder}/{name}"] = data
        if self.store is not None:
            base[corpus.MANIFEST] = encode_manifest(manifest_for(self.package, self.props))
        head = {path: data for path, data in base.items() if not path.startswith(("proofs/", "refutations/"))}
        head[corpus.CANDIDATE] = self.head_text.encode()
        for folder, (job, post) in head_plans.items():
            for name, data in cache.materialize(job, post).items():
                head[f"{folder}/{name}"] = data
        for path, value in self.spec["head"].get("files", {}).items():
            if value == "shadow":
                head[path] = self.package["candidates"]["shadow"].encode()
            elif value == "companion":
                head[path] = (self.package["root"] / self.package["companion"]["path"]).read_bytes()
            else:
                head[path] = value.encode()
        if self.store is not None:
            head[corpus.MANIFEST] = self.changed_manifest(base[corpus.MANIFEST])
            if head[corpus.MANIFEST] is None:
                del head[corpus.MANIFEST]
        return base, head

    def changed_manifest(self, original):
        change = self.store["manifest"]
        manifest = json.loads(original)
        if change["kind"] == "unchanged":
            return original
        if change["kind"] == "delete":
            return None
        if change["kind"] == "change":
            for item in manifest["contracts"]:
                if item["id"] == change["id"]:
                    item["formal_statement"] = change["formal_statement"]
        elif change["kind"] == "remove":
            manifest["contracts"] = [c for c in manifest["contracts"] if c["id"] != change["id"]]
        elif change["kind"] == "rebind":
            manifest["candidate"] = change["candidate"]
        else:
            raise ValueError("unknown manifest change")
        return encode_manifest(manifest)

    def baseline(self, protected):
        obligations = []
        for prop in self.props:
            name = f"contracts/{prop['id']}.json"
            data = corpus.contract_bytes(prop["contract"])
            (protected / name).parent.mkdir(parents=True, exist_ok=True)
            (protected / name).write_bytes(data)
            item = {"id": prop["id"], "policy": "required", "contract": name, "contract_sha256": sha(data),
                    "evidence": "proofs/" + prop["id"]}
            if self.spec["head"].get("refutation"):
                item["refutation"] = "refutations/" + prop["id"]
            obligations.append(item)
        data = json.dumps({"version": 1, "candidate": corpus.CANDIDATE, "obligations": obligations},
                          indent=2, sort_keys=True).encode()
        (protected / "baseline.json").write_bytes(data)
        return sha(data)


def git(repo, *args, capture=True):
    env = {**os.environ, **GIT_IDENTITY}
    result = subprocess.run(["git", "-C", str(repo), *args], env=env, check=True,
                            stdout=subprocess.PIPE if capture else subprocess.DEVNULL, text=True)
    return result.stdout.strip() if capture else None


def write_tree(repo, tree):
    for entry in repo.iterdir():
        if entry.name == ".git":
            continue
        shutil.rmtree(entry) if entry.is_dir() else entry.unlink()
    for path, data in tree.items():
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)


def make_repo(repo, base_tree, head_tree, untracked=None):
    repo.mkdir(parents=True)
    git(repo, "init", "-q", "-b", "main")
    git(repo, "remote", "add", "origin", REPOSITORY)
    write_tree(repo, base_tree)
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", "base")
    base = git(repo, "rev-parse", "HEAD")
    write_tree(repo, head_tree)
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "--allow-empty", "-m", "head")
    head = git(repo, "rev-parse", "HEAD")
    for path, text in (untracked or {}).items():
        (repo / path).write_text(text)
    return base, head


def envelope(repo, base, head, baseline_digest, policy):
    candidate = repo / corpus.CANDIDATE
    return {"version": 1, "repository": REPOSITORY, "head": head, "base": base,
            "candidate_sha256": sha(candidate.read_bytes()), "baseline_sha256": baseline_digest,
            "dependency": proofci.digest(proofci.VALIDATOR / "core-dependencies.json"),
            "toolchain": proofci.TOOLCHAIN_SHA256, "trust_policy": proofci.policy_digest(),
            "resource_policy": policy}


# ---------------------------------------------------------------------------
# Execution

def run_command(command, timeout=COMMAND_TIMEOUT):
    started = time.monotonic()
    try:
        process = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        status, stderr = process.returncode, process.stderr.decode(errors="replace")[-2000:]
    except subprocess.TimeoutExpired:
        status, stderr = 2, "evaluation command timeout"
    return status, time.monotonic() - started, stderr


def read_report(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return {"status": "error", "reason": "report missing or unreadable"}


def active_digest(store):
    with sqlite3.connect(store) as db:
        row = db.execute("SELECT a.digest, r.revision FROM active a, active_revision r WHERE a.id=1 AND r.id=1").fetchone()
    return None if row is None else {"digest": row[0], "revision": row[1]}


class PersistenceStore:
    """One reviewed activation shared by persistence scenarios with the same base commit."""

    def __init__(self, root):
        self.root = root
        self.templates = {}
        self.activation = {}

    def template(self, scenario, cache):
        base_tree, _ = scenario.trees(cache)
        key = sha(json.dumps(sorted((p, sha(d)) for p, d in base_tree.items())).encode())
        if key in self.templates:
            return self.templates[key]
        work = self.root / ("template-" + key[:12])
        repo = work / "snapshot"
        base, _ = make_repo(repo, base_tree, base_tree)
        git(repo, "reset", "-q", "--hard", base)
        store = work / "store" / "baselines.db"
        store.parent.mkdir(parents=True)
        env_path = work / "envelope.json"
        env_path.write_text(json.dumps(envelope(repo, base, base, "0" * 64, RESOURCE_POLICY)))
        manifest = (repo / corpus.MANIFEST).read_bytes()
        status, seconds, stderr = run_command([sys.executable, str(PORTABLE / "baselines.py"), "activate",
                                               "--store", str(store), "--snapshot", str(repo),
                                               "--envelope", str(env_path), "--report", str(work / "activation.json"),
                                               "--manifest-path", corpus.MANIFEST, "--reviewed-sha256", sha(manifest),
                                               "--approver", APPROVER])
        if status != 0:
            raise RuntimeError(f"persistence baseline activation failed ({status}): {stderr}")
        self.templates[key] = (store, base, active_digest(store))
        self.activation[key] = {"seconds": seconds, "digest": active_digest(store)}
        return self.templates[key]


def run_scenario(scenario, mode, repetition, cache, workdir, stores, model_profile, keep, assisted_runner=None):
    """Run one scenario. `assisted_runner` lets tests supply an in-process broker."""
    root = Path(tempfile.mkdtemp(prefix=f"{scenario.id}-{mode}-{repetition}-", dir=workdir))
    try:
        base_tree, head_tree = scenario.trees(cache)
        repo = root / "snapshot"
        base, head = make_repo(repo, base_tree, head_tree, scenario.spec["head"].get("untracked"))
        protected = root / "protected"
        protected.mkdir()
        policy = {**RESOURCE_POLICY, **scenario.spec.get("resource_policy", {})}
        report_path = root / "report.json"
        env_path = root / "envelope.json"
        store_before = store_after = None
        if scenario.store is not None:
            template, template_base, store_before = stores.template(scenario, cache)
            if template_base != base:
                raise RuntimeError("persistence scenario base differs from its activated baseline")
            store = root / "store" / "baselines.db"
            store.parent.mkdir()
            shutil.copyfile(template, store)
            env_path.write_text(json.dumps(envelope(repo, base, head, "0" * 64, policy)))
            if scenario.store["action"] == "activate":
                manifest = (repo / corpus.MANIFEST).read_bytes()
                command = [sys.executable, str(PORTABLE / "baselines.py"), "activate", "--store", str(store),
                           "--snapshot", str(repo), "--envelope", str(env_path), "--report", str(report_path),
                           "--manifest-path", corpus.MANIFEST, "--reviewed-sha256", sha(manifest),
                           "--approver", APPROVER]
            else:
                command = [sys.executable, str(PORTABLE / "baselines.py"), "run", "--store", str(store),
                           "--snapshot", str(repo), "--envelope", str(env_path), "--report", str(report_path)]
        else:
            digest = scenario.baseline(protected)
            env_path.write_text(json.dumps(envelope(repo, base, head, digest, policy)))
            artifacts = root / "artifacts"
            artifacts.mkdir()
            command = [sys.executable, str(PORTABLE / "assist.py"), "--envelope", str(env_path),
                       "--baseline", str(protected / "baseline.json"), "--snapshot", str(repo),
                       "--report", str(report_path), "--artifacts", str(artifacts)]
            if mode == "assisted":
                config = dict(model_profile)
                config.update(repository=REPOSITORY, run_id=str(uuid.uuid4()), head=head,
                              baseline_sha256=digest)
                config_path = root / "model-config.json"
                config_path.write_text(json.dumps(config))
                command += ["--model-config", str(config_path)]
        if mode == "assisted" and assisted_runner is not None:
            started = time.monotonic()
            status = assisted_runner(envelope_path=env_path, baseline_path=protected / "baseline.json",
                                     snapshot=repo, report_path=report_path, artifacts=root / "artifacts",
                                     config=config)
            seconds, stderr = time.monotonic() - started, ""
        else:
            status, seconds, stderr = run_command(command)
        report = read_report(report_path)
        if scenario.store is not None:
            store_after = active_digest(store)
        return record(scenario, mode, repetition, status, seconds, report, stderr, store_before, store_after,
                      base, head, cache)
    finally:
        if not keep:
            shutil.rmtree(root, ignore_errors=True)


TIMED_OUT = re.compile(r"timed out after [0-9.]+ seconds")
HOST_PATH = re.compile(r"(?:/[^\s'\"\],]+)+")


def normalize_reason(reason):
    """Classify a run-level reason without host paths so it can be counted and compared."""
    if not reason:
        return reason
    if TIMED_OUT.search(reason):
        return "timeout"
    return HOST_PATH.sub("<path>", reason)


def summarize_usage(report):
    usage = report.get("usage") or {}
    requests = usage.get("requests") or []
    final = {}
    for event in requests:
        final[event.get("request_id")] = event
    uncertain = [e for e in final.values() if e.get("state") in ("uncertain", "reserved")]
    settled = [e for e in final.values() if e.get("state") == "settled"]
    return {"model_calls": usage.get("model_calls", 0),
            "input_tokens": sum(e.get("input_tokens", 0) for e in settled),
            "output_tokens": sum(e.get("output_tokens", 0) for e in settled),
            "settled_cost_micros": sum(e.get("cost_micros", 0) for e in settled),
            "uncertain_requests": len(uncertain),
            "uncertain_reserved_cost_micros": sum(e.get("cost_micros", 0) for e in uncertain),
            "report_elapsed_seconds": usage.get("elapsed_seconds")}


def record(scenario, mode, repetition, status, seconds, report, stderr, store_before, store_after, base, head, cache):
    expect = scenario.spec["expect"]
    truths = {}
    for prop in scenario.props:
        try:
            truths[prop["id"]] = oracle.judge(scenario.head_text, prop["contract"])[0]
        except ValueError:
            truths[prop["id"]] = None  # Outside the admitted language: no property can be verified.
    results = []
    for item in report.get("results") or []:
        suggestion = item.get("proof_suggestion")
        repaired_by = None
        if item.get("decision") == "verified" and suggestion is not None:
            repaired_by = "fixed_tactic" if suggestion in aggregate.FIXED_TACTICS else "model"
        attempted = (item.get("decision") != "verified" and item.get("reason") in
                     ("missing_evidence", "invalid_evidence", "proof_failed", "unproven", "search_exhausted")
                     and report.get("status") in ("passed", "blocked"))
        results.append({"id": item.get("id"), "decision": item.get("decision"), "reason": item.get("reason"),
                        "repair_reason": item.get("repair_reason"), "repaired_by": repaired_by,
                        "repair_attempted": attempted or repaired_by is not None,
                        "elapsed_seconds": item.get("elapsed_seconds"), "truth": truths.get(item.get("id"))})
    false_acceptances, false_rejections = [], []
    for r in results:
        if r["decision"] == "verified" and r["truth"] is not True:
            false_acceptances.append({"kind": "false_verified", "obligation": r["id"],
                                      "detail": "verified a property that does not hold for the head target"})
        if r["decision"] == "violated" and r["truth"] is not False:
            false_rejections.append({"kind": "false_violated", "obligation": r["id"]})
    if status == 0 and 0 not in expect["exit"]:
        false_acceptances.append({"kind": "false_passing_gate", "detail": "public exit 0 where the scenario forbids a pass"})
    if status == 0 and any(t is not True for t in truths.values()):
        false_acceptances.append({"kind": "false_passing_gate", "detail": "public exit 0 with a false required property"})
    if store_before is not None and store_after != store_before:
        false_acceptances.append({"kind": "baseline_replaced", "detail": f"{store_before} -> {store_after}"})
    failures = []
    if status not in expect["exit"]:
        failures.append(f"exit {status} not in {expect['exit']}")
    if status in (0, 1):
        # A completed run must report every registered obligation.
        by_id = {r["id"]: r for r in results}
        for prop in scenario.props:
            r = by_id.get(prop["id"])
            if r is None:
                failures.append(f"{prop['id']}: missing result")
                continue
            if mode != "deterministic":
                continue
            allowed = corpus.spec_for(expect.get("decisions"), prop["id"])
            reasons = corpus.spec_for(expect.get("reasons"), prop["id"])
            if allowed and r["decision"] not in allowed:
                failures.append(f"{prop['id']}: decision {r['decision']} not in {allowed}")
            elif reasons and r["decision"] != "verified" and r["reason"] not in reasons:
                failures.append(f"{prop['id']}: reason {r['reason']} not in {reasons}")
    run_reason = normalize_reason(report.get("reason"))
    if "run_reason" in expect and not any(text in (run_reason or "") for text in expect["run_reason"]):
        failures.append(f"run reason {run_reason!r} does not match {expect['run_reason']}")
    coverage = report.get("coverage") or {}
    cov = {"unsupported_changed_code": len(coverage.get("unsupported_changed_code") or []),
           "uncovered_supported_symbols": len(coverage.get("uncovered_supported_symbols") or []),
           "unsupported_paths": [item.get("path") for item in coverage.get("unsupported_changed_code") or []]}
    for key in ("unsupported_changed_code", "uncovered_supported_symbols"):
        if key in expect and cov[key] != expect[key]:
            failures.append(f"{key} {cov[key]} != {expect[key]}")
    proposed = [item.get("kind") for item in report.get("proposed_guarantee_changes") or []]
    if "proposed_changes" in expect and not set(expect["proposed_changes"]) <= set(proposed):
        failures.append(f"proposed changes {proposed} do not include {expect['proposed_changes']}")
    if mode == "assisted":
        # Assistance may legitimately repair more obligations; only soundness is enforced.
        failures = [f for f in failures if not f.startswith("exit ") or status == 0]
    if false_acceptances:
        failures.append("false acceptance")
    keys = [cache.key(job) for job in scenario.jobs()]
    return {"scenario": scenario.id, "category": scenario.category, "package": scenario.package["name"],
            "mode": mode, "repetition": repetition, "temperature": "cold" if repetition == 1 else "warm",
            "evidence_cache": "built_this_invocation" if any(k in cache.built_keys for k in keys) else "reused",
            "base": base, "head": head, "exit": status, "wall_seconds": seconds, "status": report.get("status"),
            "run_reason": run_reason, "stderr_tail": stderr if status == 2 else "", "results": results,
            "coverage": cov, "proposed_changes": proposed, "usage": summarize_usage(report),
            "active_baseline": {"before": store_before, "after": store_after} if store_before else None,
            "false_acceptances": false_acceptances, "false_rejections": false_rejections,
            "expectation": {"met": not failures, "failures": failures}}


# ---------------------------------------------------------------------------
# Environment identity

def command_output(command):
    try:
        return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                              timeout=30).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return None


def memory_bytes():
    if sys.platform == "darwin":
        value = command_output(["sysctl", "-n", "hw.memsize"])
        return int(value) if value and value.isdecimal() else None
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal:"):
                return int(line.split()[1]) * 1024
    except OSError:
        return None
    return None


def environment(cache, image_id):
    sys.path.insert(0, str(proofci.VALIDATOR))
    import binding
    docker = command_output(["docker", "info", "--format",
                             "{{.ServerVersion}} {{.OperatingSystem}} {{.Architecture}} cpus={{.NCPU}} mem={{.MemTotal}}"])
    status = command_output(["git", "-C", str(REPO), "status", "--porcelain"])
    return {
        "platform": platform.platform(), "machine": platform.machine(),
        "processor": platform.processor() or command_output(["sysctl", "-n", "machdep.cpu.brand_string"]),
        "cpu_count": os.cpu_count(), "memory_bytes": memory_bytes(), "python": sys.version.split()[0],
        "docker": docker, "git": command_output(["git", "--version"]),
        "container_limits": "verifier container: 1 CPU, memory and process limits from the envelope resource policy",
        "verifier": {
            "commit": command_output(["git", "-C", str(REPO), "rev-parse", "HEAD"]),
            "dirty": bool(status),
            "image_id": image_id,
            "toolchain_sha256": proofci.TOOLCHAIN_SHA256,
            "dependency_sha256": proofci.digest(proofci.VALIDATOR / "core-dependencies.json"),
            "trust_policy_sha256": proofci.policy_digest(),
            "bubblewrap_sha256": proofci.BWRAP_SHA256,
            "lean_commit": binding.LEAN_COMMIT,
            "builder_sha256": cache.builder,
            "resource_policy": RESOURCE_POLICY,
        },
        "cache": {"bundles_reused": cache.reused, "bundles_built": cache.built, "build_seconds": cache.build_seconds,
                  "directory_entries": sum(1 for _ in cache.root.iterdir()),
                  "note": "evidence construction is preparation outside measured latency; the verifier keeps no proof cache"},
        "temperature_definition": TEMPERATURE,
    }


# ---------------------------------------------------------------------------
# Commands

def load_profile(path):
    profile = proofci.parse_json(Path(path).read_bytes())
    allowed = {"model", "limits", "authorized", "private", "private_source_consent"}
    if not {"model", "limits", "authorized"} <= set(profile) or set(profile) - allowed:
        raise ValueError("model profile needs model, limits and authorized, and only consent fields besides")
    return profile


def assisted_status(args):
    if args.mode == "deterministic":
        return {"status": "not_requested", "reason": "deterministic mode only"}, None
    if args.model_profile is None:
        return {"status": "not_measured", "reason": "no model profile was supplied"}, None
    if not os.environ.get("PROOFCI_OPENAI_API_KEY"):
        return {"status": "not_measured", "reason": "PROOFCI_OPENAI_API_KEY is not set in the control process"}, None
    profile = load_profile(args.model_profile)
    return {"status": "measured", "reason": f"model {profile['model']}"}, profile


def command_run(args):
    packages, scenarios = corpus.load()
    problems = corpus.check(packages, scenarios)
    lock, lock_problems = corpus.verify_lock()
    if problems or lock_problems:
        for problem in problems + lock_problems:
            print(problem, file=sys.stderr)
        return 2
    selected = [s for s in scenarios if not args.scenario or s["id"] in args.scenario]
    if args.scenario and len(selected) != len(set(args.scenario)):
        print("unknown scenario requested", file=sys.stderr)
        return 2
    status_info, profile = assisted_status(args)
    modes = ["deterministic"] + (["assisted"] if profile is not None else [])
    image_id = command_output(["docker", "image", "inspect", "--format", "{{.Id}}", IMAGE_ID])
    if image_id != IMAGE_ID:
        print("the pinned verifier image is not available", file=sys.stderr)
        return 2
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cache_dir = args.cache.resolve()
    if args.clear_cache and cache_dir.exists():
        shutil.rmtree(cache_dir)
    cache = EvidenceCache(cache_dir, image_id)
    objects = [Scenario(spec, packages) for spec in selected]
    started_at = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    print(f"preparing evidence for {len(objects)} scenarios", file=sys.stderr, flush=True)
    jobs = {cache.key(job): job for scenario in objects for job in scenario.jobs()}
    cache.ensure(list(jobs.values()))
    workdir = Path(tempfile.mkdtemp(prefix="proofci-evaluation-", dir=args.workdir))
    runs = []
    try:
        stores = PersistenceStore(workdir)
        for repetition in range(1, args.repetitions + 1):
            for scenario in objects:
                for mode in modes:
                    if mode == "assisted" and not scenario.assisted:
                        continue
                    print(f"[{repetition}/{args.repetitions}] {mode} {scenario.id}", file=sys.stderr, flush=True)
                    run = run_scenario(scenario, mode, repetition, cache, workdir, stores, profile, args.keep_workdirs)
                    print(f"    exit {run['exit']} in {run['wall_seconds']:.1f}s; expectation "
                          f"{'met' if run['expectation']['met'] else 'NOT MET: ' + '; '.join(run['expectation']['failures'])}",
                          file=sys.stderr, flush=True)
                    runs.append(run)
                    (output / "runs.partial.json").write_text(json.dumps(runs, indent=1))
    finally:
        if not args.keep_workdirs:
            shutil.rmtree(workdir, ignore_errors=True)
    complete = not args.scenario and args.repetitions >= 2
    total_props = sum(len(p["properties"]) for p in packages.values())
    evaluation = {
        "version": 1,
        "started_at": started_at,
        "finished_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "command": " ".join([Path(sys.argv[0]).name] + sys.argv[1:]),
        "repetitions": args.repetitions,
        "corpus": {"corpus_sha256": lock["corpus_sha256"], "frozen_at": lock["frozen_at"],
                   "reviewer": lock["reviewer"], "properties": total_props,
                   "packages": {name: {"domain": p["domain"], "properties": len(p["properties"])}
                                for name, p in packages.items()},
                   "scenarios_total": len(scenarios), "scenarios_run": len(selected),
                   "selected": [s["id"] for s in selected] if args.scenario else "all"},
        "environment": environment(cache, image_id),
        "persistence_activations": stores.activation,
    }
    evaluation["summary"] = aggregate.summarize(runs, complete=complete, modes=modes, assisted_status=status_info,
                                                soundness=corpus.SOUNDNESS, persistence=corpus.PERSISTENCE)
    evaluation["runs"] = runs
    (output / "evaluation.json").write_text(json.dumps(evaluation, indent=2, sort_keys=True) + "\n")
    (output / "evaluation.md").write_text(aggregate.markdown(evaluation))
    (output / "runs.partial.json").unlink(missing_ok=True)
    release = evaluation["summary"]["release"]
    print(f"false acceptances: {release['false_acceptances']}; expectations met: "
          f"{release['deterministic_expectations_met']}; release blocked: {release['blocked']}", file=sys.stderr)
    return 1 if release["blocked"] else 0


def command_check(_args):
    packages, scenarios = corpus.load()
    problems = corpus.check(packages, scenarios)
    _, lock_problems = corpus.verify_lock()
    for problem in problems + lock_problems:
        print(problem)
    total = sum(len(p["properties"]) for p in packages.values())
    print(f"{total} properties, {len(packages)} packages, {len(scenarios)} scenarios; "
          f"{'frozen' if not lock_problems else 'not frozen'}; {'ok' if not problems else 'invalid'}")
    return 0 if not problems and not lock_problems else 1


def command_freeze(args):
    packages, scenarios = corpus.load()
    problems = corpus.check(packages, scenarios)
    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        return 1
    lock, lock_problems = corpus.verify_lock()
    if lock is not None and lock_problems and not args.replace:
        print("the corpus differs from its existing lock; pass --replace to record a new freeze. "
              "Earlier results are not comparable with the new corpus.", file=sys.stderr)
        return 1
    lock = corpus.freeze(args.frozen_at, args.reviewer)
    print(lock["corpus_sha256"])
    return 0


def command_render(args):
    evaluation = json.loads(args.input.read_text())
    args.output.write_text(aggregate.markdown(evaluation))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check")
    freeze = sub.add_parser("freeze")
    freeze.add_argument("--reviewer", required=True)
    freeze.add_argument("--frozen-at", default=datetime.date.today().isoformat())
    freeze.add_argument("--replace", action="store_true")
    run = sub.add_parser("run")
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--mode", choices=("deterministic", "both"), default="both")
    run.add_argument("--repetitions", type=int, default=2)
    run.add_argument("--model-profile", type=Path)
    run.add_argument("--scenario", action="append")
    run.add_argument("--cache", type=Path, default=Path.home() / ".cache" / "proofci-evaluation")
    run.add_argument("--clear-cache", action="store_true")
    run.add_argument("--workdir", type=Path)
    run.add_argument("--keep-workdirs", action="store_true")
    render = sub.add_parser("render")
    render.add_argument("--input", type=Path, required=True)
    render.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "run" and args.repetitions < 1:
        parser.error("--repetitions must be positive")
    try:
        return {"check": command_check, "freeze": command_freeze, "run": command_run,
                "render": command_render}[args.command](args)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"evaluation failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
