#!/usr/bin/env python3
"""Activate and run reviewed contracts from a protected local baseline store."""
import argparse
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile

import proofci
from container import IMAGE_ID

HERE = Path(__file__).resolve().parent


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def nonempty(value):
    return isinstance(value, str) and bool(value.strip())


def parse_manifest(data, *, supported=True):
    manifest = proofci.parse_json(data)
    proofci.fields(manifest, ("version", "candidate", "contracts"))
    if type(manifest["version"]) is not int or manifest["version"] != 1:
        raise ValueError("unsupported manifest version")
    if not nonempty(manifest["candidate"]) or not isinstance(manifest["contracts"], list) or not manifest["contracts"]:
        raise ValueError("invalid candidate or empty contracts")
    seen = set()
    for item in manifest["contracts"]:
        proofci.fields(item, ("id", "explanation", "owner", "formal_statement", "assumptions", "specification_closure", "implementation_bindings", "policy", "evidence"))
        if not all(nonempty(item[k]) for k in ("id", "explanation", "owner", "formal_statement", "evidence")):
            raise ValueError("missing contract field")
        if item["id"] in seen:
            raise ValueError("duplicate contract ID")
        seen.add(item["id"])
        if item["policy"] not in ("required", "advisory"):
            raise ValueError("invalid policy")
        # These are the complete supported semantics of the current source adapter.
        if not all(isinstance(item[k], list) for k in ("assumptions", "specification_closure", "implementation_bindings")):
            raise ValueError("invalid contract dependencies")
        if supported and (item["assumptions"] != [] or item["specification_closure"] != [] or item["implementation_bindings"] != ["target"]):
            raise ValueError("unsupported assumptions, specification closure, or implementation bindings")
    if supported and not any(c["policy"] == "required" for c in manifest["contracts"]):
        raise ValueError("at least one required contract is needed")
    return manifest


def materialize(manifest, root):
    obligations = []
    for index, item in enumerate(manifest["contracts"]):
        data = encoded({"rhs": item["formal_statement"]})
        name = f"contract-{index}.json"
        (root / name).write_bytes(data)
        obligations.append({"id": item["id"], "policy": item["policy"], "contract": name,
                            "contract_sha256": sha(data), "evidence": item["evidence"]})
    baseline = encoded({"version": 1, "candidate": manifest["candidate"], "obligations": obligations})
    (root / "baseline.json").write_bytes(baseline)
    return sha(baseline)


def open_store(path):
    db = sqlite3.connect(path, timeout=30)
    try:
        db.executescript("""BEGIN IMMEDIATE;
        CREATE TABLE IF NOT EXISTS baselines (
        digest TEXT PRIMARY KEY, manifest BLOB NOT NULL, manifest_path TEXT NOT NULL,
        baseline_sha256 TEXT NOT NULL, repository TEXT NOT NULL, initial_head TEXT NOT NULL,
        approval_identity TEXT NOT NULL, approval_source TEXT NOT NULL, report BLOB NOT NULL,
        created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP);
        CREATE TABLE IF NOT EXISTS active (id INTEGER PRIMARY KEY CHECK(id=1), digest TEXT NOT NULL REFERENCES baselines(digest));
        CREATE TABLE IF NOT EXISTS active_revision (id INTEGER PRIMARY KEY CHECK(id=1), revision INTEGER NOT NULL);
        INSERT OR IGNORE INTO active_revision(id, revision) SELECT 1, CASE WHEN EXISTS(SELECT 1 FROM active WHERE id=1) THEN 1 ELSE 0 END;
        CREATE TRIGGER IF NOT EXISTS active_revision_insert AFTER INSERT ON active BEGIN
            UPDATE active_revision SET revision=revision+1 WHERE id=1;
        END;
        CREATE TRIGGER IF NOT EXISTS active_revision_update AFTER UPDATE OF digest ON active WHEN OLD.digest IS NOT NEW.digest BEGIN
            UPDATE active_revision SET revision=revision+1 WHERE id=1;
        END;
        CREATE TRIGGER IF NOT EXISTS active_revision_delete AFTER DELETE ON active BEGIN
            UPDATE active_revision SET revision=revision+1 WHERE id=1;
        END;
        COMMIT;""")
    except Exception:
        db.rollback()
        db.close()
        raise
    return db


def lookup(db, digest=None):
    db.row_factory = sqlite3.Row
    if digest is None:
        row = db.execute("SELECT b.* FROM baselines b JOIN active a ON a.digest=b.digest WHERE a.id=1").fetchone()
    else:
        row = db.execute("SELECT * FROM baselines WHERE digest=?", (digest,)).fetchone()
    if row is None:
        raise ValueError("baseline not found")
    result = dict(row)
    if sha(result["manifest"]) != result["digest"]:
        raise ValueError("stored baseline digest mismatch")
    parse_manifest(result["manifest"])
    return result


def snapshot_manifest(snapshot, path):
    snapshot = snapshot.resolve(strict=True)
    target = proofci.path_in(snapshot, path)
    head = subprocess.check_output(["git", "-C", str(snapshot), "rev-parse", "HEAD"], text=True).strip()
    tracked = subprocess.check_output(["git", "-C", str(snapshot), "ls-files", "--error-unmatch", "--", path], text=True).strip()
    if tracked != path:
        raise ValueError("manifest path must be tracked")
    committed = subprocess.check_output(["git", "-C", str(snapshot), "show", head + ":" + path])
    if target.read_bytes() != committed:
        raise ValueError("manifest differs from committed snapshot")
    return committed


def changes(old, new):
    result = []
    if old["candidate"] != new["candidate"]:
        result.append({"kind": "candidate_binding_changed"})
    before = {c["id"]: c for c in old["contracts"]}
    after = {c["id"]: c for c in new["contracts"]}
    for key in sorted(before.keys() | after.keys()):
        if key not in before:
            result.append({"id": key, "kind": "added"})
        elif key not in after:
            result.append({"id": key, "kind": "removed"})
        else:
            fields = [field for field in before[key] if before[key][field] != after[key][field]]
            if fields:
                result.append({"id": key, "kind": "changed", "fields": fields})
    return result


def invoke(snapshot, envelope_path, manifest, report_path):
    with tempfile.TemporaryDirectory(prefix="proofci-baseline-") as directory:
        root = Path(directory)
        digest = materialize(manifest, root)
        envelope = proofci.parse_json(proofci.bounded_read(envelope_path, 1024 * 1024))
        envelope["baseline_sha256"] = digest
        (root / "envelope.json").write_bytes(encoded(envelope))
        status = subprocess.run([sys.executable, str(HERE / "container.py"), "--envelope", str(root / "envelope.json"),
                                 "--baseline", str(root / "baseline.json"), "--snapshot", str(snapshot),
                                 "--report", str(report_path), "--image", IMAGE_ID]).returncode
        report = proofci.parse_json(proofci.bounded_read(report_path, 8 * 1024 * 1024))
        if status == 0 and (report.get("status") != "passed" or report.get("envelope") != envelope):
            raise ValueError("verification report does not match invocation")
        return status, report, digest, envelope


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    initialize = sub.add_parser("initialize", help="initialize or upgrade a protected baseline store")
    initialize.add_argument("--store", type=Path, required=True)
    activate = sub.add_parser("activate")
    for name in ("store", "snapshot", "envelope", "report"):
        activate.add_argument("--" + name, type=Path, required=True)
    for name in ("manifest-path", "reviewed-sha256", "approver"):
        activate.add_argument("--" + name, required=True)
    run = sub.add_parser("run")
    for name in ("store", "snapshot", "envelope", "report"):
        run.add_argument("--" + name, type=Path, required=True)
    inspect = sub.add_parser("lookup")
    inspect.add_argument("--store", type=Path, required=True)
    inspect.add_argument("--digest")
    args = parser.parse_args()
    try:
        with closing(open_store(args.store)) as db:
            if args.command == "initialize":
                return 0
            if args.command == "lookup":
                row = lookup(db, args.digest)
                row["manifest"] = proofci.parse_json(row["manifest"])
                row["report"] = proofci.parse_json(row["report"])
                print(json.dumps(row, indent=2, sort_keys=True))
                return 0
            if args.command == "activate":
                if not nonempty(args.approver) or not re.fullmatch(r"[0-9a-f]{64}", args.reviewed_sha256):
                    raise ValueError("trusted approver and reviewed manifest digest are required")
                data = snapshot_manifest(args.snapshot, args.manifest_path)
                if sha(data) != args.reviewed_sha256:
                    raise ValueError("reviewed digest does not match snapshot")
                manifest = parse_manifest(data)
                status, report, baseline_digest, envelope = invoke(args.snapshot, args.envelope, manifest, args.report)
                if status != 0:
                    return status
                if snapshot_manifest(args.snapshot, args.manifest_path) != data:
                    raise ValueError("reviewed manifest changed during activation")
                # The caller is responsible for authenticating this local approval operation.
                db.execute("BEGIN IMMEDIATE")
                with db:
                    current = db.execute("SELECT digest FROM active WHERE id=1").fetchone()
                    if current is not None and current[0] != sha(data):
                        raise ValueError("active baseline replacement requires an authorized migration")
                    existing = db.execute("SELECT manifest_path, repository, initial_head, approval_identity FROM baselines WHERE digest=?", (sha(data),)).fetchone()
                    identity = (args.manifest_path, envelope["repository"], envelope["head"], args.approver)
                    if existing is not None and existing != identity:
                        raise ValueError("digest already has a different approval record")
                    db.execute("INSERT OR IGNORE INTO baselines(digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES(?,?,?,?,?,?,?,?,?)",
                               (sha(data), data, args.manifest_path, baseline_digest, envelope["repository"], envelope["head"], args.approver, "trusted-local-caller", encoded(report)))
                    db.execute("INSERT INTO active(id,digest) VALUES(1,?) ON CONFLICT(id) DO UPDATE SET digest=excluded.digest", (sha(data),))
                return 0
            row = lookup(db)
            manifest = parse_manifest(row["manifest"])
            status, report, baseline_digest, envelope = invoke(args.snapshot, args.envelope, manifest, args.report)
            if baseline_digest != row["baseline_sha256"] or envelope.get("repository") != row["repository"]:
                raise ValueError("active baseline identity mismatch")
            try:
                proposed = snapshot_manifest(args.snapshot, row["manifest_path"])
                proposed_value = parse_manifest(proposed, supported=False)
                difference = changes(manifest, proposed_value)
            except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError):
                difference = [{"kind": "missing_or_invalid_manifest"}]
            report["reviewed_baseline_sha256"] = row["digest"]
            report["proposed_guarantee_changes"] = difference
            if difference and status == 0:
                status = 1
                report["status"] = "blocked"
            args.report.write_bytes(encoded(report))
            return status
    except (OSError, ValueError, KeyError, TypeError, sqlite3.Error, subprocess.SubprocessError) as error:
        if args.command != "lookup":
            try:
                args.report.write_bytes(encoded({"version": 1, "status": "error", "reason": str(error)}))
            except OSError:
                pass
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
