#!/usr/bin/env python3
"""Trusted service operations for an explicitly authorized baseline migration."""
import argparse
from contextlib import closing
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import signal
import tempfile
import uuid

import baselines
import dispatch
import proofci
import service_baseline
import service_execute


def schema(db):
    db.execute("BEGIN IMMEDIATE")
    try:
        db.execute('''CREATE TABLE IF NOT EXISTS migrations (
            id TEXT PRIMARY KEY, repository TEXT NOT NULL, previous TEXT NOT NULL,
            replacement TEXT NOT NULL, manifest BLOB NOT NULL, manifest_path TEXT NOT NULL,
            head TEXT NOT NULL, actor INTEGER NOT NULL, selection_generation TEXT NOT NULL,
            status TEXT NOT NULL, report BLOB, baseline_sha256 TEXT,
            changes BLOB NOT NULL, created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP)''')
        if 'revision' not in {row[1] for row in db.execute('PRAGMA table_info(active)')}:
            db.execute('ALTER TABLE active ADD COLUMN revision INTEGER NOT NULL DEFAULT 0')
        if 'previous_revision' not in {row[1] for row in db.execute('PRAGMA table_info(migrations)')}:
            db.execute('ALTER TABLE migrations ADD COLUMN previous_revision INTEGER NOT NULL DEFAULT -1')
        db.commit()
    except BaseException:
        db.rollback()
        raise

def prepare(store, repository, snapshot, head, previous, replacement, actor, generation):
    if not re.fullmatch(r'[a-f0-9]{40}', head) or not all(re.fullmatch(r'[a-f0-9]{64}', x) for x in (previous, replacement)):
        raise ValueError('invalid migration identity')
    if type(actor) is not int or actor < 1 or not generation:
        raise ValueError('invalid maintainer identity')
    row = service_baseline.active_row(store, repository)
    if row['digest'] != previous:
        raise ValueError('active baseline changed')
    data = baselines.snapshot_manifest(Path(snapshot), row['manifest_path'])
    if baselines.sha(data) != replacement:
        raise ValueError('replacement digest changed')
    manifest = baselines.parse_manifest(data)
    if head != subprocess.check_output(['git', '-C', snapshot, 'rev-parse', 'HEAD'], text=True).strip():
        raise ValueError('candidate changed')
    changes = baselines.changes(baselines.parse_manifest(row['manifest']), manifest)
    if not changes:
        raise ValueError('replacement has no policy changes')
    migration = uuid.uuid4().hex
    with closing(baselines.open_store(store)) as db:
        schema(db)
        db.execute('BEGIN IMMEDIATE')
        with db:
            active = baselines.lookup(db)
            if active['digest'] != previous or active['repository'] != repository:
                raise ValueError('active baseline changed')
            revision = db.execute('SELECT revision FROM active WHERE id=1').fetchone()[0]
            db.execute('INSERT INTO migrations(id, repository, previous, replacement, manifest, manifest_path, head, actor, selection_generation, status, changes, previous_revision) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)',
                       (migration, repository, previous, replacement, data, row['manifest_path'], head, actor, generation, 'authorized', baselines.encoded(changes), revision))
    return migration


def verify(store, repository, snapshot, migration, report):
    with closing(baselines.open_store(store)) as db:
        schema(db)
        db.row_factory = sqlite3.Row
        row = db.execute('SELECT * FROM migrations WHERE id=? AND repository=?', (migration, repository)).fetchone()
        if row is None or row['status'] != 'authorized':
            raise ValueError('migration is not authorized')
        active = baselines.lookup(db)
        if active['digest'] != row['previous'] or active['repository'] != repository or db.execute('SELECT revision FROM active WHERE id=1').fetchone()[0] != row['previous_revision']:
            raise ValueError('active baseline changed')
        data = baselines.snapshot_manifest(Path(snapshot), row['manifest_path'])
        if data != row['manifest'] or baselines.sha(data) != row['replacement']:
            raise ValueError('replacement changed')
        manifest = baselines.parse_manifest(data)
        with tempfile.TemporaryDirectory(prefix='proofci-migration-') as temporary:
            root = Path(temporary)
            digest = baselines.materialize(manifest, root)
            baseline = proofci.parse_json((root / 'baseline.json').read_bytes())
            candidate = proofci.path_in(Path(snapshot).resolve(strict=True), baseline['candidate'])
            envelope = {'version': 1, 'repository': repository, 'head': row['head'], 'base': row['head'],
                'candidate_sha256': proofci.digest(candidate), 'baseline_sha256': digest,
                'dependency': proofci.digest(proofci.VALIDATOR / 'core-dependencies.json'),
                'toolchain': proofci.TOOLCHAIN_SHA256, 'trust_policy': proofci.policy_digest(),
                'resource_policy': service_execute.LIMITS}
            envelope_path = root / 'envelope.json'
            envelope_path.write_bytes(baselines.encoded(envelope))
            status = dispatch.run(envelope_path=envelope_path, baseline_path=root / 'baseline.json', snapshot=snapshot,
                                  report_path=report, launcher=service_execute.launch_vm)
        result = proofci.parse_json(proofci.bounded_read(Path(report), dispatch.MAX_REPORT_BYTES))
        if status != 0 or result.get('status') != 'passed':
            return status if status in (1, 2) else 2
        if baselines.snapshot_manifest(Path(snapshot), row['manifest_path']) != data:
            raise ValueError('replacement changed')
        result['policy_changed'] = True
        result['previous_baseline_sha256'] = row['previous']
        result['replacement_manifest_sha256'] = row['replacement']
        result['guarantee_changes'] = json.loads(row['changes'])
        old_manifest = baselines.parse_manifest(active['manifest'])
        semantic_fields = {'formal_statement', 'assumptions', 'specification_closure', 'implementation_bindings', 'policy'}
        retired = {item['id'] for item in result['guarantee_changes'] if item['kind'] == 'removed' or (item['kind'] == 'changed' and semantic_fields.intersection(item['fields']))}
        if any(item['kind'] == 'candidate_binding_changed' for item in result['guarantee_changes']):
            retired.update(item['id'] for item in old_manifest['contracts'])
        result['retired_guarantees'] = [item for item in old_manifest['contracts'] if item['id'] in retired]
        db.execute('BEGIN IMMEDIATE')
        with db:
            active = baselines.lookup(db)
            if active['digest'] != row['previous'] or active['repository'] != repository or db.execute('SELECT revision FROM active WHERE id=1').fetchone()[0] != row['previous_revision']:
                raise ValueError('active baseline changed')
            updated = db.execute("UPDATE migrations SET status='verified', report=?, baseline_sha256=? WHERE id=? AND status='authorized'", (baselines.encoded(result), digest, migration))
            if updated.rowcount != 1:
                raise ValueError('migration changed')
        Path(report).write_bytes(baselines.encoded(result))
        return 0


def activate(store, repository, migration, head, actor, generation):
    with closing(baselines.open_store(store)) as db:
        schema(db)
        db.row_factory = sqlite3.Row
        db.execute('BEGIN IMMEDIATE')
        with db:
            row = db.execute('SELECT * FROM migrations WHERE id=? AND repository=?', (migration, repository)).fetchone()
            if row is None or row['status'] != 'verified' or row['head'] != head or row['actor'] != actor or row['selection_generation'] != generation:
                raise ValueError('migration authorization is stale')
            active = baselines.lookup(db)
            if active['digest'] != row['previous'] or active['repository'] != repository or db.execute('SELECT revision FROM active WHERE id=1').fetchone()[0] != row['previous_revision']:
                raise ValueError('active baseline changed')
            if baselines.sha(row['manifest']) != row['replacement']:
                raise ValueError('replacement digest changed')
            existing = db.execute('SELECT manifest, manifest_path, baseline_sha256, repository FROM baselines WHERE digest=?', (row['replacement'],)).fetchone()
            if existing and tuple(existing) != (row['manifest'], row['manifest_path'], row['baseline_sha256'], repository):
                raise ValueError('replacement conflicts with baseline history')
            if existing is None:
                db.execute('INSERT INTO baselines(digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES(?,?,?,?,?,?,?,?,?)',
                           (row['replacement'], row['manifest'], row['manifest_path'], row['baseline_sha256'], repository, head, str(actor), 'authenticated-migration', row['report']))
            changed = db.execute('UPDATE active SET digest=?, revision=revision+1 WHERE id=1 AND digest=? AND revision=?', (row['replacement'], row['previous'], row['previous_revision']))
            if changed.rowcount != 1:
                raise ValueError('active baseline changed')
            db.execute("UPDATE migrations SET status='activated' WHERE id=?", (migration,))
            return json.loads(row['report'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('operation', choices=['prepare', 'verify', 'activate'])
    for name in ('store', 'repository', 'snapshot', 'head', 'previous', 'replacement', 'actor', 'generation', 'migration', 'report'):
        parser.add_argument('--' + name)
    args = parser.parse_args()
    try:
        if args.operation == 'prepare':
            result = {'migration': prepare(args.store, args.repository, args.snapshot, args.head, args.previous, args.replacement, int(args.actor), args.generation)}
        elif args.operation == 'verify':
            return verify(args.store, args.repository, args.snapshot, args.migration, args.report)
        else:
            result = activate(args.store, args.repository, args.migration, args.head, int(args.actor), args.generation)
        print(json.dumps(result))
        return 0
    except (ValueError, TypeError, OSError, sqlite3.Error, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 2

if __name__ == '__main__':
    signal.signal(signal.SIGTERM, lambda _signum, _frame: (_ for _ in ()).throw(KeyboardInterrupt()))
    raise SystemExit(main())
