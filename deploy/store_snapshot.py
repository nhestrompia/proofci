#!/usr/bin/env python3
"""Copy and describe a protected baseline store for deployment backup and restore.

The copy uses SQLite's online backup API, so it is consistent even if a trusted
operator command holds the store open. The description lists the state that a
restoration must preserve: the active baseline, its revision, the authority
revision, migration approvals, and maintainer grants.
"""
import argparse
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'portable'))
import baselines  # noqa: E402


def table(db, name):
    return db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (name,)).fetchone() is not None


def describe(path):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise ValueError('protected baseline store is unavailable')
    with closing(sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)) as db:
        db.execute('BEGIN')
        if db.execute('PRAGMA integrity_check').fetchone()[0] != 'ok':
            raise ValueError('store integrity check failed')
        if not table(db, 'baselines') or not table(db, 'active'):
            raise ValueError('store has no baseline tables')
        result = {'tables': sorted(row[0] for row in db.execute("SELECT name FROM sqlite_master WHERE type='table'"))}
        active = db.execute('SELECT b.digest, b.baseline_sha256, b.repository FROM baselines b JOIN active a ON a.digest=b.digest WHERE a.id=1').fetchone()
        if active is not None:
            row = baselines.lookup(db)
            result['active'] = {'reviewed_sha256': row['digest'], 'baseline_sha256': row['baseline_sha256'], 'repository': row['repository']}
        else:
            result['active'] = None
        result['repositories'] = sorted({row[0] for row in db.execute('SELECT repository FROM baselines')})
        result['baselines'] = db.execute('SELECT count(*) FROM baselines').fetchone()[0]
        result['active_revision'] = db.execute('SELECT revision FROM active_revision WHERE id=1').fetchone()[0] if table(db, 'active_revision') else None
        if table(db, 'authority_state'):
            state = db.execute('SELECT repository, ref, head, epoch, pending_id FROM authority_state WHERE id=1').fetchone()
            enabled = db.execute('SELECT enabled FROM authority_enrollment WHERE id=1').fetchone() if table(db, 'authority_enrollment') else None
            members = [row[0] for row in db.execute('SELECT actor FROM authority_members WHERE active=1 ORDER BY actor')] if table(db, 'authority_members') else []
            result['authority'] = None if state is None else {'repository': state[0], 'ref': state[1], 'head': state[2], 'epoch': state[3],
                'pending': state[4] is not None, 'enabled': bool(enabled and enabled[0] == 1), 'members': members}
            if state is not None:
                result['repositories'] = sorted(set(result['repositories']) | {state[0]})
        else:
            result['authority'] = None
        if table(db, 'migrations'):
            result['migrations'] = [{'id': row[0], 'status': row[1], 'replacement': row[2]} for row in
                                    db.execute('SELECT id, status, replacement FROM migrations ORDER BY id')]
        else:
            result['migrations'] = []
        return result


def copy(source, target):
    source, target = Path(source), Path(target)
    if source.is_symlink() or not source.is_file():
        raise ValueError('protected baseline store is unavailable')
    if target.exists() or target.is_symlink():
        raise ValueError('backup target already exists')
    descriptor = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.close(descriptor)
    try:
        with closing(sqlite3.connect(source.resolve().as_uri() + '?mode=ro', uri=True)) as origin, closing(sqlite3.connect(target)) as copy_db:
            origin.backup(copy_db)
        with target.open('rb') as handle:
            os.fsync(handle.fileno())
    except BaseException:
        target.unlink(missing_ok=True)
        raise
    return describe(target)


def digest(path):
    with open(path, 'rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def install(source, target):
    """Place a verified store copy at a configured path that must not already hold different data."""
    source, target = Path(source), Path(target)
    if target.is_symlink():
        raise ValueError('store target must not be a symbolic link')
    if target.exists():
        if digest(target) != digest(source):
            raise ValueError('store target already exists with different contents')
        return describe(target)
    if not target.parent.is_dir():
        raise ValueError('store parent directory is missing')
    temporary = target.with_name(f'.{target.name}.restore-{os.getpid()}')
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, 'wb') as output, open(source, 'rb') as data:
            while chunk := data.read(1 << 20):
                output.write(chunk)
            output.flush()
            os.fsync(output.fileno())
        if digest(temporary) != digest(source):
            raise ValueError('store copy changed while restoring')
        os.link(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)
    return describe(target)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('describe', 'copy', 'install'))
    parser.add_argument('source')
    parser.add_argument('target', nargs='?')
    args = parser.parse_args()
    try:
        if args.command == 'describe':
            value = describe(args.source)
        elif args.target is None:
            raise ValueError('target is required')
        else:
            value = copy(args.source, args.target) if args.command == 'copy' else install(args.source, args.target)
        print(json.dumps(value, sort_keys=True))
        return 0
    except (OSError, ValueError, sqlite3.Error, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
