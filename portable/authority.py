#!/usr/bin/env python3
"""Serialize managed repository state with the protected baseline store.

Only trusted operators may write this store. A pending head change blocks work
until the gateway completes or explicitly reconciles it.
"""
import argparse
from contextlib import closing
import json
import os
from pathlib import Path
import re
import sqlite3
import sys
import uuid

import baselines


def schema(db):
    db.execute('''CREATE TABLE IF NOT EXISTS authority_state (
        id INTEGER PRIMARY KEY CHECK(id=1), repository TEXT NOT NULL, ref TEXT NOT NULL,
        head TEXT NOT NULL, epoch INTEGER NOT NULL, pending_id TEXT, pending_head TEXT)''')
    db.execute('''CREATE TABLE IF NOT EXISTS authority_enrollment (
        id INTEGER PRIMARY KEY CHECK(id=1), enabled INTEGER NOT NULL CHECK(enabled IN (0,1)))''')
    db.execute('''CREATE TABLE IF NOT EXISTS authority_members (
        actor INTEGER PRIMARY KEY CHECK(actor>0), active INTEGER NOT NULL CHECK(active IN (0,1)))''')
    db.execute('''CREATE TABLE IF NOT EXISTS authority_changes (
        id TEXT PRIMARY KEY, old_head TEXT NOT NULL, new_head TEXT NOT NULL,
        status TEXT NOT NULL CHECK(status IN ('pending','applied','aborted','quarantined')))''')
    db.execute('''CREATE TABLE IF NOT EXISTS authority_events (
        id INTEGER PRIMARY KEY, operation TEXT NOT NULL, subject INTEGER, change_id TEXT,
        epoch INTEGER NOT NULL, operator_uid INTEGER NOT NULL, created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP)''')


def valid_ref(ref):
    return (isinstance(ref, str) and ref.startswith('refs/heads/') and len(ref) <= 512
            and not re.search(r'[\x00-\x20\x7f~^:?*\[\\]', ref) and '..' not in ref
            and '@{' not in ref and not ref.endswith(('/', '.'))
            and all(part and not part.startswith('.') and not part.endswith('.lock') for part in ref.split('/')))


def checked(db, repository, head=None, actor=None, epoch=None, ref=None):
    state = db.execute('SELECT repository, ref, head, epoch, pending_id FROM authority_state WHERE id=1').fetchone()
    if state is None or state[0] != repository or state[4] is not None:
        raise ValueError('repository authority unavailable')
    enrollment = db.execute('SELECT enabled FROM authority_enrollment WHERE id=1').fetchone()
    if enrollment is None or enrollment[0] != 1:
        raise ValueError('repository authority disabled')
    if ref is not None and state[1] != ref:
        raise ValueError('authority ref changed')
    if head is not None and state[2] != head:
        raise ValueError('authority head changed')
    if epoch is not None and state[3] != epoch:
        raise ValueError('authority revision changed')
    if actor is not None and db.execute('SELECT 1 FROM authority_members WHERE actor=? AND active=1', (actor,)).fetchone() is None:
        raise ValueError('maintainer authority revoked')
    return state[3]


def observe(store, repository, head=None, ref=None):
    path = Path(store)
    if path.is_symlink() or not path.is_file():
        raise ValueError('protected baseline store is unavailable')
    with closing(sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)) as db:
        if db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='authority_state'").fetchone() is None:
            return None
        return checked(db, repository, head=head, ref=ref)


def pending(store, repository):
    path = Path(store)
    if path.is_symlink() or not path.is_file():
        raise ValueError('protected baseline store is unavailable')
    with closing(sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)) as db:
        row = db.execute('SELECT repository,ref,head,pending_id,pending_head FROM authority_state WHERE id=1').fetchone()
        if row is None or row[0] != repository or row[3] is None or row[4] is None:
            raise ValueError('no recoverable head change')
        return {'ref': row[1], 'old_head': row[2], 'change': row[3], 'new_head': row[4]}


def mutate(store, operation, repository, *, head=None, actor=None, change=None, expected=None, ref=None):
    path = Path(store)
    if path.is_symlink() or not path.is_file():
        raise ValueError('protected baseline store is unavailable')
    with closing(baselines.open_store(path)) as db:
        db.execute('BEGIN IMMEDIATE')
        try:
            schema(db)
            active = baselines.lookup(db)
            if active['repository'] != repository:
                raise ValueError('repository mismatch')
            if operation == 'bootstrap':
                if not re.fullmatch(r'[a-f0-9]{40}', head or '') or type(actor) is not int or actor < 1 or not valid_ref(ref):
                    raise ValueError('invalid bootstrap identity')
                db.execute('INSERT INTO authority_state VALUES(1,?,?,?,1,NULL,NULL)', (repository, ref, head))
                db.execute('INSERT INTO authority_members VALUES(?,1)', (actor,))
                db.execute('INSERT INTO authority_enrollment VALUES(1,1)')
                result = {'epoch': 1}
            else:
                epoch = checked(db, repository) if operation not in ('finish', 'revoke', 'quarantine', 'disable', 'enable') else None
                if operation == 'revoke':
                    state = db.execute('SELECT repository,epoch FROM authority_state WHERE id=1').fetchone()
                    if state is None or state[0] != repository:
                        raise ValueError('repository authority unavailable')
                    epoch = state[1]
                if operation in ('disable', 'enable'):
                    state = db.execute('SELECT repository,pending_id,epoch FROM authority_state WHERE id=1').fetchone()
                    if state is None or state[0] != repository or (operation == 'enable' and state[1] is not None):
                        raise ValueError('repository authority unavailable')
                    desired = int(operation == 'enable')
                    current = db.execute('SELECT enabled FROM authority_enrollment WHERE id=1').fetchone()
                    if current is None:
                        raise ValueError('repository enrollment authority unavailable')
                    if current[0] == desired:
                        result = {'epoch': state[2], 'unchanged': True}
                    else:
                        db.execute('UPDATE authority_enrollment SET enabled=? WHERE id=1', (desired,))
                        db.execute('UPDATE authority_state SET epoch=epoch+1 WHERE id=1')
                        result = {'epoch': state[2] + 1}
                elif operation in ('grant', 'revoke'):
                    if type(actor) is not int or actor < 1:
                        raise ValueError('invalid maintainer identity')
                    current = db.execute('SELECT active FROM authority_members WHERE actor=?', (actor,)).fetchone()
                    desired = int(operation == 'grant')
                    if current is not None and current[0] == desired:
                        result = {'epoch': epoch, 'unchanged': True}
                    else:
                        db.execute('INSERT INTO authority_members(actor,active) VALUES(?,?) ON CONFLICT(actor) DO UPDATE SET active=excluded.active', (actor, desired))
                        db.execute('UPDATE authority_state SET epoch=epoch+1 WHERE id=1')
                        result = {'epoch': epoch + 1}
                elif operation == 'begin':
                    if not re.fullmatch(r'[a-f0-9]{40}', head or '') or not re.fullmatch(r'[a-f0-9]{40}', expected or ''):
                        raise ValueError('invalid head change')
                    if head == expected:
                        raise ValueError('head change must advance')
                    if not isinstance(ref, str):
                        raise ValueError('managed ref required')
                    checked(db, repository, head=expected, ref=ref)
                    change = uuid.uuid4().hex
                    db.execute('INSERT INTO authority_changes VALUES(?,?,?,?)', (change, expected, head, 'pending'))
                    db.execute('UPDATE authority_state SET pending_id=?, pending_head=?, epoch=epoch+1 WHERE id=1', (change, head))
                    result = {'change': change, 'epoch': epoch + 1}
                elif operation == 'finish':
                    state = db.execute('SELECT repository,pending_id,pending_head,epoch FROM authority_state WHERE id=1').fetchone()
                    record = db.execute('SELECT new_head,status FROM authority_changes WHERE id=?', (change,)).fetchone()
                    if state is None or state[0] != repository or record is None or record[0] != head:
                        raise ValueError('pending head change mismatch')
                    if record[1] == 'applied':
                        result = {'epoch': state[3], 'already_applied': True}
                    elif state[1] != change or state[2] != head or record[1] != 'pending':
                        raise ValueError('pending head change mismatch')
                    else:
                        db.execute('UPDATE authority_state SET head=pending_head,pending_id=NULL,pending_head=NULL,epoch=epoch+1 WHERE id=1')
                        db.execute("UPDATE authority_changes SET status='applied' WHERE id=?", (change,))
                        result = {'epoch': state[3] + 1}
                elif operation == 'quarantine':
                    state = db.execute('SELECT repository,pending_id,pending_head,epoch FROM authority_state WHERE id=1').fetchone()
                    if state is None or state[0] != repository:
                        raise ValueError('repository authority unavailable')
                    if state[1] is None or state[2] is not None:
                        if state[1] is not None:
                            db.execute("UPDATE authority_changes SET status='quarantined' WHERE id=? AND status='pending'", (state[1],))
                        change = uuid.uuid4().hex
                        db.execute('UPDATE authority_state SET pending_id=?,pending_head=NULL,epoch=epoch+1 WHERE id=1', (change,))
                        result = {'quarantined': True, 'change': change}
                    else:
                        change = state[1]
                        result = {'quarantined': True, 'change': change, 'unchanged': True}
                else:
                    raise ValueError('unknown authority operation')
            current_epoch = db.execute('SELECT epoch FROM authority_state WHERE id=1').fetchone()[0]
            if not result.get('unchanged') and not result.get('already_applied'):
                db.execute('INSERT INTO authority_events(operation,subject,change_id,epoch,operator_uid) VALUES(?,?,?,?,?)',
                           (operation, actor, change, current_epoch, os.getuid()))
            db.commit()
            return result
        except BaseException:
            db.rollback()
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['bootstrap', 'grant', 'revoke', 'begin', 'finish', 'quarantine', 'disable', 'enable', 'observe'])
    parser.add_argument('--store', required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--head')
    parser.add_argument('--actor', type=int)
    parser.add_argument('--change')
    parser.add_argument('--expected')
    parser.add_argument('--ref')
    args = parser.parse_args()
    try:
        if args.operation == 'observe':
            print(json.dumps({'epoch': observe(args.store, args.repository)}))
        else:
            print(json.dumps(mutate(args.store, args.operation, args.repository, head=args.head, actor=args.actor, change=args.change, expected=args.expected, ref=args.ref)))
        return 0
    except (ValueError, TypeError, OSError, sqlite3.Error) as error:
        print(str(error), file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
