#!/usr/bin/env python3
"""Read and materialize an approved active baseline for a trusted service."""
import argparse
from contextlib import closing
import json
from pathlib import Path
import sqlite3
import sys

import baselines


class NoActiveBaseline(ValueError):
    pass


def active_row(store, repository):
    path = Path(store)
    if path.is_symlink() or not path.is_file():
        raise ValueError('protected baseline store is unavailable')
    with closing(sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)) as db:
        db.execute('BEGIN')
        try:
            row = baselines.lookup(db)
        except ValueError as error:
            if str(error) == 'baseline not found':
                raise NoActiveBaseline('no active baseline') from error
            raise
        try:
            revision = db.execute('SELECT revision FROM active_revision WHERE id=1').fetchone()
        except sqlite3.OperationalError as error:
            if 'no such table: active_revision' not in str(error):
                raise
            revision = None
        row['active_revision'] = revision[0] if revision else None
    if row['repository'] != repository:
        raise ValueError('active baseline repository mismatch')
    return row


def lookup(store, repository):
    row = active_row(store, repository)
    return {'baseline_sha256': row['baseline_sha256'], 'reviewed_sha256': row['digest'], 'active_revision': row['active_revision'],
            'initial_head': row['initial_head'], 'manifest_path': row['manifest_path']}


def materialize(store, repository, expected, output):
    row = active_row(store, repository)
    if row['baseline_sha256'] != expected:
        raise ValueError('active baseline changed')
    output = Path(output)
    if output.is_symlink() or not output.is_dir() or any(output.iterdir()):
        raise ValueError('protected output must be an empty directory')
    digest = baselines.materialize(baselines.parse_manifest(row['manifest']), output)
    if digest != expected:
        raise ValueError('materialized baseline digest mismatch')
    current = lookup(store, repository)
    if current['baseline_sha256'] != expected or current['reviewed_sha256'] != row['digest']:
        raise ValueError('active baseline changed')
    return current


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--store', type=Path, required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--expected')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        if (args.expected is None) != (args.output is None):
            raise ValueError('expected digest and output must be supplied together')
        value = lookup(args.store, args.repository) if args.expected is None else materialize(args.store, args.repository, args.expected, args.output)
        print(json.dumps(value, sort_keys=True))
        return 0
    except NoActiveBaseline as error:
        print(str(error), file=sys.stderr)
        return 3
    except (OSError, ValueError, sqlite3.Error, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
