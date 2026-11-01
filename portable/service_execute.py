#!/usr/bin/env python3
"""Run an approved baseline against a staged immutable snapshot."""
import argparse
import json
from pathlib import Path
import re
import signal
import sqlite3
import subprocess
import tempfile

import baselines
import dispatch
import proofci
import service_baseline

LIMITS = json.loads(Path(__file__).with_name('resource_limits.json').read_text())


def launch_vm(command, deadline):
    command = list(command)
    command[1] = str(Path(__file__).with_name('vm_container.py'))
    return dispatch._run_process(command, deadline)


def execute(*, store, repository, head, base, baseline_digest, snapshot, report):
    try:
        if not re.fullmatch(r'[a-f0-9]{40}', head) or not re.fullmatch(r'[a-f0-9]{40}', base):
            raise ValueError('invalid candidate identity')
        snapshot = Path(snapshot)
        if snapshot.is_symlink():
            raise ValueError('snapshot must not be a symbolic link')
        snapshot = snapshot.resolve(strict=True)
        report = Path(report).resolve()
        if report.is_relative_to(snapshot):
            raise ValueError('report must be outside the snapshot')
        row = service_baseline.active_row(store, repository)
        if row['baseline_sha256'] != baseline_digest:
            raise ValueError('active baseline changed')
        with tempfile.TemporaryDirectory(prefix='proofci-approved-') as temporary:
            root = Path(temporary)
            protected = root / 'protected'; protected.mkdir()
            service_baseline.materialize(store, repository, baseline_digest, protected)
            baseline = proofci.parse_json((protected / 'baseline.json').read_bytes())
            candidate = proofci.path_in(snapshot, baseline['candidate'])
            if not candidate.is_file() or candidate.stat().st_size > LIMITS['file_bytes']:
                raise ValueError('invalid candidate file')
            envelope = {'version': 1, 'repository': repository, 'head': head, 'base': base,
                'candidate_sha256': proofci.digest(candidate), 'baseline_sha256': baseline_digest,
                'dependency': proofci.digest(proofci.VALIDATOR / 'core-dependencies.json'),
                'toolchain': proofci.TOOLCHAIN_SHA256, 'trust_policy': proofci.policy_digest(),
                'resource_policy': LIMITS}
            envelope_path = root / 'envelope.json'
            envelope_path.write_bytes(baselines.encoded(envelope))
            status = dispatch.run(envelope_path=envelope_path, baseline_path=protected / 'baseline.json',
                                  snapshot=snapshot, report_path=report, launcher=launch_vm)
            result = proofci.parse_json(proofci.bounded_read(report, dispatch.MAX_REPORT_BYTES))
            current = service_baseline.active_row(store, repository)
            if current['digest'] != row['digest'] or current['baseline_sha256'] != baseline_digest:
                raise ValueError('active baseline changed')
            if status in (0, 1):
                try:
                    proposed = baselines.parse_manifest(baselines.snapshot_manifest(snapshot, row['manifest_path']), supported=False)
                    difference = baselines.changes(baselines.parse_manifest(row['manifest']), proposed)
                except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError):
                    difference = [{'kind': 'missing_or_invalid_manifest'}]
                result['reviewed_baseline_sha256'] = row['digest']
                result['proposed_guarantee_changes'] = difference
                if difference and status == 0:
                    status = 1
                    result['status'] = 'blocked'
                report.write_bytes(baselines.encoded(result))
            return status
    except KeyboardInterrupt:
        dispatch._write_error(report, 'cancelled')
        return 2
    except (OSError, ValueError, KeyError, TypeError, RecursionError, UnicodeError, sqlite3.Error, subprocess.SubprocessError) as error:
        dispatch._write_error(report, error)
        return 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('store', 'repository', 'head', 'base', 'baseline-digest', 'snapshot', 'report'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    return execute(store=args.store, repository=args.repository, head=args.head, base=args.base,
                   baseline_digest=args.baseline_digest, snapshot=args.snapshot, report=args.report)


if __name__ == '__main__':
    signal.signal(signal.SIGTERM, lambda _signum, _frame: (_ for _ in ()).throw(KeyboardInterrupt()))
    raise SystemExit(main())
