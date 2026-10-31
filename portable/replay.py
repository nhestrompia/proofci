#!/usr/bin/env python3
"""Export a portable evidence archive and independently replay it."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import select
import time
import subprocess
import sys
import tarfile
import tempfile

import proofci

MAX_ARCHIVE = 256 * 1024 * 1024
MAX_FILE = 128 * 1024 * 1024
MAX_FILES = 1024


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    if not isinstance(name, str) or not name or '\\' in name or any(ord(c) < 32 or ord(c) == 127 for c in name):
        raise ValueError('unsafe archive path')
    parts = name.split('/')
    if any(p in ('', '.', '..') for p in parts) or name.startswith('/'):
        raise ValueError('unsafe archive path: ' + name)
    return name


def read_file(path, limit=MAX_FILE):
    if path.is_symlink() or not path.is_file():
        raise ValueError('missing or unsafe input: ' + str(path))
    return proofci.bounded_read(path, limit)


def export(args):
    envelope_bytes = read_file(args.envelope, 1024 * 1024)
    baseline_bytes = read_file(args.baseline, 1024 * 1024)
    report_bytes = read_file(args.report, 8 * 1024 * 1024)
    envelope = proofci.parse_json(envelope_bytes)
    baseline = proofci.parse_json(baseline_bytes)
    report = proofci.parse_json(report_bytes)
    if report.get('version') != 1 or report.get('envelope') != envelope or report.get('status') not in ('passed', 'blocked'):
        raise ValueError('report does not describe a completed run of this envelope')
    if sha(baseline_bytes) != envelope['baseline_sha256']:
        raise ValueError('baseline digest mismatch')
    snapshot = args.snapshot.resolve(strict=True)
    proofci.validate(envelope, baseline, snapshot, args.baseline.resolve().parent)
    import time
    proofci.verify_snapshot(snapshot, envelope, baseline, time.monotonic() + 60)
    files = {'envelope.json': envelope_bytes, 'baseline/baseline.json': baseline_bytes, 'report.json': report_bytes}
    for item in baseline['obligations']:
        name = safe_name(item['contract'])
        path = proofci.path_in(args.baseline.resolve().parent, name)
        data = read_file(path, 16384)
        if sha(data) != item['contract_sha256']:
            raise ValueError('contract digest mismatch: ' + name)
        key = 'baseline/' + name
        if key == 'baseline/baseline.json':
            raise ValueError('contract path collides with baseline')
        files[key] = data
    with tempfile.TemporaryDirectory(prefix='proofci-export-') as tmp:
        bundle = Path(tmp) / 'repository.bundle'
        # Explicit refs preserve both commits, including a base outside the head ancestry.
        head, base = envelope['head'], envelope['base']
        if not all(isinstance(x, str) and re.fullmatch(r'[0-9a-f]{40}', x) for x in (head, base)):
            raise ValueError('expected full SHA-1 commit IDs')
        # A temporary bare repository avoids modifying the source checkout's refs.
        repo = Path(tmp) / 'repo.git'
        subprocess.run(['git', 'clone', '--bare', '--no-hardlinks', str(snapshot), str(repo)], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        for ref, commit in (('head', head), ('base', base)):
            subprocess.run(['git', '--git-dir', str(repo), 'fetch', '--no-tags', str(snapshot), commit], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            subprocess.run(['git', '--git-dir', str(repo), 'update-ref', 'refs/heads/proofci-' + ref, commit], check=True)
        subprocess.run(['git', '--git-dir', str(repo), 'bundle', 'create', str(bundle), 'refs/heads/proofci-head', 'refs/heads/proofci-base'], check=True)
        files['repository.bundle'] = read_file(bundle)
        if len(files) > MAX_FILES or sum(map(len, files.values())) > MAX_ARCHIVE:
            raise ValueError('bundle exceeds size limit')
        manifest = {'version': 1, 'files': {name: sha(data) for name, data in sorted(files.items())}}
        files['manifest.json'] = (json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n').encode()
        with tarfile.open(args.output, 'w') as archive:
            for name, data in sorted(files.items()):
                safe_name(name)
                info = tarfile.TarInfo(name)
                info.size = len(data)
                info.mode = 0o600
                info.mtime = 0
                archive.addfile(info, io.BytesIO(data))
    print('sha256:' + proofci.digest(args.output))


def ingest(path, expected):
    if not re.fullmatch(r'[0-9a-f]{64}', expected):
        raise ValueError('expected bundle SHA-256 must be 64 lowercase hex characters')
    data = read_file(path, MAX_ARCHIVE)
    if sha(data) != expected:
        raise ValueError('bundle digest mismatch; obtain the original digest from a trusted channel')
    files = {}
    total = 0
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:') as archive:
        for member in archive:
            name = safe_name(member.name)
            if name in files or not member.isfile() or member.size > MAX_FILE:
                raise ValueError('duplicate, non-regular, or oversized archive member: ' + name)
            total += member.size
            if total > MAX_ARCHIVE or len(files) >= MAX_FILES:
                raise ValueError('archive exceeds size or file count limit')
            stream = archive.extractfile(member)
            content = stream.read(member.size + 1)
            if len(content) != member.size:
                raise ValueError('truncated archive member: ' + name)
            files[name] = content
    manifest = proofci.parse_json(files.pop('manifest.json'))
    proofci.fields(manifest, ('version', 'files'))
    if type(manifest['version']) is not int or manifest['version'] != 1:
        raise ValueError('unsupported bundle version')
    if manifest['files'] != {name: sha(content) for name, content in sorted(files.items())}:
        raise ValueError('bundle contents do not match manifest')
    if not {'envelope.json', 'baseline/baseline.json', 'report.json', 'repository.bundle'} <= files.keys():
        raise ValueError('bundle is missing required inputs')
    if any(name not in ('envelope.json', 'report.json', 'repository.bundle') and not name.startswith('baseline/') for name in files):
        raise ValueError('unexpected bundle member')
    return files


def replay(args):
    files = ingest(args.bundle, args.sha256)
    envelope = proofci.parse_json(files['envelope.json'])
    original = proofci.parse_json(files['report.json'])
    with tempfile.TemporaryDirectory(prefix='proofci-replay-') as tmp:
        root = Path(tmp)
        for name, data in files.items():
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        snapshot = root / 'snapshot'
        subprocess.run(['git', '-c', 'transfer.unpackLimit=1', 'clone', '--no-checkout', str(root / 'repository.bundle'), str(snapshot)], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=60)
        if not isinstance(envelope.get('head'), str) or not re.fullmatch(r'[0-9a-f]{40}', envelope['head']):
            raise ValueError('invalid head commit')
        # Count every tree entry, including repeated blobs, before materializing files.
        listing = subprocess.Popen(['git', '-C', str(snapshot), 'ls-tree', '-r', '-l', '-z', envelope['head']], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        deadline = time.monotonic() + 60
        total = count = 0
        pending = b''
        try:
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([listing.stdout], [], [], remaining)[0]:
                    raise ValueError('repository inspection timed out')
                chunk = os.read(listing.stdout.fileno(), 65536)
                if not chunk:
                    break
                pending += chunk
                while b'\0' in pending:
                    entry, pending = pending.split(b'\0', 1)
                    metadata = entry.split(b'\t', 1)[0].split()
                    count += 1
                    if len(metadata) != 4 or metadata[1] != b'blob' or not metadata[3].isdigit():
                        raise ValueError('unsupported repository tree entry')
                    size = int(metadata[3])
                    total += size
                    if size > MAX_FILE or total > MAX_ARCHIVE or count > 100000:
                        raise ValueError('expanded repository exceeds size or file count limit')
                if len(pending) > 65536:
                    raise ValueError('repository path exceeds size limit')
            if pending or listing.wait(timeout=30) != 0:
                raise ValueError('cannot inspect repository tree')
        finally:
            if listing.poll() is None:
                listing.kill()
                listing.wait()
        subprocess.run(['git', '-C', str(snapshot), 'checkout', '--detach', envelope['head']], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        subprocess.run(['git', '-C', str(snapshot), 'remote', 'set-url', 'origin', envelope['repository']], check=True)
        result = root / 'replayed.json'
        status = subprocess.run([sys.executable, str(Path(__file__).with_name('container.py')), '--envelope', str(root / 'envelope.json'), '--baseline', str(root / 'baseline/baseline.json'), '--snapshot', str(snapshot), '--report', str(result)]).returncode
        fresh = proofci.parse_json(read_file(result, 8 * 1024 * 1024))
        def outcomes(report):
            return [(r['id'], r['policy'], r['decision'], r['reason'], r.get('evidence_sha256')) for r in report['results']]
        reproduced = status in (0, 1) and original.get('envelope') == envelope and original.get('status') == fresh.get('status') and original.get('execution') == fresh.get('execution') and isinstance(original.get('execution'), dict) and outcomes(original) == outcomes(fresh)
        output = {'version': 1, 'status': 'reproduced' if reproduced else 'not_reproduced', 'historical_ci_publication': 'not_reproduced', 'original_report': original, 'replay_report': fresh}
        args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
        return status if reproduced else 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    create = commands.add_parser('export')
    for name in ('envelope', 'baseline', 'snapshot', 'report', 'output'):
        create.add_argument('--' + name, required=True, type=Path)
    run = commands.add_parser('replay')
    run.add_argument('--bundle', required=True, type=Path)
    run.add_argument('--sha256', required=True)
    run.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'export':
            export(args)
            return 0
        return replay(args)
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.SubprocessError) as error:
        print('proofci replay: ' + str(error), file=sys.stderr)
        if args.command == 'replay':
            try:
                args.output.write_text(json.dumps({'version': 1, 'status': 'not_reproduced', 'historical_ci_publication': 'not_reproduced', 'reason': str(error)}) + '\n')
            except OSError:
                pass
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
