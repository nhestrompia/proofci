#!/usr/bin/env python3
"""Run the fixed verifier in a disposable networkless QEMU guest."""
import argparse
import base64
import hashlib
import json
import os
import re
from pathlib import Path
import signal
import shutil
import select
import sys
import time
import subprocess
import tempfile
import uuid

import proofci
import report as report_contract

VM_IMAGE_ID = 'sha256:166f221ee92c8e38ca0a211fe10d057d919216216c21e661b48cf73859a6acce'


def cancel(_signal, _frame):
    raise KeyboardInterrupt


def run(args):
    report = Path(args.report).resolve()
    name = 'proofci-vm-' + uuid.uuid4().hex
    try:
        if os.getuid() == 0:
            raise ValueError('run the launcher as an unprivileged user')
        envelope = proofci.parse_json(proofci.bounded_read(Path(args.envelope), 1024 * 1024))
        baseline_input = Path(args.baseline)
        snapshot_input = Path(args.snapshot)
        if baseline_input.is_symlink() or snapshot_input.is_symlink():
            raise ValueError('input must not be a symbolic link')
        snapshot = snapshot_input.resolve(strict=True)
        baseline_path = baseline_input.resolve(strict=True)
        baseline = proofci.parse_json(proofci.bounded_read(baseline_path, 1024 * 1024))
        proofci.validate(envelope, baseline, snapshot, baseline_path.parent)
        if report.is_relative_to(snapshot) or baseline_path.parent.is_relative_to(snapshot):
            raise ValueError('protected paths must be outside snapshot')
        if args.dependencies is not None:
            raise ValueError('VM dependency staging is not supported')
        image = args.image or VM_IMAGE_ID
        runtime = os.environ.get('PROOFCI_APPLE_RUNTIME')
        if runtime:
            kernel = os.environ.get('PROOFCI_APPLE_KERNEL', '')
            expected = os.environ.get('PROOFCI_APPLE_KERNEL_SHA256', '')
            if not Path(runtime).is_absolute() or not Path(kernel).is_absolute() or not re.fullmatch(r'[a-f0-9]{64}', expected):
                raise ValueError('invalid accelerated runtime configuration')
            with open(kernel, 'rb') as source:
                if hashlib.file_digest(source, 'sha256').hexdigest() != expected:
                    raise ValueError('accelerated kernel identity mismatch')
            if image != VM_IMAGE_ID:
                raise ValueError('VM image identity mismatch')
            apple_image = 'docker.io/library/proofci-vm-verifier:latest'
            inspection = json.loads(subprocess.check_output([runtime, 'image', 'inspect', apple_image], text=True, timeout=20))
            verified_index = inspection[0]['configuration']['descriptor']['digest']
            variants = inspection[0]['variants']
            if not any(item.get('digest') == VM_IMAGE_ID and item.get('platform') == {'architecture': 'arm64', 'os': 'linux'} for item in variants):
                raise ValueError('VM image identity mismatch')
            image_id = VM_IMAGE_ID
        else:
            image_id = subprocess.check_output(['docker', 'image', 'inspect', '--format', '{{.Id}}', image], text=True, timeout=20).strip()
            if image_id != VM_IMAGE_ID:
                raise ValueError('VM image identity mismatch')
        with tempfile.TemporaryDirectory(prefix='proofci-vm-input-') as temporary:
            root = Path(temporary); os.chmod(root, 0o755)
            if runtime:
                kernel_dir = root / 'kernel'; kernel_dir.mkdir(mode=0o700)
                staged_kernel = kernel_dir / 'vmlinux'
                with open(kernel, 'rb') as source, staged_kernel.open('xb') as target:
                    shutil.copyfileobj(source, target)
                staged_kernel.chmod(0o400)
                with staged_kernel.open('rb') as source:
                    if hashlib.file_digest(source, 'sha256').hexdigest() != expected:
                        raise ValueError('accelerated kernel identity mismatch')
                kernel = str(staged_kernel)
            input_dir = root / 'input'; input_dir.mkdir(mode=0o755)
            protected = root / 'protected'; protected.mkdir(mode=0o755)
            (input_dir / 'envelope.json').write_text(json.dumps(envelope))
            (protected / 'baseline.json').write_bytes(proofci.bounded_read(baseline_path, 1024 * 1024))
            for item in baseline['obligations']:
                contract = proofci.path_in(baseline_path.parent, item['contract'])
                data = proofci.bounded_read(contract, 16384)
                if hashlib.sha256(data).hexdigest() != item['contract_sha256']:
                    raise ValueError('contract identity mismatch')
                target = protected / item['contract']
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            for path in (input_dir, protected):
                for directory, subdirs, files in os.walk(path):
                    os.chmod(directory, 0o755)
                    for file in files: os.chmod(Path(directory) / file, 0o444)
            if runtime:
                command = [runtime, 'create', '--name', name, '--rm', '--virtualization', '--kernel', kernel,
                           '--network', 'none', '--memory', '4g', '--cpus', '2']
                for source, target in ((snapshot, '/snapshot'), (protected, '/baseline'), (input_dir, '/runinput')):
                    if ',' in str(source): raise ValueError('unsupported input path')
                    command.extend(['--mount', f'type=bind,source={source},target={target},readonly'])
                command.append(apple_image)
                guard_script = 'vm_apple_guard.py'
                start_command = [runtime, 'start', '--attach', name]
            else:
                command = ['docker', 'create', '--rm', '--name', name, '--network', 'none', '--read-only',
                           '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges', '--memory', '3g', '--pids-limit', '128', '--cpus', '1',
                           '--tmpfs', '/tmp:rw,size=256m,mode=1777']
                if Path('/dev/kvm').exists():
                    command.extend(['--device', '/dev/kvm:/dev/kvm'])
                for source, target in ((snapshot, '/snapshot'), (protected, '/baseline'), (input_dir, '/runinput')):
                    if ',' in str(source): raise ValueError('unsupported input path')
                    command.extend(['--mount', f'type=bind,src={source},dst={target},readonly'])
                command.append(image_id)
                guard_script = 'create_guard.py'
                start_command = ['docker', 'start', '-a', name]
            timeout = min(900, envelope['resource_policy']['timeout_seconds'], envelope['resource_policy']['cpu_seconds'])
            deadline = time.monotonic() + timeout
            guard = subprocess.Popen(
                [sys.executable, str(Path(__file__).with_name(guard_script)), *([runtime] if runtime else []), name, json.dumps(command)],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, start_new_session=True,
            )
            try:
                ready, _, _ = select.select([guard.stdout], [], [], max(0, deadline - time.monotonic()))
                if not ready:
                    raise subprocess.TimeoutExpired('docker create', timeout)
                if guard.stdout.readline() != b'created\n':
                    raise ValueError('VM container creation failed')
                if runtime:
                    created = json.loads(subprocess.check_output([runtime, 'inspect', name], text=True, timeout=20))
                    if len(created) != 1 or created[0]['configuration']['image']['descriptor']['digest'] != verified_index:
                        raise ValueError('created VM image identity mismatch')
                guard.stdin.write(b'S')
                guard.stdin.flush()
                process = subprocess.Popen(start_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                try:
                    output, stderr = process.communicate(timeout=max(0, deadline - time.monotonic()))
                except (KeyboardInterrupt, subprocess.TimeoutExpired):
                    process.kill()
                    process.communicate()
                    raise
            finally:
                # The independent guard removes the container even if this launcher is killed.
                guard.stdin.close()
                guard.stdout.close()
            if process.returncode != 0 or len(output) > 12 * 1024 * 1024: raise ValueError('VM execution failed: ' + stderr.decode(errors='replace')[-3000:])
            response = json.loads(output)
            if response.get('status') != 'ok' or response.get('exit_code') not in (0, 1, 2): raise ValueError('VM returned invalid status')
            data = base64.b64decode(response['report'], validate=True)
            if len(data) > 8 * 1024 * 1024: raise ValueError('VM report exceeds size limit')
            value = proofci.parse_json(data)
            status = response['exit_code']
            if status in (0, 1): report_contract.validate(value, envelope, baseline)
            elif value.get('version') != 1 or value.get('status') != 'error': raise ValueError('VM error report invalid')
            if (status == 0 and value.get('status') != 'passed') or (status == 1 and value.get('status') != 'blocked'):
                raise ValueError('VM status mismatch')
            value.setdefault('execution', {})['dispatch_phase'] = args.phase
            value['execution']['image'] = image_id
            value['execution']['virtualization'] = 'apple' if runtime else 'qemu'
            report.write_text(json.dumps(value, sort_keys=True) + '\n')
            return status
    except KeyboardInterrupt:
        report.write_text(json.dumps({'version': 1, 'status': 'error', 'reason': 'cancelled'}) + '\n')
        return 2
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        report.write_text(json.dumps({'version': 1, 'status': 'error', 'reason': str(error)}) + '\n')
        return 2


def main():
    signal.signal(signal.SIGTERM, cancel)
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('envelope', 'baseline', 'snapshot', 'report'): parser.add_argument('--' + name, required=True)
    parser.add_argument('--phase', choices=('worker', 'final-validation'), default='worker')
    parser.add_argument('--image')
    parser.add_argument('--dependencies')
    parser.add_argument('--validator-only', action='store_true')
    return run(parser.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
