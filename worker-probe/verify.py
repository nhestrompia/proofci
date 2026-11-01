#!/usr/bin/env python3
"""Run one fixed verifier invocation inside a networkless disposable guest."""
import base64
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile

import run

run.LOG_LIMIT_BYTES = 12 * 1024 * 1024


def main():
    signal.signal(signal.SIGTERM, run.cancel_on_sigterm)
    with tempfile.TemporaryDirectory(prefix='proofci-vm-') as temporary:
        root = Path(temporary) / 'root'
        for name in ('bin', 'proc', 'sys', 'dev', 'guest', 'lib'):
            (root / name).mkdir(parents=True, exist_ok=True)
        shutil.copy('/bin/busybox.static', root / 'bin/busybox')
        shutil.copytree('/lib/modules', root / 'lib/modules')
        shutil.copy('/verify-init', root / 'init')
        os.chmod(root / 'init', 0o755)
        archive = Path(temporary) / 'initramfs'
        with archive.open('wb') as out:
            listing = subprocess.Popen(['find', '.', '-print'], cwd=root, stdout=subprocess.PIPE)
            packed = subprocess.run(['cpio', '-o', '-H', 'newc'], cwd=root, stdin=listing.stdout, stdout=out, stderr=subprocess.DEVNULL)
            listing.stdout.close()
            if listing.wait() or packed.returncode: raise RuntimeError('cannot construct guest')
        accelerator = 'kvm' if os.path.exists('/dev/kvm') and os.access('/dev/kvm', os.R_OK | os.W_OK) else 'tcg'
        command = ['qemu-system-aarch64', '-machine', 'virt', '-accel', accelerator, '-cpu', 'host' if accelerator == 'kvm' else 'max', '-m', '2048',
                   '-nographic', '-no-reboot', '-nic', 'none', '-kernel', '/boot/vmlinuz-virt', '-initrd', str(archive),
                   '-append', 'console=ttyAMA0 rdinit=/init panic=-1 quiet']
        for tag, path in (('root', '/vm-root'), ('snapshot', '/snapshot'), ('baseline', '/baseline'), ('input', '/runinput')):
            command.extend(['-virtfs', f'local,path={path},mount_tag={tag},security_model=none,readonly=on'])
        code, output, reason = run.collect_guest(command, timeout=900)
        matches = re.findall(r'^PROOFCI_REPORT:([A-Za-z0-9+/=]+)\r?$', output, re.MULTILINE)
        statuses = re.findall(r'^PROOFCI_STATUS:([012])\r?$', output, re.MULTILINE)
        if reason or code != 0 or len(matches) != 1 or len(statuses) != 1:
            print(output[-3000:], file=sys.stderr)
            print(json.dumps({'status': 'error', 'reason': reason or 'guest_failed'}))
            return 2
        data = base64.b64decode(matches[0], validate=True)
        if len(data) > 8 * 1024 * 1024: return 2
        print(json.dumps({'status': 'ok', 'exit_code': int(statuses[0]), 'report': base64.b64encode(data).decode()}))
        return 0


if __name__ == '__main__':
    raise SystemExit(main())
