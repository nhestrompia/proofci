#!/usr/bin/env python3
"""Remove an Apple container after its launcher exits or loses its pipe."""
import json
import subprocess
import sys
import time

runtime, name, encoded = sys.argv[1:]
try:
    subprocess.run(json.loads(encoded), check=True, stdin=subprocess.DEVNULL,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print('created', flush=True)
    if sys.stdin.read(1) == 'S':
        sys.stdin.read(1)
finally:
    while True:
        try:
            subprocess.run([runtime, 'delete', '--force', name], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=15, check=False)
            result = subprocess.run([runtime, 'inspect', name], stdout=subprocess.DEVNULL,
                                    stderr=subprocess.PIPE, timeout=15, check=False)
            if result.returncode != 0 and b'container not found:' in result.stderr.lower():
                break
        except (OSError, subprocess.TimeoutExpired):
            pass
        time.sleep(2)
