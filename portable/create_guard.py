#!/usr/bin/env python3
"""Remove a delayed Docker creation if the launching process goes away."""
import json
import subprocess
import sys
import time

name, encoded = sys.argv[1:]
try:
    subprocess.run(json.loads(encoded), check=True, stdin=subprocess.DEVNULL,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print("created", flush=True)
    if sys.stdin.read(1) == "S":
        sys.stdin.read(1)
finally:
    while True:
        try:
            subprocess.run(["docker", "rm", "-f", name], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=15, check=False)
            inspection = subprocess.run(["docker", "inspect", name], stdout=subprocess.DEVNULL,
                                        stderr=subprocess.PIPE, timeout=15, check=False)
            if inspection.returncode != 0 and b"no such object" in inspection.stderr.lower():
                break
        except (OSError, subprocess.TimeoutExpired):
            pass
        time.sleep(2)
