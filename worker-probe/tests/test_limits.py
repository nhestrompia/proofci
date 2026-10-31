"""Exercise the launcher limits with real subprocesses and pipes."""
import importlib.util
import os
import time
from pathlib import Path
import sys
import subprocess
import unittest

spec = importlib.util.spec_from_file_location("probe", Path(__file__).resolve().parents[1] / "run.py")
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class GuestLimitsTest(unittest.TestCase):
    def test_time_limit_terminates_process(self):
        original = probe.TIME_LIMIT_SECONDS
        self.addCleanup(setattr, probe, "TIME_LIMIT_SECONDS", original)
        probe.TIME_LIMIT_SECONDS = 0.2
        code, _, reason = probe.collect_guest([sys.executable, "-c", "import time; time.sleep(10)"])
        self.assertEqual(reason, "guest_timeout")
        self.assertNotEqual(code, 0)

    def test_log_limit_terminates_process_without_retaining_excess(self):
        original = probe.LOG_LIMIT_BYTES
        self.addCleanup(setattr, probe, "LOG_LIMIT_BYTES", original)
        probe.LOG_LIMIT_BYTES = 1024
        code, output, reason = probe.collect_guest([sys.executable, "-c", "import sys; sys.stdout.write('x' * 100000); sys.stdout.flush()"])
        self.assertEqual(reason, "guest_log_limit")
        self.assertLessEqual(len(output.encode()), 1024)
        self.assertNotEqual(code, 0)

    def test_sigterm_cancels_guest(self):
        runner = Path(__file__).resolve().parents[1] / "run.py"
        script = f"""
import importlib.util, os, signal, sys, threading
spec = importlib.util.spec_from_file_location('probe', {str(runner)!r})
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
signal.signal(signal.SIGTERM, probe.cancel_on_sigterm)
threading.Timer(0.2, lambda: os.kill(os.getpid(), signal.SIGTERM)).start()
code, _, reason = probe.collect_guest([sys.executable, '-c', 'import time; time.sleep(10)'])
assert reason == 'cancelled' and code != 0
"""
        completed = subprocess.run([sys.executable, "-c", script], timeout=5, capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_timeout_kills_descendant_after_parent_exits(self):
        original = probe.TIME_LIMIT_SECONDS
        self.addCleanup(setattr, probe, "TIME_LIMIT_SECONDS", original)
        probe.TIME_LIMIT_SECONDS = 0.2
        command = "import subprocess, sys; p=subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(10)']); print(p.pid, flush=True)"
        _, output, reason = probe.collect_guest([sys.executable, "-c", command])
        self.assertEqual(reason, "guest_timeout")
        pid = int(output.strip())
        for _ in range(100):
            try:
                state = Path(f"/proc/{pid}/stat").read_text().split()[2]
            except FileNotFoundError:
                break
            if state == "Z":
                break
            time.sleep(0.01)
        else:
            self.fail(f"descendant {pid} is still running")


if __name__ == "__main__":
    unittest.main()
