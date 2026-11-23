import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import check, bridge  # noqa: E402

F = "src/ledger.ts::transfer"


class DowngradeTests(unittest.TestCase):
    def test_proved_to_tested_is_a_downgrade(self):
        [d] = check._downgrades({F: ("tested", "did not check")}, {F: "proved"}, set())
        self.assertEqual((d["function"], d["was"], d["now"], d["accepted"], d["reason"]),
                         (F, "proved", "tested", False, "did not check"))

    def test_proved_to_proved_is_not(self):
        self.assertEqual(check._downgrades({F: ("proved", "")}, {F: "proved"}, set()), [])

    def test_tested_to_tested_is_not(self):
        self.assertEqual(check._downgrades({F: ("tested", "")}, {F: "tested"}, set()), [])
        self.assertEqual(check._downgrades({F: ("unsupported", "")}, {F: "not proved"}, set()), [])

    def test_proved_to_unsupported_or_removed(self):
        for now in (("unsupported", "only `number` operands"), ("removed", "the function is not in the pull request's code")):
            [d] = check._downgrades({F: now}, {F: "proved"}, set())
            self.assertEqual((d["was"], d["now"]), ("proved", now[0]))

    def test_unknown_base_fails_closed(self):
        [d] = check._downgrades({F: ("tested", "did not check")}, {F: "unknown"}, set())
        self.assertEqual((d["was"], d["accepted"]), ("unknown", False))
        self.assertIn("unknown", d["reason"])
        # ...but a function proved now cannot be a downgrade however the base check went.
        self.assertEqual(check._downgrades({F: ("proved", "")}, {F: "unknown"}, set()), [])

    def test_accepted(self):
        [d] = check._downgrades({F: ("tested", "")}, {F: "proved"}, {F})
        self.assertTrue(d["accepted"])

    def test_blocks_the_report(self):
        report = check.Report(language="typescript")
        report.outcomes = [check.Outcome("fees", "capped", "f", "fee_capped", True, check.VERIFIED)]
        self.assertTrue(report.passed)
        report.downgrades = [{"function": F, "was": "proved", "now": "tested", "reason": "", "accepted": False}]
        self.assertFalse(report.passed)
        report.downgrades[0]["accepted"] = True
        self.assertTrue(report.passed)


class BaseStatusTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.base_checkout, self.work = root / "base", root / "work"
        for d in (self.base_checkout / "src", self.work / "bridge"):
            d.mkdir(parents=True)
        (self.base_checkout / "src" / "ledger.ts").write_text("// code")
        self.base = SimpleNamespace(crate=".", assumes=(), effects=())
        self.now = {F: ("tested", "did not check")}

    def statuses(self, functions=(F,), now=None, deps_changed=False):
        return check._base_statuses(self.base_checkout, self.base, self.work, list(functions),
                                    Path("vendor"), 60, 900, now or self.now, deps_changed)

    def extraction(self, failures=()):
        return SimpleNamespace(failures=failures)

    def test_missing_base_file_is_not_proved(self):
        (self.base_checkout / "src" / "ledger.ts").unlink()
        with patch.object(check.typescript, "extract", side_effect=AssertionError("must not run")):
            self.assertEqual(self.statuses(), {F: "not proved"})

    def test_missing_check_uses_the_package_directory(self):
        # A nested package: the function's file is resolved under `crate`, not the root.
        (self.base_checkout / "packages" / "x" / "src").mkdir(parents=True)
        (self.base_checkout / "packages" / "x" / "src" / "ledger.ts").write_text("// code")
        self.base.crate = "packages/x"
        seen = {}
        with patch.object(check.typescript, "extract", return_value=self.extraction([F])) as extract:
            self.assertEqual(self.statuses(), {F: "not proved"})
            seen["package"] = extract.call_args[0][1]
        self.assertEqual(seen["package"], "packages/x")

    def test_extraction_crash_is_unknown(self):
        with patch.object(check.typescript, "extract", side_effect=KeyError("x")):
            self.assertEqual(self.statuses(), {F: "unknown"})

    def test_extraction_failure(self):
        with patch.object(check.typescript, "extract", return_value=self.extraction([F])):
            self.assertEqual(self.statuses(), {F: "not proved"})
            self.assertEqual(self.statuses(deps_changed=True), {F: "unknown"})

    def _bridge(self, statuses):
        def run(extraction, work, functions, timeout=None, budget=None):
            return {f: bridge.FunctionStatus(f, *statuses[f]) for f in functions if f in statuses}
        return run

    def test_bridge_results(self):
        gen = ({F: "ledger_transfer.lean"}, {})
        with patch.object(check.typescript, "extract", return_value=self.extraction()), \
             patch.object(check.bridge, "generate", return_value=gen), \
             patch.object(check.bridge, "run", self._bridge({F: ("tested", "did not check")})):
            self.assertEqual(self.statuses(), {F: "tested"})
            self.assertEqual(self.statuses(deps_changed=True), {F: "unknown"})
        with patch.object(check.typescript, "extract", return_value=self.extraction()), \
             patch.object(check.bridge, "generate", return_value=gen), \
             patch.object(check.bridge, "run", self._bridge({F: ("tested", "the bridge proof did not finish in 60 seconds")})):
            self.assertEqual(self.statuses(), {F: "unknown"})

    def test_identical_input_skips_base_run(self):
        (self.work / "bridge" / "f.lean").write_text("theorem t")
        gen = ({F: "f.lean"}, {})
        def generate(extraction, targets, out):
            out.mkdir(exist_ok=True)
            (out / "f.lean").write_text("theorem t")
            return gen
        run = self._bridge({F: ("proved", "")})
        with patch.object(check.typescript, "extract", return_value=self.extraction()), \
             patch.object(check.bridge, "generate", generate), \
             patch.object(check.bridge, "run", run):
            self.assertEqual(self.statuses(), {F: "not proved"})
        # A head run that timed out is inconclusive: unknown, and no budget is spent.
        self.now[F] = ("tested", "the bridge proof did not finish in 60 seconds")
        with patch.object(check.typescript, "extract", return_value=self.extraction()), \
             patch.object(check.bridge, "generate", generate), \
             patch.object(check.bridge, "run", side_effect=AssertionError("must not run")):
            self.assertEqual(self.statuses(), {F: "unknown"})

    def test_deps_changed(self):
        head = Path(self.tmp.name) / "head"
        head.mkdir()
        (self.base_checkout / "package.json").write_text("{}")
        self.assertTrue(check._deps_changed(self.base_checkout, head, "."))  # removed on the pull request
        self.assertFalse(check._deps_changed(self.base_checkout, self.base_checkout, "."))
        (head / "package.json").write_text("{}")
        self.assertFalse(check._deps_changed(self.base_checkout, head, "."))
        (head / "package.json").write_text('{"a": 1}')
        self.assertTrue(check._deps_changed(self.base_checkout, head, "."))

    def test_deps_changed_in_monorepo_ancestors(self):
        # The package sits in packages/x; the install reads the lockfile and manager
        # config at the checkout root, so a change there counts too.
        head = Path(self.tmp.name) / "head"
        for root in (self.base_checkout, head):
            (root / "packages" / "x").mkdir(parents=True)
            (root / "packages" / "x" / "package.json").write_text("{}")
            (root / "pnpm-lock.yaml").write_text("lockfileVersion: '9.0'")
        self.assertFalse(check._deps_changed(self.base_checkout, head, "packages/x"))
        (head / "pnpm-lock.yaml").write_text("lockfileVersion: '10.0'")
        self.assertTrue(check._deps_changed(self.base_checkout, head, "packages/x"))
        (head / "pnpm-lock.yaml").write_text("lockfileVersion: '9.0'")
        (head / ".npmrc").write_text("registry=https://evil.example")
        self.assertTrue(check._deps_changed(self.base_checkout, head, "packages/x"))
        (head / "packages" / "x" / "pnpm-workspace.yaml").write_text("packages: []")
        self.assertTrue(check._deps_changed(self.base_checkout, head, "packages/x"))


if __name__ == "__main__":
    unittest.main()
