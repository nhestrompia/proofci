"""The agent-facing interface: `proofci scan`, `proofci local` and the fields
the JSON report carries for tools (fix-it hints, Lean errors with file/line,
Node disagreements)."""

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import check, cli, lean, local, sandbox, typescript  # noqa: E402


class StructuredErrorTests(unittest.TestCase):
    def test_lake_and_plain_shapes(self):
        text = ("error: Proofs.lean:12:4: unsolved goals\n"
                "Model.lean:9:0: error: unknown constant `x`\n"
                "warning: something else\n")
        self.assertEqual(lean.structured_errors(text), [
            {"file": "Proofs.lean", "line": 12, "column": 4, "message": "unsolved goals"},
            {"file": "Model.lean", "line": 9, "column": 0, "message": "unknown constant `x`"}])

    def test_report_json_carries_errors_and_disagreements(self):
        o = check.Outcome("t", "g", "a.ts::f", "g", True, check.UNPROVEN,
                          reason="the proof does not check:\nerror: Proofs.lean:4:2: type mismatch")
        report = check.Report(outcomes=[o], language="typescript")
        report.disagreements = ["a.ts::f [1, 2]"]
        data = report.to_json()
        self.assertEqual(data["guarantees"][0]["errors"],
                         [{"file": "Proofs.lean", "line": 4, "column": 2, "message": "type mismatch"}])
        self.assertEqual(data["disagreements"], ["a.ts::f [1, 2]"])


class ScanTests(unittest.TestCase):
    OUTCOME = {"module": "Bank", "functions": [
        {"function": "src/a.ts::ok", "translated": True},
        {"function": "src/a.ts::nope", "translated": False,
         "reason": "src/a.ts:3: `any` is not supported yet\nHow to fix: write the real type"}]}

    def test_probe_splits_hints(self):
        with tempfile.TemporaryDirectory() as tmp:
            done = sandbox.Result(0, "logs\n" + json.dumps(self.OUTCOME))
            with mock.patch.object(typescript.sandbox, "run", return_value=done) as run:
                outcome = typescript.probe(Path(tmp), ".", Path(tmp) / "w")
        self.assertEqual(run.call_args.args[0][:2], ["node", str(typescript.support_dir() / "probe.mjs")])
        nope = outcome["functions"][1]
        self.assertEqual((nope["reason"], nope["hint"]),
                         ("src/a.ts:3: `any` is not supported yet", "write the real type"))

    def test_probe_failure_is_an_error_not_an_empty_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            done = sandbox.Result(1, "node crashed")
            with mock.patch.object(typescript.sandbox, "run", return_value=done), \
                    self.assertRaises(typescript.Unsupported):
                typescript.probe(Path(tmp), ".", Path(tmp) / "w")

    def _manifest(self, root):
        (root / "proofci.yaml").write_text(
            "version: 1\nlanguage: typescript\ntargets:\n"
            "  - id: t\n    function: src/a.ts::ok\n    guarantees: [{id: g, theorem: g}]\n")

    def test_scan_prints_json(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._manifest(root)
            out, err = io.StringIO(), io.StringIO()
            with mock.patch.object(cli.typescript, "probe", return_value=self.OUTCOME), \
                    redirect_stdout(out), redirect_stderr(err):
                status = cli.main(["scan", "--repo", str(root)])
            self.assertEqual(status, 0)
            self.assertEqual(json.loads(out.getvalue())["functions"], self.OUTCOME["functions"])

    def test_scan_without_a_manifest_uses_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            with mock.patch.object(cli.typescript, "probe", return_value=self.OUTCOME) as probe:
                status = cli.main(["scan", "--repo", tmp, "--package", "pkg"])
            self.assertEqual(status, 0)
            self.assertEqual(probe.call_args.args[1], "pkg")

    def test_dev_json_flag_passes_through(self):
        with tempfile.TemporaryDirectory() as tmp:
            with mock.patch("proofci.dev.run", return_value=0) as run:
                cli.main(["dev", "--repo", tmp, "--json"])
            self.assertTrue(run.call_args.args[5])

    def test_scan_on_a_rust_repo_is_an_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proofci.yaml").write_text(
                "version: 1\ncrate: .\ntargets:\n"
                "  - id: t\n    function: crate::f\n    guarantees: [{id: g, theorem: g}]\n")
            err = io.StringIO()
            with redirect_stderr(err):
                status = cli.main(["scan", "--repo", str(root)])
            self.assertEqual(status, 2)
            self.assertIn("TypeScript", err.getvalue())


class DevJsonTests(unittest.TestCase):
    """`dev --json` must report unsupported functions on every run, cached or not."""

    def _repo(self, root):
        (root / "proofci").mkdir()
        (root / "proofci" / "Contract.lean").write_text(
            "/-- The fee stays capped. -/\ntheorem g (n : Int) (h : n ≤ 10) : True := by sorry\n")
        (root / "proofci" / "Proofs.lean").write_text("theorem g : True := by sorry\n")
        (root / "proofci.yaml").write_text(
            "version: 1\nlanguage: typescript\npackage: .\nlean: proofci\ntargets:\n"
            "  - id: t\n    function: src/a.ts::ok\n    guarantees: [{id: g, theorem: g}]\n"
            "  - id: u\n    function: src/a.ts::broken\n    guarantees: [{id: h, theorem: h}]\n")
        (root / "src").mkdir()
        (root / "src" / "a.ts").write_text(
            "export function ok() { return 1 }\nexport function broken() { return 2 }\n")

    def test_cached_run_keeps_unsupported(self):
        from proofci import dev, extract
        with tempfile.TemporaryDirectory() as tmp:
            root, work = Path(tmp) / "repo", Path(tmp) / "work"
            root.mkdir()
            self._repo(root)
            failure = {"src/a.ts::broken": "src/a.ts:2: `any` is not supported yet\nHow to fix: write the real type"}
            extraction = mock.Mock(failures=failure, lean_file=root / "proofci" / "Contract.lean",
                                   module="Repo", modelled=[], names={})
            built = mock.Mock(status=0, output="")

            def fake_assemble(ws_root, *args):
                ws_root.mkdir(parents=True, exist_ok=True)
                (ws_root / "Proofs.lean").write_text("theorem g : True := by sorry\n")

            with mock.patch.object(dev.typescript, "extract", return_value=extraction), \
                    mock.patch.object(dev.lean, "assemble", side_effect=fake_assemble), \
                    mock.patch.object(dev.lean, "_copy_lean_tree"), \
                    mock.patch.object(dev.lean, "_lake", return_value=built):
                captured = []
                status = dev.run(root, work, out=captured.append, as_json=True)
            self.assertEqual(status, 0)
            first = json.loads(captured[-1])["unsupported"]["src/a.ts::broken"]
            self.assertEqual(first["hint"], "write the real type")
            # Second run reuses the translation but must not lose the entry.
            with mock.patch.object(dev.lean, "_copy_lean_tree"), \
                    mock.patch.object(dev.lean, "_lake", return_value=built):
                captured = []
                status = dev.run(root, work, out=captured.append, as_json=True)
            self.assertEqual(json.loads(captured[-1])["unsupported"]["src/a.ts::broken"], first)

    def test_guarantee_entries_carry_claim_and_hypotheses(self):
        from proofci import dev
        with tempfile.TemporaryDirectory() as tmp:
            root, work = Path(tmp) / "repo", Path(tmp) / "work"
            root.mkdir()
            self._repo(root)
            extraction = mock.Mock(failures={}, lean_file=root / "proofci" / "Contract.lean",
                                   module="Repo", modelled=[], names={})
            built = mock.Mock(status=0, output="")

            def fake_assemble(ws_root, *args):
                ws_root.mkdir(parents=True, exist_ok=True)
                (ws_root / "Proofs.lean").write_text("x")

            with mock.patch.object(dev.typescript, "extract", return_value=extraction), \
                    mock.patch.object(dev.lean, "assemble", side_effect=fake_assemble), \
                    mock.patch.object(dev.lean, "_copy_lean_tree"), \
                    mock.patch.object(dev.lean, "_lake", return_value=built), \
                    mock.patch.object(dev.lean, "clone"), \
                    mock.patch.object(dev.lean, "comparator",
                                      return_value=mock.Mock(accepted=True, reason=None)):
                captured = []
                dev.run(root, work, judge=True, out=captured.append, as_json=True)
            g = json.loads(captured[-1])["guarantees"][0]
            self.assertEqual(g["claim"], "The fee stays capped.")
            self.assertEqual(g["hypotheses"], ["h : n ≤ 10"])


class LocalTests(unittest.TestCase):
    """`proofci local` must wrap the check in the same sandboxed container CI uses."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.repo.mkdir()
        self.calls = []

        def fake_run(command, **kwargs):
            self.calls.append((command, kwargs))
            if "merge-base" in command:
                return mock.Mock(returncode=0, stdout="deadbeef\n")
            if command[:2] == ["git", "-C"] and "rev-parse" in command:
                return mock.Mock(returncode=0, stdout="origin/main\n" if "--abbrev-ref" in command else "cafef00d\n")
            mounted = [arg.split(":")[0] for arg in command if isinstance(arg, str) and arg.endswith(":/out")]
            if mounted and ("check" in command or "scan" in command):
                (Path(mounted[0]) / "report.json").write_text('{"passed": true}\n')
            return mock.Mock(returncode=0, stdout="logs", stderr="")

        self.fake = fake_run
        patches = [mock.patch.object(local.subprocess, "run", side_effect=self.fake)]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def _report_dir(self, command):
        for arg in command:
            if arg.endswith(":/out"):
                return Path(arg.split(":")[0])
        return None

    def test_check_command_and_flags(self):
        status = local.run(self.repo, "HEAD", "base", "image:x")
        self.assertEqual(status, 0)
        check_call = next(c for c, _ in self.calls if "check" in c)
        self.assertIn("git", self.calls[0][0])
        self.assertEqual(check_call[:3], ["docker", "run", "--rm"])
        self.assertIn("--user", check_call)   # files in /out stay owned by the caller
        self.assertIn("none", check_call)
        for flag in ("--cap-drop", "--read-only", "--pids-limit"):
            self.assertIn(flag, check_call)
        self.assertIn("--report", check_call)

    def test_scan_runs_scan_inside(self):
        status = local.run(self.repo, "HEAD", "base", "image:x", scan=True)
        self.assertEqual(status, 0)
        inner = next(c for c, _ in self.calls if "scan" in c)
        self.assertIn("scan", inner)
        self.assertNotIn("check", inner)
        self.assertFalse(any(c[0] == "git" for c, _ in self.calls))  # no base checkout needed

    def test_fetch_first(self):
        local.run(self.repo, "HEAD", "base", "image:x", fetch_deps=True)
        fetch = next(c for c, _ in self.calls if "fetch" in c)
        self.assertNotIn("--network", fetch)  # only the fetch step keeps the network
        self.assertIn("/vendor", fetch)

    def test_no_report_is_an_error(self):
        def no_report(command, **kwargs):
            self.calls.append((command, kwargs))
            status = 0 if command[:2] in (["git", "-C"], ["tar", "-x"]) else 1
            return mock.Mock(returncode=status, stdout="", stderr="")
        with mock.patch.object(local.subprocess, "run", side_effect=no_report):
            status = local.run(self.repo, "HEAD", "base", "image:x")
        self.assertEqual(status, 2)

    def test_default_base_is_the_merge_base(self):
        out, errs = io.StringIO(), []
        with redirect_stdout(out):
            status = local.run(self.repo, None, "base", "image:x", err=errs.append)
        self.assertEqual(status, 0)
        merge = next(c for c, _ in self.calls if "merge-base" in c)
        self.assertEqual(merge[-2:], ["HEAD", "origin/main"])
        self.assertIn("deadbeef", "\n".join(errs))            # printed to stderr
        self.assertEqual(json.loads(out.getvalue())["base"], "deadbeef")

    def test_policy_head_says_it_is_not_ci(self):
        errs = []
        with redirect_stdout(io.StringIO()):
            local.run(self.repo, "HEAD", "head", "image:x", err=errs.append)
        self.assertTrue(any("not the result CI reports" in e for e in errs))

    def test_scan_fetch_without_a_manifest_is_an_error(self):
        with self.assertRaises(check.ConfigError):
            local.run(self.repo, "HEAD", "base", "image:x", scan=True, fetch_deps=True)
        self.assertFalse(any("fetch" in c for c, _ in self.calls))

    def test_base_ref_failure_is_an_error(self):
        def git_fails(command, **kwargs):
            if command[:2] == ["git", "-C"]:
                return mock.Mock(returncode=1, stderr=b"bad revision")
            return mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch.object(local.subprocess, "run", side_effect=git_fails), \
                self.assertRaises(check.ConfigError):
            local.run(self.repo, "HEAD", "base", "image:x")


if __name__ == "__main__":
    unittest.main()
