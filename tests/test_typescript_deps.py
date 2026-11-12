"""Installing a TypeScript project's packages for the type checker.

These tests replace the sandbox and the package managers with small fakes, so
they check ProofCI's own decisions: which lockfile, which command, what is
removed from the copy, and where the result goes. The real installers run in
the toolchain image (see docs/typescript.md).
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import sandbox, typescript  # noqa: E402
from proofci.extract import FetchError, Unsupported  # noqa: E402

REGISTRY = "https://registry.npmjs.org/left-pad/-/left-pad-1.3.0.tgz"


def write(path, text=""):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


def npm_lock(*urls):
    return json.dumps({"lockfileVersion": 3, "packages": {
        "": {"name": "app"},
        **{f"node_modules/p{i}": {"version": "1.0.0", "resolved": url} for i, url in enumerate(urls)}}})


class FakeRunner:
    """Runs the install command directly, with a fake package manager that
    writes a `node_modules` where it is told to run."""

    def __init__(self, status=0):
        self.calls, self.status = [], status

    def __call__(self, argv, *, writable, cwd, readable=(), binds=(), env=None, timeout=600, network=False):
        cwd = Path(cwd)
        self.calls.append({"argv": [str(a) for a in argv], "cwd": cwd, "network": network, "env": env or {},
                           "config": sorted(p.name for p in cwd.iterdir()),
                           "writable": [Path(w) for w in writable]})
        if self.status == 0:
            write(cwd / "node_modules" / "left-pad" / "index.d.ts", "export declare function leftPad(s: string): string;")
            (cwd / "node_modules" / ".bin").mkdir()
            (cwd / "node_modules" / ".bin" / "tool").symlink_to("../left-pad/index.d.ts")
        return sandbox.Result(self.status, "boom" if self.status else "")


class Repo(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.tmp = Path(self._tmp.name)
        self.repo = self.tmp / "repo"
        write(self.repo / "package.json", json.dumps({"name": "app", "dependencies": {"left-pad": "1.3.0"}}))
        write(self.repo / "src" / "a.ts", "export const a = 1;")
        write(self.repo / ".git" / "HEAD", "ref")


class LockfileTests(Repo):
    def test_nearest_lockfile_wins_and_climbs_to_the_workspace_root(self):
        write(self.repo / "pnpm-lock.yaml", "lockfileVersion: 9")
        write(self.repo / "packages" / "core" / "package.json", "{}")
        self.assertEqual(typescript.find_lockfile(self.repo, "packages/core"), (self.repo.resolve(), "pnpm-lock.yaml", "pnpm"))
        write(self.repo / "packages" / "core" / "yarn.lock", "# yarn lockfile v1")
        self.assertEqual(typescript.find_lockfile(self.repo, "packages/core")[2], "yarn")

    def test_manager_follows_the_file(self):
        write(self.repo / "package-lock.json", npm_lock())
        self.assertEqual(typescript.find_lockfile(self.repo, ".")[2], "npm")
        self.assertIsNone(typescript.find_lockfile(self.tmp, "."))  # never leaves the checkout

    def test_a_symlinked_lockfile_is_ignored(self):
        write(self.tmp / "elsewhere.json", npm_lock())
        (self.repo / "package-lock.json").symlink_to(self.tmp / "elsewhere.json")
        self.assertIsNone(typescript.find_lockfile(self.repo, "."))

    def test_npm_v1_lockfiles_may_only_name_the_public_registry(self):
        lock = write(self.repo / "package-lock.json", json.dumps({"lockfileVersion": 1, "dependencies": {
            "a": {"resolved": REGISTRY}}}))
        typescript.check_lockfile(lock, "npm")
        for bad in ("git+ssh://git@github.com/o/r.git#abc", "http://registry.npmjs.org/x.tgz",
                    "https://evil.example/x.tgz", "file:../local"):
            lock.write_text(json.dumps({"lockfileVersion": 1, "dependencies": {"a": {"resolved": bad}}}))
            with self.assertRaises(Unsupported, msg=bad) as caught:
                typescript.check_lockfile(lock, "npm")
            self.assertIn("public npm registry", str(caught.exception))

    def test_packages_from_elsewhere_are_left_out_of_an_npm_install(self):
        write(self.repo / "package.json", json.dumps({"name": "app", "dependencies": {"left-pad": "1", "private-lib": "github:o/r"},
                                                      "devDependencies": {"sheet": "https://cdn.example/sheet.tgz"}}))
        lock = write(self.repo / "package-lock.json", json.dumps({"lockfileVersion": 3, "packages": {
            "": {"dependencies": {"left-pad": "1", "private-lib": "github:o/r"}, "devDependencies": {"sheet": "https://cdn.example/sheet.tgz"}},
            "node_modules/left-pad": {"resolved": REGISTRY, "integrity": "sha512-x"},
            "node_modules/private-lib": {"resolved": "git+ssh://git@github.com/o/r.git#abc"},
            "node_modules/sheet": {"resolved": "https://cdn.example/sheet.tgz"},
            "node_modules/core": {"resolved": "packages/core", "link": True}}}))
        typescript.check_lockfile(lock, "npm")
        copy = self.tmp / "copy"
        copy.mkdir()
        (copy / "package.json").write_text((self.repo / "package.json").read_text())
        (copy / "package-lock.json").write_text(lock.read_text())
        self.assertEqual(typescript.drop_foreign_packages(copy), ["private-lib", "sheet"])
        data = json.loads((copy / "package-lock.json").read_text())
        self.assertEqual(sorted(data["packages"]), ["", "node_modules/core", "node_modules/left-pad"])
        self.assertEqual(data["packages"][""], {"dependencies": {"left-pad": "1"}, "devDependencies": {}})
        manifest = json.loads((copy / "package.json").read_text())
        self.assertEqual(manifest["dependencies"], {"left-pad": "1"})
        self.assertEqual(manifest["devDependencies"], {})
        self.assertIn("git+ssh", lock.read_text())  # the project's own files are not touched

    def test_registry_packages_forget_that_they_needed_a_dropped_one(self):
        copy = self.tmp / "copy"
        write(copy / "package.json", json.dumps({"dependencies": {"common": "1"}}))
        write(copy / "package-lock.json", json.dumps({"lockfileVersion": 3, "packages": {
            "": {"dependencies": {"common": "1"}},
            "node_modules/common": {"resolved": REGISTRY, "dependencies": {"deferred": "3", "other": "1"}},
            "node_modules/other": {"resolved": REGISTRY},
            "node_modules/deferred": {"resolved": "git+ssh://git@github.com/o/deferred.git#abc"},
            "node_modules/deferred/node_modules/inner": {"resolved": REGISTRY}}}))
        self.assertEqual(typescript.drop_foreign_packages(copy), ["deferred"])
        data = json.loads((copy / "package-lock.json").read_text())
        self.assertEqual(sorted(data["packages"]), ["", "node_modules/common", "node_modules/other"])
        self.assertEqual(data["packages"]["node_modules/common"]["dependencies"], {"other": "1"})

    def test_a_registry_only_lockfile_loses_nothing(self):
        copy = self.tmp / "copy"
        write(copy / "package-lock.json", npm_lock(REGISTRY))
        self.assertEqual(typescript.drop_foreign_packages(copy), [])

    def test_nested_npm_v1_dependencies_are_checked(self):
        lock = write(self.repo / "package-lock.json", json.dumps({"lockfileVersion": 1, "dependencies": {
            "a": {"resolved": REGISTRY, "dependencies": {"b": {"resolved": "https://evil.example/b.tgz"}}}}}))
        with self.assertRaises(Unsupported):
            typescript.check_lockfile(lock, "npm")

    def test_workspace_links_in_an_npm_lock_are_fine(self):
        lock = write(self.repo / "package-lock.json", json.dumps({"packages": {
            "": {}, "node_modules/core": {"resolved": "packages/core", "link": True}}}))
        typescript.check_lockfile(lock, "npm")

    def test_pnpm_lock(self):
        ok = write(self.repo / "pnpm-lock.yaml",
                   "packages:\n  left-pad@1.3.0:\n    resolution: {integrity: sha512-abc}\n")
        typescript.check_lockfile(ok, "pnpm")
        ok.write_text("packages:\n  x@1.0.0:\n    resolution: {tarball: https://registry.npmjs.org/x/-/x-1.0.0.tgz}\n")
        typescript.check_lockfile(ok, "pnpm")
        ok.write_text("packages:\n  x@1.0.0:\n    resolution: {tarball: https://evil.example/x.tgz}\n")
        with self.assertRaises(Unsupported):
            typescript.check_lockfile(ok, "pnpm")
        ok.write_text("packages:\n  x@1.0.0:\n    resolution: {type: git, repo: https://github.com/o/r, commit: abc}\n")
        with self.assertRaises(Unsupported):
            typescript.check_lockfile(ok, "pnpm")

    def test_yarn_lock(self):
        lock = write(self.repo / "yarn.lock", f'left-pad@1.3.0:\n  version "1.3.0"\n  resolved "{REGISTRY}#abc"\n')
        typescript.check_lockfile(lock, "yarn")
        lock.write_text('x@1:\n  resolved "https://github.com/o/r/archive/abc.tar.gz"\n')
        with self.assertRaises(Unsupported):
            typescript.check_lockfile(lock, "yarn")

    def test_yarn_berry_is_refused(self):
        lock = write(self.repo / "yarn.lock", "__metadata:\n  version: 8\n")
        with self.assertRaises(Unsupported) as caught:
            typescript.check_lockfile(lock, "yarn")
        self.assertIn("Yarn Berry", str(caught.exception))


class InstallTests(Repo):
    def install(self, runner=None, lock=("package-lock.json", npm_lock(REGISTRY)), package="."):
        write(self.repo / lock[0], lock[1])
        vendor, work = self.tmp / "vendor", Path(tempfile.mkdtemp(dir=self.tmp))
        runner = runner or FakeRunner()
        with mock.patch.object(sandbox, "run", runner):
            modules = typescript.install(self.repo, package, vendor, work)
        return runner, vendor, modules

    def test_npm_runs_ci_without_scripts_and_with_the_network(self):
        runner, vendor, modules = self.install()
        call = runner.calls[0]
        self.assertTrue(call["network"])
        self.assertEqual(call["argv"][0], "node")
        for flag in ("ci", "--ignore-scripts", "--registry", "https://registry.npmjs.org/"):
            self.assertIn(flag, call["argv"])
        self.assertEqual(modules, ["."])
        self.assertTrue((vendor / "modules" / "node_modules" / "left-pad" / "index.d.ts").is_file())
        self.assertEqual(json.loads((vendor / "dependencies.json").read_text()),
                         {"lockfile": "package-lock.json", "manager": "npm", "modules": ["."], "skipped": []})

    def test_the_manager_runs_in_a_copy_that_has_no_project_settings(self):
        write(self.repo / ".npmrc", "script-shell=/tmp/evil\n")
        write(self.repo / ".pnpmfile.cjs", "module.exports = {}")
        write(self.repo / ".yarnrc.yml", "yarnPath: .yarn/releases/evil.cjs\n")
        write(self.repo / ".yarn" / "releases" / "evil.cjs", "")
        runner, _, _ = self.install()
        call = runner.calls[0]
        self.assertNotEqual(call["cwd"].resolve(), self.repo.resolve())
        self.assertEqual(call["config"], ["package-lock.json", "package.json", "src"])
        self.assertTrue((self.repo / ".npmrc").exists())  # the checkout itself is untouched
        self.assertFalse((self.repo / "node_modules").exists())

    def test_pnpm_and_yarn_commands_turn_off_project_code(self):
        runner, _, _ = self.install(lock=("pnpm-lock.yaml", "lockfileVersion: '9.0'\n"))
        argv = runner.calls[0]["argv"]
        for flag in ("install", "--frozen-lockfile", "--ignore-scripts", "--ignore-pnpmfile"):
            self.assertIn(flag, argv)
        self.assertTrue(argv[1].endswith("pnpm.cjs"))
        (self.repo / "pnpm-lock.yaml").unlink()
        runner, _, _ = self.install(lock=("yarn.lock", "# yarn lockfile v1\n"))
        argv = runner.calls[0]["argv"]
        for flag in ("--frozen-lockfile", "--ignore-scripts", "--use-yarnrc"):
            self.assertIn(flag, argv)
        self.assertTrue(argv[1].endswith("yarn.js"))

    def test_a_monorepo_installs_at_the_lockfile_and_keeps_every_node_modules(self):
        write(self.repo / "packages" / "core" / "package.json", json.dumps({"dependencies": {"x": "1"}}))

        class Workspace(FakeRunner):
            def __call__(self, argv, **kwargs):
                result = super().__call__(argv, **kwargs)
                write(Path(kwargs["cwd"]) / "packages" / "core" / "node_modules" / "x" / "index.d.ts")
                return result

        runner, vendor, modules = self.install(Workspace(), package="packages/core")
        self.assertEqual(sorted(modules), [".", "packages/core"])
        self.assertTrue((vendor / "modules" / "packages" / "core" / "node_modules" / "x").is_dir())

    def test_a_failed_install_is_a_download_problem(self):
        with self.assertRaises(FetchError) as caught:
            self.install(FakeRunner(status=1))
        self.assertIn("could not install", str(caught.exception))

    def test_nothing_to_install_without_a_lockfile_or_dependencies(self):
        runner = FakeRunner()
        with mock.patch.object(sandbox, "run", runner):
            self.assertIsNone(typescript.install(self.repo, ".", self.tmp / "v1", self.tmp))
            write(self.repo / "package.json", json.dumps({"name": "app"}))
            write(self.repo / "package-lock.json", npm_lock())
            self.assertIsNone(typescript.install(self.repo, ".", self.tmp / "v2", self.tmp))
        self.assertEqual(runner.calls, [])
        self.assertFalse((self.tmp / "v1" / "dependencies.json").exists())

    def test_a_pnpm_lockfile_that_leaves_the_registry_is_refused_before_anything_runs(self):
        runner = FakeRunner()
        with self.assertRaises(Unsupported):
            self.install(runner, lock=("pnpm-lock.yaml", "packages:\n  x@1:\n    resolution: {tarball: https://evil.example/x.tgz}\n"))
        self.assertEqual(runner.calls, [])

    def test_npm_skips_foreign_packages_and_records_them(self):
        runner, vendor, _ = self.install(lock=("package-lock.json", npm_lock(REGISTRY, "git+ssh://git@github.com/o/r.git")))
        self.assertEqual(json.loads((vendor / "dependencies.json").read_text())["skipped"], ["p1"])


class PrepareTests(Repo):
    def vendor(self):
        vendor = self.tmp / "vendor"
        write(vendor / "modules" / "node_modules" / "left-pad" / "index.d.ts", "x")
        write(vendor / "dependencies.json", json.dumps({"modules": ["."]}))
        return vendor

    def test_without_installed_packages_the_checkout_is_used_as_it_is(self):
        self.assertEqual(typescript.prepare(self.repo, self.tmp, None), (self.repo, []))
        (self.tmp / "vendor").mkdir()
        self.assertEqual(typescript.prepare(self.repo, self.tmp, self.tmp / "vendor"), (self.repo, []))

    def test_installed_packages_are_mounted_into_a_copy(self):
        vendor = self.vendor()
        staged, binds = typescript.prepare(self.repo, self.tmp / "work", vendor)
        self.assertNotEqual(staged.resolve(), self.repo.resolve())
        self.assertTrue((staged / "src" / "a.ts").is_file())
        self.assertFalse((staged / ".git").exists())
        self.assertEqual(binds, [(vendor / "modules" / "node_modules", staged / "node_modules")])
        self.assertTrue((staged / "node_modules").is_dir())
        self.assertEqual(list((staged / "node_modules").iterdir()), [])  # filled by the sandbox, not copied
        self.assertFalse((self.repo / "node_modules").exists())  # the checkout is not written to

    def test_the_translator_and_the_comparison_get_the_copy_and_the_mounts(self):
        vendor = self.vendor()
        seen = []

        def fake_run(argv, **kwargs):
            seen.append(kwargs)
            config = json.loads(Path(argv[2]).read_text())
            self.assertNotEqual(Path(config["root"]).resolve(), self.repo.resolve())
            self.assertEqual(kwargs["binds"], [(vendor / "modules" / "node_modules", Path(config["root"]) / "node_modules")])
            result = {"names": {}, "failures": {}, "signatures": {}, "assumed": {}, "files": {}, "imports": {}}
            return sandbox.Result(0, json.dumps(result))

        work = self.tmp / "work"
        work.mkdir()
        with mock.patch.object(sandbox, "run", fake_run):
            extraction = typescript.extract(self.repo, ".", work, ["src/a.ts::a"], vendor_dir=vendor)
        self.assertEqual(len(seen), 1)
        self.assertEqual(extraction.binds[0][1], extraction.checkout / "node_modules")


class HintTests(Repo):
    def failing(self, vendor=None, reason="src/a.ts:3: the type `Point` is not supported yet"):
        def fake_run(argv, **kwargs):
            return sandbox.Result(0, json.dumps({"fatal": reason}))
        work = Path(tempfile.mkdtemp(dir=self.tmp))
        with mock.patch.object(sandbox, "run", fake_run):
            with self.assertRaises(Unsupported) as caught:
                typescript.extract(self.repo, ".", work, ["src/a.ts::a"], vendor_dir=vendor)
        return str(caught.exception)

    def test_missing_lockfile_is_named(self):
        self.assertIn("commit package-lock.json", self.failing())

    def test_missing_install_is_named_when_there_is_a_lockfile(self):
        write(self.repo / "package-lock.json", npm_lock())
        self.assertIn("proofci fetch", self.failing())

    def test_a_refused_lockfile_is_the_reason(self):
        write(self.repo / "pnpm-lock.yaml", "packages:\n  x@1:\n    resolution: {tarball: https://evil.example/x.tgz}\n")
        vendor = self.tmp / "vendor"
        with self.assertRaises(Unsupported):
            typescript.install(self.repo, ".", vendor, self.tmp)
        self.assertIn("public npm registry", self.failing(vendor))

    def test_other_failures_are_left_alone(self):
        self.assertEqual(self.failing(reason="src/a.ts:3: `while` is not welcome"), "src/a.ts:3: `while` is not welcome")

    def test_a_project_without_dependencies_gets_no_hint(self):
        write(self.repo / "package.json", json.dumps({"name": "app"}))
        self.assertNotIn("installed", self.failing())


if __name__ == "__main__":
    unittest.main()
