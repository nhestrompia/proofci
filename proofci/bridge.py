"""Tie the Lean view of each TypeScript function to the model of JavaScript.

Users prove guarantees about a *view*: the Lean the translator wrote for a
function (`typescript/translate.mjs`). The bridge is the missing link. A second,
independent lowering (`spike/core/lower.mjs`) turns the same source into Core, a
small-step model of JavaScript, and a generated theorem says the view and Core
agree on every input. With the bridge checked, a guarantee about the view is a
guarantee about the JavaScript semantics, not just about Lean code that
happened to pass a test.

Everything the bridge trusts comes from the image: the generator, Core, the
number model and the tactics (`/opt/proofci/spike/core`). The pull request
supplies only the source text that is lowered, the same way it does for the
translator. Generating and checking both run in the sandbox.

Each translated function ends up with one of three statuses:

proved   The bridge theorem checked with only the standard axioms.
tested   The bridge was not generated, did not finish, or did not check, but the
         comparison with Node found no difference. The guarantee still holds of
         the view; that the view matches JavaScript is tested here, not proved.
failed   Node and the view disagree (decided in `check.py`, which blocks).

A bridge that doesn't check is *never* called failed. The tactics report
"STUCK" both when a function uses a form they don't cover yet and when the
view is wrong (a planted `<=` for `<` gives exactly the same message), so the
output can't say which it was. Calling it failed would block pull requests on
tactic weakness, and calling it proved would be a lie, so it is `tested`, and
`require_bridge` in the policy is how a repository turns that into a block.
"""

import json
import os
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

from . import sandbox
from .lean import PERMITTED_AXIOMS

PROVED, TESTED, FAILED = "proved", "tested", "failed"

DEFAULT_TIMEOUT = 120      # seconds for one function's bridge to check
DEFAULT_BUDGET = 900       # seconds for all of them together
MAX_JOBS = 4               # Lean processes at once
GENERATE_TIMEOUT = 300

NO_ASYNC_BRIDGE = "no bridge for async code yet"

AXIOMS = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", re.M)
THEOREMS = re.compile(r"^#print axioms (\S+)$", re.M)
ERROR = re.compile(r"^\S+:\d+:\d+: error:? ?(.*)$", re.M)
ANSI = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")


@dataclass
class FunctionStatus:
    """What is known about how one function's view relates to JavaScript."""
    function: str
    status: str
    reason: str = ""
    seconds: float = None
    guarantees: list = field(default_factory=list)

    def entry(self):
        return {"function": self.function, "status": self.status, "reason": self.reason,
                "seconds": self.seconds, "guarantees": self.guarantees}


def toolchain_dir():
    """The generator and the Lean libraries it needs, in the image. Never the pull request's."""
    installed = Path("/opt/proofci/spike/core")
    return Path(os.environ.get("PROOFCI_BRIDGE", installed))


def available():
    return (toolchain_dir() / "action_bridge.mjs").is_file() and \
        (toolchain_dir() / ".lake" / "build" / "lib" / "lean" / "Spike" / "Tac.olean").is_file()


def settings(timeout=None, budget=None, jobs=None):
    """Limits from the arguments, then the environment, then the defaults."""
    def number(value, name, default):
        value = value if value is not None else os.environ.get(name)
        try:
            return max(1, int(value)) if value not in (None, "") else default
        except ValueError:
            return default
    return (number(timeout, "PROOFCI_BRIDGE_TIMEOUT", DEFAULT_TIMEOUT),
            number(budget, "PROOFCI_BRIDGE_BUDGET", DEFAULT_BUDGET),
            min(MAX_JOBS, number(jobs, "PROOFCI_BRIDGE_JOBS", max(1, min(MAX_JOBS, os.cpu_count() or 1)))))


def _message(output, limit=500):
    """The first Lean error, cut to a size a report can carry."""
    text = ANSI.sub("", output)
    found = ERROR.search(text)
    if not found:
        lines = [line for line in text.splitlines() if line.strip()]
        return (lines[-1] if lines else "no output")[:limit]
    first = found.group(1).strip()
    return (first or "error")[:limit]


def classify(lean_status, output, timed_out, theorems, timeout):
    """Status and reason for one function from Lean's verdict on its bridge file.

    `theorems` names the bridge theorems in the file (the function and what it calls). It is
    `proved` only if Lean exited cleanly *and* reported, for every one of them, that it depends
    on nothing beyond the standard axioms. Anything else is `tested`: see the module docstring
    for why a failed proof is not `failed`."""
    if timed_out:
        return TESTED, f"the bridge proof did not finish in {timeout} seconds"
    text = ANSI.sub("", output)
    if lean_status in (137, -9):
        return TESTED, "the bridge proof ran out of memory"
    reported = {name: (axioms or "") for name, axioms in AXIOMS.findall(text)}
    if lean_status != 0:
        return TESTED, "the bridge theorem did not check: " + _message(text)
    if not theorems:
        return TESTED, "the bridge file states no theorem"
    for name in theorems:
        if name not in reported:
            return TESTED, f"the bridge theorem `{name}` did not report its axioms"
        used = {a.strip() for a in reported[name].split(",") if a.strip()}
        extra = sorted(used - set(PERMITTED_AXIOMS))
        if extra:
            return TESTED, f"the bridge proof depends on {', '.join(extra)}"
    return PROVED, ""


def generate(extraction, targets, out: Path):
    """Write one Lean file per target into `out`: {target: file name or None}, {target: reason}.

    The generator runs in the sandbox on the code the translator read, and gets the very Lean
    text that proofs are written against, so the theorem is about those definitions."""
    scripts = toolchain_dir()
    checkout, policy = Path(extraction.checkout), Path(extraction.policy)
    config = out / "config.json"
    config.write_text(json.dumps({
        "root": str(extraction.root), "repository": str(checkout), "policyRoot": str(policy), "viewFile": str(extraction.lean_file),
        "out": str(out), "targets": list(targets),
        "assumes": [{"call": call, "signature": signature} for call, signature in extraction.assumptions.items()],
        "effects": extraction.effect_entries,
    }))
    result = sandbox.run(["node", str(scripts / "action_bridge.mjs"), str(config)],
                         readable=[checkout, policy, scripts, Path(extraction.lean_file).parent, out],
                         binds=getattr(extraction, "binds", ()), writable=[out], cwd=out, timeout=GENERATE_TIMEOUT)
    if result.status != 0 or not result.output.strip():
        why = "timed out" if result.timed_out else _message(result.output)
        return {}, {t: f"the bridge generator failed: {why}" for t in targets}
    try:
        found = json.loads(result.output.splitlines()[-1])["results"]
    except (ValueError, KeyError):
        return {}, {t: "the bridge generator gave no result" for t in targets}
    files = {t: found[t]["file"] for t in targets if t in found and "file" in found[t]}
    reasons = {t: found.get(t, {}).get("reason", "the bridge generator gave no result") for t in targets if t not in files}
    return files, reasons


def check_one(path: Path, timeout):
    """Lean on one bridge file, in the sandbox, with the image's libraries."""
    text = path.read_text()
    theorems = THEOREMS.findall(text)
    started = time.monotonic()
    result = sandbox.run(["lake", "env", "lean", str(path)], readable=[path.parent], writable=[],
                         cwd=toolchain_dir(), timeout=timeout)
    seconds = round(time.monotonic() - started, 1)
    status, reason = classify(result.status, result.output, result.timed_out, theorems, timeout)
    return status, reason, seconds


def run(extraction, work: Path, functions, timeout=None, budget=None, jobs=None):
    """Bridge `functions` (each `file.ts::name`). Returns {function: FunctionStatus}.

    Every function gets a status. None of them is ever `failed` here; `check.py` decides that
    from the comparison with Node, which runs first."""
    timeout, budget, jobs = settings(timeout, budget, jobs)
    results = {}
    todo = []
    for function in functions:
        if function in (extraction.effects or {}):
            results[function] = FunctionStatus(function, TESTED, NO_ASYNC_BRIDGE)
        else:
            todo.append(function)
    if not todo:
        return results
    if not available():
        for function in todo:
            results[function] = FunctionStatus(function, TESTED, "the bridge is not installed in this toolchain image")
        return results
    out = work / "bridge"
    out.mkdir()
    files, reasons = generate(extraction, todo, out)
    for function, reason in reasons.items():
        results[function] = FunctionStatus(function, TESTED, reason)
    deadline = time.monotonic() + budget
    lock = threading.Lock()

    def one(function):
        left = deadline - time.monotonic()
        if left < 1:
            status = FunctionStatus(function, TESTED, f"the bridge time budget ({budget} seconds) ran out before this function was checked")
        else:
            try:
                state, reason, seconds = check_one(out / files[function], max(1, min(timeout, int(left))))
                status = FunctionStatus(function, state, reason, seconds)
            except Exception as error:  # a crash here must not turn into a pass
                status = FunctionStatus(function, TESTED, f"the bridge could not be run: {error}")
        with lock:
            results[function] = status

    with ThreadPoolExecutor(max_workers=max(1, min(jobs, len(files) or 1))) as pool:
        list(pool.map(one, list(files)))
    return results
