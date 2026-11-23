"""The trusted Lean base must be fully kernel-checkable.

A declaration skipped with `debug.skipKernelTC` (or never checked because it
relies on `native_decide`/`implemented_by`/`extern`/`sorry`/`axiom`) is invisible
to `#print axioms` — the external kernel replay the comparator runs would reject
it anyway. Keep this list in sync with the `COPY spike/...` entries in
`toolchain/Dockerfile` and `toolchain/Release.Dockerfile`.
"""

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

TRUSTED = [
    "spike/core/Core.lean",
    "spike/core/F64.lean",
    "spike/core/ProofciJs.lean",
    "spike/core/ProofciAsync.lean",
    "spike/core/CoreAsync.lean",
    "spike/core/Spike/Rules.lean",
    "spike/core/Spike/LoopInd.lean",
    "spike/core/Spike/Safe.lean",
    "spike/core/Spike/Sim.lean",
    "spike/core/Spike/Tac.lean",
    "spike/core/Spike/ASim.lean",
    "proofci/lean/ProofciJs.lean",
    "proofci/lean/ProofciAsync.lean",
]

FORBIDDEN = re.compile(
    r"debug\.skipKernelTC|native_decide|implemented_by|\bextern\b|\bsorry\b|\baxiom\b"
)


class TestTrustedLean(unittest.TestCase):
    def test_no_unchecked_declarations(self):
        offenders = []
        for name in TRUSTED:
            text = (ROOT / name).read_text()
            for lineno, line in enumerate(text.splitlines(), 1):
                if FORBIDDEN.search(line):
                    offenders.append(f"{name}:{lineno}: {line.strip()}")
        self.assertEqual(offenders, [])

    def test_listed_files_exist(self):
        missing = [name for name in TRUSTED if not (ROOT / name).exists()]
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
