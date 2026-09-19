#!/usr/bin/env python3
"""Unit tests for the publication guard of ``results/telemetry/owner-tools/lane.sh``.

Audit report f75e6fb6 (issue #552) found a live publication bypass: when
``pr_open.py`` failed, the lane pushed the branch itself with
``MIPSTARRE_SKIP_HOOKS=1`` and retried, so a pr_open failure could still publish
with the hooks skipped.  The fallback was removed; a pr_open failure now leaves
the lane through ``fail``, which records needs-attention and exits non-zero.
These tests are offline: the publication statement and the ``fail`` helper are
lifted verbatim out of ``lane.sh`` and run in a sandbox against a stub
``pr_open.py`` that fails and a stub ``git`` that records every call.
"""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LANE_SH = ROOT / "results" / "telemetry" / "owner-tools" / "lane.sh"


def statement(prefix: str) -> str:
    """The lane.sh statement starting with ``prefix``, with its continuations."""
    lines = LANE_SH.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    end = start
    while lines[end].rstrip().endswith("\\"):
        end += 1
    return "\n".join(lines[start : end + 1])


class PublicationBypassRemovedTests(unittest.TestCase):
    def test_lane_never_skips_hooks_and_never_pushes_itself(self):
        code = [
            line
            for line in LANE_SH.read_text().splitlines()
            if not line.lstrip().startswith("#")
        ]
        for banned in ("MIPSTARRE_SKIP_HOOKS", "push github"):
            self.assertFalse(
                [line for line in code if banned in line], f"{banned} is still run"
            )

    def test_failed_pr_open_fails_the_lane_without_publishing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "local" / "bin").mkdir(parents=True)
            (root / "state").mkdir()
            (root / "stub-bin").mkdir()
            for path, body in (
                (root / "local" / "bin" / "pr_open.py", "#!/bin/sh\nexit 1\n"),
                (root / "stub-bin" / "git", '#!/bin/sh\necho "$@" >> "$GIT_CALLS"\n'),
            ):
                path.write_text(body)
                path.chmod(0o755)
            harness = root / "harness.sh"
            harness.write_text(
                "set -u\n"
                'N=552; BR=issue-552-fixture; W="$PWD"; TITLE=fixture\n'
                'PRB="$PWD/pr.md"; STATE="$PWD/state"\n'
                + statement("fail() {")
                + "\n"
                + statement("PR=$(local/bin/pr_open.py")
                + "\necho PUBLISHED=$PR\n"
            )
            env = dict(os.environ, GIT_CALLS=str(root / "git-calls.txt"))
            env["PATH"] = f"{root / 'stub-bin'}:{env['PATH']}"
            proc = subprocess.run(
                ["bash", str(harness)], cwd=root, env=env, capture_output=True, text=True
            )
            self.assertNotEqual(proc.returncode, 0, proc.stdout)
            self.assertNotIn("PUBLISHED=", proc.stdout)
            self.assertIn("pr_open failed", proc.stdout + proc.stderr)
            self.assertTrue((root / "state" / "552.needs-attention").is_file())
            self.assertFalse((root / "git-calls.txt").exists())


if __name__ == "__main__":
    unittest.main()
