"""Offline entry-point comparisons against the owner's current-main baseline."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock
from scripts.tests import test_dispatch_retry_and_claim as dispatch
from scripts.tests import test_ci_step_failures as ci
from scripts.tests import test_github_workflow as workflow
from scripts.tests import test_lane_branch_identity as lane

BASE = "d8bb9efb9760348c9bb9c85019549bcbda593df9"
ROOT = Path(__file__).resolve().parents[2]

def baseline(repo, names):
    for name in names:
        (repo / "local/bin" / name).write_bytes(subprocess.check_output(
            ["git", "show", f"{BASE}:local/bin/{name}"], cwd=ROOT))


def setup_case(case, old, names):
    copy = shutil.copy2
    def copied(source, target):
        result = copy(source, target)
        if old and Path(source).name in names:
            baseline(Path(target).parents[2], [Path(target).name])
        return result
    with mock.patch.object(shutil, "copy2", side_effect=copied):
        case.setUp()


class OwnerConditionsTests(unittest.TestCase):
    def test_default_dispatch_router_and_event_match_main_despite_stale_knobs(self):
        for outcome in ("ok", "concurrency", "task-failure", "capacity"):
            observations = []
            for old in (True, False):
                with tempfile.TemporaryDirectory() as directory:
                    fx = dispatch.DispatchFixture(Path(directory))
                    (fx.cache / "watchdog/run-mode.json").unlink()
                    if old:
                        baseline(fx.repo, dispatch.COPIED)
                    (fx.cache / "watchdog/drain").touch()
                    (fx.cache / "watchdog/model-override").write_text("astra-all")
                    health = fx.cache / "watchdog/capacity/health-primary.json"
                    health.parent.mkdir(); health.write_text('{"state":"down"}')
                    fx.plant_claim(os.getpid())
                    if outcome == "capacity":
                        (fx.cache / "watchdog/max-codex-primary").write_text("0")
                    result = fx.run("--role", "prover", "--issue", "42", "--no-persona",
                                    "--worktree", str(fx.repo), "--skip-hook-check", "--", "test",
                                    MIPSTARRE_TEST_CODEX_MODE=outcome, MIPSTARRE_ACCOUNT_WAIT="0",
                                    MIPSTARRE_DISPATCH_ATTEMPTS="3")
                    rows = fx.registry_rows()
                    for row in rows:
                        for key in ("start", "end", "wall_s"):
                            row.pop(key, None)
                    event = subprocess.run(["python3", str(fx.repo / "local/bin/telemetry.py"),
                        "--repo-root", str(fx.repo), "event", "--date", "2026-09-14",
                        "--text", "offline compatibility"], env=fx.env(), capture_output=True,
                        text=True, check=True)
                    normalized = re.sub(r"wall_s: .*", "wall_s: <elapsed>", result.stdout)
                    observations.append(json.dumps([result.returncode, normalized, rows,
                        fx.marker.read_text() if fx.marker.exists() else "", event.stderr,
                        (fx.repo / "results/telemetry/events.md").read_text()]).replace(
                            str(fx.root), "<fixture>"))
                    self.assertFalse(list((fx.cache / "watchdog/capacity").glob("spool/*")))
                    self.assertFalse(list((fx.cache / "accounts").glob("*/[0-9]*")))
            self.assertEqual(*observations, outcome)

    def test_complete_ci_command_set_and_statuses_match_main(self):
        observations = []
        for old in (True, False):
            case = ci.CiStepFailureTests(); setup_case(case, old, ["ci.sh"])
            try:
                (case.repo / ".git/info").mkdir(exist_ok=True)
                (case.repo / ".git/info/exclude").write_text("scripts/check_umbrella_imports.py\n")
                (case.repo / "scripts/check_umbrella_imports.py").write_text("raise SystemExit(9)")
                manifest, commands = case.run_ci()
                commands = [re.sub(r"\b[0-9a-f]{40}\b", "<fixture-sha>", c) for c in commands]
                observations.append((commands, [(s["step"], s["outcome"])
                                               for s in manifest["steps"]]))
            finally:
                case.doCleanups()
        self.assertEqual(*observations)

    def test_complete_review_publication_matches_main(self):
        observations = []
        for old in (True, False):
            case = workflow.ReviewRoundCounterTests()
            setup_case(case, old, ["review.sh", "model_policy.py"])
            try:
                body = "## Findings\n\n- none\n\n## Review\n\nClean.\n\nVERDICT: APPROVED\n"
                result, _ = case.run_native_resume("compatibility", body)
                self.assertEqual(result.returncode, 0, result.stderr)
                reviews = case.gh.payloads("POST", r"^pulls/7/reviews$")
                statuses = case.gh.payloads("POST", r"^statuses/")
                observations.append((len(reviews), "VERDICT: APPROVED" in reviews[0]["body"],
                                     [(s["context"], s["state"]) for s in statuses]))
            finally:
                case.doCleanups()
        self.assertEqual(*observations)

    def test_complete_lane_parks_failed_worker_and_finishes_success(self):
        for code in (9, 0):
            case = lane.LaneIdentityFailClosedTests(); case.setUp()
            try:
                repo, tools = case.tmp / "checkout", case.tmp / "bin"
                local = repo / "local/bin"
                (repo / ".lake").mkdir(); (repo / ".lake/fixture").touch()
                (case.tmp / "cache/watchdog/max-codex-primary").write_text("1")
                for name, body in {
                    "git": 'case "$*" in *rev-list*) echo 1;; *rev-parse*|*merge-base*) echo deadbeef;; esac',
                    "sleep": ":", "lake": 'echo build >> "$HOME/phases"',
                }.items():
                    (tools / name).write_text("#!/bin/sh\n" + body + "\n")
                    (tools / name).chmod(0o755)
                (local / "gh_common.py").write_text(
                    'import json,sys\nprint(json.dumps({"title":"Prove Pauli", "body":"", '
                    '"state":"OPEN", "head":{"sha":"deadbeef"}}))\n')
                for name, body in {
                    "worktree_resolve.sh": 'echo "$MIPSTARRE_CHECKOUT"',
                    "worktree-setup.sh": ":", "dispatch.sh": f"exit {code}",
                    "pr_open.py": 'echo publish >> "$HOME/phases"; echo 552',
                    "ci.sh": 'echo ci >> "$HOME/phases"',
                    "review.sh": 'echo review >> "$HOME/phases"',
                }.items():
                    (local / name).write_text("#!/bin/sh\n" + body + "\n")
                    (local / name).chmod(0o755)
                result = case._run("342", "slug", branch="issue-342-slug", issue_ok=True)
                phases = case.tmp / "phases"
                if code:
                    self.assertEqual(result.returncode, 1, result.stderr)
                    self.assertFalse(phases.exists())
                    self.assertIn("dispatch-failed", (case.lanes / "342.needs-attention").read_text())
                else:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(phases.read_text().splitlines(), ["build", "publish", "ci", "review"])
                    self.assertIn("HEAD=deadbeef", (case.lanes / "342.done").read_text())
            finally:
                case.doCleanups()
