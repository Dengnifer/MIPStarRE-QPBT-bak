#!/usr/bin/env python3
"""Bounded owner merge service for the active relay-3/cap11 episode.

The service is intentionally conservative: each tick records remote/main
identity, dirty-primary and gate state, reports the oldest eligible PR age, and
only delegates an exact-head merge to ``pr_merge.py`` after all local checks
pass. Refreshing stale branches remains a separate lane-owned operation.
"""

from __future__ import annotations

import argparse
from contextlib import redirect_stdout
from datetime import datetime, timezone
import fcntl
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
CACHE = Path(os.environ.get("MIPSTARRE_CACHE_ROOT", Path.home() / ".cache/mipstarre-dev"))
DAEMON = CACHE / "watchdog" / "daemon"
LOCK = DAEMON / "space-cap5.lock"
LOG = DAEMON / "space-cap5.jsonl"
GITHUB_MAIN = "refs/heads/main"


READ_TIMEOUT_S = 30
ELIGIBILITY_BUDGET_S = 240


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args],
                                   text=True, timeout=READ_TIMEOUT_S).strip()


def remote_main() -> str:
    rows = git("ls-remote", "--refs", "github", GITHUB_MAIN).splitlines()
    matches = [row.split()[0] for row in rows if row.split()[-1] == GITHUB_MAIN]
    if len(matches) != 1:
        raise RuntimeError("remote main is unreadable or ambiguous")
    return matches[0]


def runtime_gate() -> tuple[bool, str]:
    capacity = CACHE / "watchdog" / "primary-key-capacity"
    external = CACHE / "watchdog" / "primary-external-admission"
    if not capacity.exists() or capacity.read_text().strip() != "11":
        return False, "relay-3 capacity file is missing or not 11"
    if not external.exists() or external.read_text().strip() != "0":
        return False, "external admission gate is missing or not 0"
    return True, "relay-3 cap11/external0 verified"


def lock_quiet() -> tuple[bool, str]:
    for path in sorted((CACHE / "locks").glob("fix-*.lock")):
        with path.open("a+") as handle:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return False, f"active fix lock: {path.name}"
            finally:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
    return True, "no active fix locks"


class ReadTimeout(RuntimeError):
    pass


def _alarm(_signum: int, _frame: Any) -> None:
    raise ReadTimeout("GitHub eligibility read exceeded its bounded timeout")


def eligible_prs(remote: str) -> list[dict]:
    sys.path.insert(0, str(ROOT / "local" / "bin"))
    import gh_common
    import pr_merge

    now = datetime.now(timezone.utc)
    result = []
    for pr in gh_common.api("pulls?state=open&per_page=100") or []:
        if pr.get("draft") is not False:
            continue
        number = int(pr["number"])
        head = pr.get("head", {}).get("sha")
        if not head:
            continue
        statuses = gh_common.latest_statuses(head)
        try:
            with redirect_stdout(io.StringIO()):
                pr_merge.check_ci(statuses, head)
        except pr_merge.GateFailure:
            continue
        reviews = gh_common.pr_reviews(number)
        try:
            # Keep selection aligned with the newest exact-head canonical verdict.
            with redirect_stdout(io.StringIO()):
                pr_merge.check_review(ROOT, number, head, reviews, statuses,
                                      adjudicated=False)
        except pr_merge.GateFailure:
            continue
        if any(review.get("state") == "CHANGES_REQUESTED"
               and review.get("commit_id") == head for review in reviews):
            continue
        fresh = subprocess.run(
            ["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
             remote, head], timeout=READ_TIMEOUT_S).returncode == 0
        result.append(dict(number=number, head=head,
                           created=pr["created_at"],
                           pr_age_s=int((now - datetime.fromisoformat(
                               pr["created_at"].replace("Z", "+00:00"))).total_seconds()),
                           branch=pr["head"]["ref"], marker=True,
                           fresh_against_remote=fresh,
                           eligibility_age_s=None))
    return sorted(result, key=lambda row: row["created"])


def tick(merge: bool, interval: int = 300) -> dict:
    started = time.monotonic()
    local = remote = None
    clean = False
    reason = None
    eligibility_started = time.monotonic()
    eligibility_duration = None
    read_failure = None
    reasons: list[str] = []
    try:
        local = git("rev-parse", "main")
        clean = not bool(git("status", "--porcelain", "--untracked-files=all"))
        remote = remote_main()
        if not clean:
            reasons.append("primary worktree is dirty")
        if local != remote:
            reasons.append(f"local main {local[:12]} != remote {remote[:12]}")
        ok, reason = runtime_gate()
        if not ok:
            reasons.append(reason)
        locks_ok, lock_reason = lock_quiet()
        if not locks_ok:
            reasons.append(lock_reason)
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(ELIGIBILITY_BUDGET_S)
        candidate = eligible_prs(remote)
        signal.alarm(0)
        eligibility_duration = round(time.monotonic() - eligibility_started, 3)
    except Exception as exc:
        signal.alarm(0)
        candidate = []
        eligibility_duration = round(time.monotonic() - eligibility_started, 3)
        read_failure = f"{type(exc).__name__}: {exc}"
        reasons.append(f"read_failure: {read_failure}")
        clean = False
    fresh_candidates = [row for row in candidate if row.get("fresh_against_remote")]
    stale_candidates = [row for row in candidate if not row.get("fresh_against_remote")]
    oldest = fresh_candidates[0] if fresh_candidates else None
    if stale_candidates and not fresh_candidates:
        reasons.append("stale eligible PRs: " + ",".join(str(r["number"]) for r in stale_candidates))
    record = dict(ts=datetime.now(timezone.utc).isoformat(), local_main=local,
                  remote_main=remote, clean=clean, runtime=reason,
                  oldest_eligible=oldest, oldest_stale=stale_candidates,
                  oldest_fresh_against_remote=bool(oldest),
                  eligible_count=len(candidate), fresh_count=len(fresh_candidates),
                  eligible_age_s=None, eligibility_budget_s=ELIGIBILITY_BUDGET_S,
                  eligibility_duration_s=eligibility_duration, read_failure=read_failure,
                  external_admission=0, owner_total_limit=11,
                  native_descendant_limit=9, hold_reasons=reasons,
                  action="hold", duration_s=round(time.monotonic() - started, 3),
                  cadence_sleep_s=max(0, interval - round(time.monotonic() - started, 3)))
    if not reasons and oldest and merge:
        record["action"] = "delegate-pr_merge"
        record["merge_exit"] = subprocess.run(
            [sys.executable, str(ROOT / "local" / "bin" / "pr_merge.py"),
             str(oldest["number"])], timeout=3600).returncode
        if record["merge_exit"] == 0:
            try:
                record["post_merge_remote_main"] = remote_main()
                record["post_merge_remote_verified"] = True
            except Exception as exc:
                record["post_merge_remote_verified"] = False
                record["hold_reasons"].append(
                    f"post-merge remote reread failed: {type(exc).__name__}: {exc}")
    elif not oldest:
        record["hold_reasons"].append("no fresh exact-head CI/review-eligible PR")
    DAEMON.mkdir(parents=True, exist_ok=True)
    with LOG.open("a", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        handle.write(json.dumps(record, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    print(json.dumps(record, sort_keys=True))
    return record


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--merge", action="store_true",
                        help="delegate one eligible merge to pr_merge.py after checks")
    parser.add_argument("--once", action="store_true", help="run one tick")
    parser.add_argument("--interval", type=int, default=300)
    args = parser.parse_args()
    if args.interval < 5:
        parser.error("--interval must be at least 5 seconds")
    with LOCK.open("a+") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("merge service already owns its shared lock")
        try:
            while True:
                record = tick(args.merge, args.interval)
                if args.once:
                    return 0
                time.sleep(max(0, args.interval - float(record["duration_s"])))
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


if __name__ == "__main__":
    raise SystemExit(main())
