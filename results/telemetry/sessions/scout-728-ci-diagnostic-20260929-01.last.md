**Diagnosis**

- Sole unresolved handle: `item_148`
  ```text
  python3 -m unittest discover -s scripts/tests
  ```
  CWD is the issue-728 worktree. The other 123 command handles completed.
- The capture continued updating through `2026-09-29 05:21:22 +0900`, while `item_148` remained in progress. This is not a quiet or stopped author session.
- PID `1580756` cannot be verified from this scout sandbox: `/proc` is PID-namespace-local. The author’s own `ps` probes likewise saw only their probe sandbox, not the sibling test sandbox. Therefore that PID is not safe evidence for signaling.
- No machine-wide full-build lock was present at the final observation. Earlier contention cannot be excluded.
- The late suite includes three real-Lake fixtures sharing the build lock, with a 300-second lock wait and 360-second train timeout: [test_pr_train.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-728-ldt-linear-error-bounds/scripts/tests/test_pr_train.py:549). This provides a bounded explanation for substantial latency.
- The Git metadata restriction is not a convincing cause: these tests create writable temporary repositories.
- Provider/key-looking output is fixture data. For example, `"Bad credentials"` is a mocked response in [test_blueprint_lean_sync.py](/home/drx/MIPStarRE-qpbt/.worktrees/issue-728-ldt-linear-error-bounds/scripts/tests/test_blueprint_lean_sync.py:1189), and dispatch tests use fake `codex` executables. No credential failure is evidenced.
- The reported `E` marker may indicate a real unittest error, but no final traceback has reached the capture, so the failing test remains unknown.

**Safe Action**

Do not signal PID `1580756` or the author. Continue waiting for `item_148`’s bounded fixtures and final unittest report. If interruption becomes necessary, first obtain the actual host PID/start identity from the owning dispatcher; this scout cannot safely name one. No files or processes were changed.