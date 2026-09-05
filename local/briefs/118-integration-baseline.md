# Issue 118 integration baseline

Session `orc-118-20260906-02`, September 6, 2026 (local date).

## Pinned prerequisites before integration

The GitHub API, accessed through `local/bin/gh_common.py`, reports:

- Issue 201: `7d0af711c5c6769151e41cf091288855fdb409b0`.
- Issue 117: `6b4b75d408be5399a1867166bffcc3aa56de6e4b`.
- Initial issue 118 head: `691b67159f9ead45b9de144df3bd46e015430e70`.

Both prerequisite objects are already present locally. PR 205 remains open
at the issue 201 SHA; its ongoing corrections are not part of this session.
The inherited audit, obstruction brief, and dirty telemetry are preserved in
the diagnostic commit before any merge. The mathematical handoff remains
`audits/2026-09-06-issue118-point-error-dependency.md`; this integration does
not repeat or supersede that audit.

The existing hook configuration points to the primary checkout's guarded
hooks. Branch-local hook restoration must retain the incoming merge-loss
guard, not downgrade to the old two-hook layout. No hook bypass, full build,
push, PR merge, or independent review is authorized by this integration.
