# Palomar packets and source-interface frontier

Owner briefing section 9 is active. Rule 5.4 is withdrawn entirely; MAIN may
decide internal scope, restructuring, routes and version changes, recording
reason and cost on #27. Beyond-project risks remain owner decisions, and no
submission or outside contact is authorized. The current engineering choice
keeps Lean/Mathlib v4.32.0 because no need to upgrade has been found.

The immutable 742-path ownership map is published at commit
`05749bb47fb392cd1967f841e0677cb6d674acc7` in
`results/telemetry/palomar-module-packets-20261002.md`. GitHub #743 is the
parent tracker. The following are GitHub issues with recorded dependency edges:

| Packet | Issue | Files | Direct prerequisites |
|---|---|---:|---|
| P0 pilot | #744 | 7 | none |
| P1 foundation/LDT-1 | #746 | 142 | #744 |
| P2 LDT-2 | #747 | 109 | #744, #746 |
| P3 LDT-3 | #748 | 85 | #746, #747 |
| P4 QPBT-1 | #749 | 110 | #744, #746, #747 |
| P5 QPBT-2 | #750 | 110 | #746, #747, #748, #749 |
| P6 QPBT-3 | #751 | 104 | #746, #748, #749, #750 |
| P7 QPBT-4 | #752 | 38 | #746, #748, #749, #750, #751 |
| P8 generated/tools | #753 | 37 | #748, #751, #752 |

P3 and P4 can run concurrently after P2. P8 preserves historical harness bytes
as archival text and consistently renames nonstandalone header/footer templates;
retained real Lean sources use modules. The plan and cost are on #27 comment
5936559860. Issue status must be re-read from GitHub before admission.

Three writing assignments are presently active:

- #744, `simplifier-744-20261002-01`, worktree
  `.worktrees/issue-744-palomar-module-pattern`, 3600-second assignment.
  All converted leaves and the executable path pass focused checks; Checkdecls
  resolves 2198 declarations. The normalized mathematical source is unchanged.
  Comparator expectations change only provenance lines; the assembler and
  narrow tests were updated. The worker cannot write the linked Git index from
  its workspace sandbox and is finishing a temporary-index hook run. Do not
  race that live writer. When it returns, use existing full-access authority
  for normal commit/PR/CI, or resume with the remaining budget and explicit
  `--sandbox danger-full-access`; then dispatch independent Sol review.
  Process handle 85302; log `/tmp/qpbt-palomar-pattern-worker.log`.
- #745, `orc-745-20261002-01`, worktree
  `.worktrees/issue-745-companion-review`, 5400-second assignment within a
  two-hour tooling episode. Adds the bounded companion review route; focused
  tests pass, and normal commit/publication/CI are pending. It may encounter
  the same default-workspace Git administration restriction; retain its diff
  and use the standing authorization, never request a new owner decision for
  that already-authorized operation. Do not use the new route before its own
  canonical CI and independent review/merge.
  Process handle 39027; log `/tmp/qpbt-palomar-review-route-worker.log`.
- #754, `orc-754-20261002-01`, fresh comparator clone
  `.worktrees/qpbt-comparator-palomar`, branch `issue-754-palomar-metadata`,
  base `360402fdf4a39399f94331452d6e5d0a35c144be`, 3600-second assignment.
  Metadata/checker preparation only; no Challenge, Solution, pin or CI edits,
  no Lean builds and no publication. Explicit full-access dispatch applies the
  existing owner grant. This independent repository has no library hooks;
  only the inapplicable library hook-installation check was skipped. Final
  official comparator CI and independent exact-head approval remain mandatory.
  Process handle 2355; log `/tmp/qpbt-palomar-metadata-worker.log`.

The completed Astra route scout is
`scout-palomar-faithfulness-route-20261002-01`, thread
`01a0f871-4448-7710-8930-ae1a20e1b296`, 620 seconds, exit 0. It recommends
retaining the current fixed field/basis construction and using exact bridges
for compact games/measurements, with an estimated 965-line budget. This is not
an implemented artifact or final approval. Preserve all outcome constructors,
86 ordered Pauli edges, unsquared state error, squared operator errors, and the
different malformed-answer conventions for LD and Pauli.

Before commissioning those substantial bridges, MAIN prepared one specific
follow-up: inspect the official comparator's supported `definition_names`
mechanism and Palomar policy to determine whether the existing fully specified
`fixedFieldModel` type can be a named definition supplied by the Solution,
without a new theorem assumption or changed choice. This might remove the
407-line construction from the Challenge while preserving its full mathematical
contract; it has NOT been judged valid yet. Also verify what the comparator
requires of proof-only helper bodies. Do not assume the optimization is sound.
The complete read-only task is preserved at
`~/.cache/mipstarre-dev/palomar/field-frontier-followup.md`.
The first segment used 620 of its original 1800 seconds; a continuation of at
most 900 seconds would keep the total within that budget. Admit only after
rechecking the three-slot cap; an independent final Astra reviewer remains
required after actual implementation.

All three slots are occupied at this checkpoint. The immediate source frontier
is #744's real commit, canonical CI and independent review; the next bulk
packet is #746 after the pilot gate. The goal remains active, the keeper stop
flag remains absent, and no completion or submission-ready SHA is claimed.
