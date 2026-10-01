# Native preflight and bounded checker repair — 2026-10-02

Scout754 finished in876seconds, exit0, thread
01a0f964-4034-7ce1-86a8-7972ee2a5cc1. Its source-context limitation was a read-only
shell network restriction, not a model-key failure. It used public web sources
and local archives. Its raw receipt is preserved; this audit is not PR approval.

MAIN independently queried PalomarRegistry/PalomarSubmission main through the
primary gh_common layer: it remains65f0154ed776cd26c224254aa57b379137f28b0d, the
same policy revision already pinned in the draft. The authenticated tree/blobs
were saved only under the task runtime directory
~/.cache/mipstarre-dev/palomar/official-report-source-20261002. The verifier's
Git blob hash was independently checked as
a97bb1463dd756019b1e6be32cdc1733b5dd22fe
SHA256: 1c1b4b7c8319bd31960d4484e747d23eb6664d6bf7e4e901bc724aacf34f282d

Verified source facts and scout adjudication:
- scripts/verify_submission.py5657 sets phase=verification;6248–6252 sets
  status=pass and stage=complete. The scout's earlier provisional claim that
  complete was invented is rejected; its final phase/stage description is valid.
- The actual report's kernel records are top-level kernels (5757), a list of
  name/argv objects. external_kernels is inside the protected_config JSON string
  (1198,5822–5823), not report.comparator. Scout final item3's location is wrong.
  The frozen checker therefore cannot correctly consume the current real report.
- .github/workflows/submission.yml11–18 explicitly provides workflow_call for
  own-repository predictive preflight with no Palomar state/credentials. README
  37–48 confirms it is not registry submission and does not perform editorial
  review or registration. MAIN adopts this pinned full workflow for final
  companion CI, not the registry dispatch or agent protocol. Nothing was run.
- The audit's exact definition/alias profile, real artifact-origin distinction,
  main-pin ancestry and actual import-origin gaps remain useful concrete findings.
  Precise static LFS/config limits must follow source, not inferred extra rules.

MAIN admits one1800s Sol Ultra/general checker repair in the same authorized
companion clone at644578f3d1873bc0336e9bb3509ca0072d9988d7. Existing author1547s
and scout876s remain counted; total authorized episode ceiling4223s. The repair
changes only checker/profile/metadata references/tests/docs and the honest red
report. It cannot change Lean artifacts, pins, workflows or755, push, run CI,
submit or publish. It must distinguish supplied report contents from independently
bound execution; the existing companion lane owns real run/job/artifact origin.
The final runtime local-check output will be saved in the primary library repo
after wrapper H is fixed and checked, avoiding any self-referential wrapper commit.

The first launcher preflight failed before model activation because this
standalone companion has no library .githooks. MAIN reused the identical recorded
754 metadata dispatch setup from events.md10116 at8a96787c: skip only that
inapplicable installation probe, preserve all companion CI/review/publication
gates. The incident is appended to events.md; no model budget was consumed by
that failed preflight. No new authorization or source-gate exception was needed.

Repair thread: 01a0f97b-04a4-7263-837e-4cdb2d888e59
Runtime log: /tmp/qpbt-palomar-checker-repair-worker.log
Progress Log27 comment: 5941543317

Other live workers:756 necessary toolchain port and770 compact headline aliases.
Upgrade/source gates, library-wide conversion, final Challenge/native CI and the
owner note remain incomplete. Goal stays active.
