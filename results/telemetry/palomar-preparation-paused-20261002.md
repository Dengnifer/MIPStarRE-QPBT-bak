# Palomar preparation: owner decision B12

The owner briefing `briefing-palomar-20261001.md` is the active assignment.
Its section 5.4 explicitly requires an owner decision and goal pause if the
Solution-only library must be converted to Lean's module system.

The [Palomar source requirements at policy commit 96b034cc](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md#lean-source-requirements)
expressly extend module-header and file-length checks to separately declared
substantive repositories for thin wrappers. QPBT-comparator must identify
MIPStarRE-QPBT as that substantive repository; the external-dependency exception
therefore does not exempt the library from these checks.

Main and the independent Sol scout agree on the immutable library snapshot
`14c43b47f4eb2bb005666c000f5880b60b400c8a`: 742 tracked regular Lean files,
251,114 physical lines, all 742 missing a module header, no Lean symlinks,
and no file longer than 10,000 lines. The largest file has 1,000 lines.
The scout additionally counted 1,942 existing import commands, none public.
Migration must preserve declaration visibility, exposed definition bodies,
re-export interfaces, generated comparator fragments, and all four theorem
statements. No timing estimate was inferred from file counts.

- [Owner decision B12](https://github.com/Dengnifer/MIPStarRE-QPBT/issues/500#issuecomment-5935162515)
  asks for a separately scoped module conversion or deferral of Palomar work.
- [Progress notice](https://github.com/Dengnifer/MIPStarRE-QPBT/issues/27#issuecomment-5935189906)
  records the pause and absence of a submission-ready SHA.
- [Static inventory](palomar-source-inventory-20261002.json) records the measured scope.
- Independent session: `scout-palomar-module-scope-20261002-01`, Sol/Ultra,
  thread `01a0f828-308a-75d0-b368-88ecea56dd2d`, 481 seconds, exit 0.
  Its capture and final report are retained in `results/telemetry/sessions/`.
- `docs/palomar-submission.md` is an uncommitted local draft containing the
  scope, cost, decision link and intended owner submission fields. It has not
  been presented as a final submission note or published without a PR gate.

The observed comparator main is
`360402fdf4a39399f94331452d6e5d0a35c144be`; this is a starting snapshot,
not a recommended submission SHA. No library Lean source, toolchain, comparator
checkout, external project, credential or runtime allocation was changed.
No submission or outside contact was made. The space-3 worker succeeded.

The keeper stop flag is set. There are no remaining workers; no successor is
admitted because the explicit owner-only stopping condition applies. Challenge
condensation, metadata/schema checks, final comparator CI and the complete
mechanical acceptance record remain outstanding pending the owner's decision.
