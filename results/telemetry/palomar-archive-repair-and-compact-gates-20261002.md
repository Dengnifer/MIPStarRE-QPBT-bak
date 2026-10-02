# Archive recovery and compact gate coverage — 2026-10-02

The goal remains active. The library compiler port, module integration and final
companion verification have not passed their final gates.

## Archive recovery

Issue #777 now has clean local commit
779146a14959e860014467b1febaea9bcc3c40e2. Its multi-batch verifier checks each
complete immutable preimage, exact raw recovery, deterministic gzip and the
union of all archive paths; omissions, collisions and orphans fail closed.
Two batches contain 2111 captures, 2,039,985,049 original bytes and462,071,333
compressed bytes. The complete committed source is517,947,774bytes, leaving
6,340,226bytes below the524,288,000byte limit. New captures must be measured and,
if needed, archived in another separately attributed batch before the final pin.

The first manifest is unchanged:
84b34ebfa108e2c3325916447dff23c512e115d598c6a7e897da2cc931a56037.
The second manifest hash is
d02461dfd48a7d1fa180808ed2b4795a7fcf49cb309fc99aca0014df42a5c207.
The earlier single-manifest failure and MAIN's incorrect coexistence inference
remain in the preceding checkpoint. No raw immutable Git data was lost.

Worker orc-777-20261002-04,thread01a0fa97-fa50-7852-8903-12036b8a1b9b,
completed in1086seconds; cumulative author cost2866seconds. Nine focused tests
passed. Normal hook accounting is906total,9skipped,897executed, correcting the
worker's shorthand906passed. New-version refresh, normal CI and independent
review are still required; no publication or approval is claimed.

## Compact gate omissions and assigned repair

The600second scout-776-20261002-01/thread01a0fa9f-8739-7b90-874a-3946dd380801
timed out without a final report or token accounting. Raw capture is retained.
MAIN independently verified the concrete omissions: default Lake roots do not
include the new compact modules; existing audits omit the four compact aliases
and fixedFieldModel value; drift compares bytes without compiling the standalone
Challenge; the GitHub library CI mirror enumerates only the two old challenges.

The1200second #774 preparation assignment starts at publishedb01bcd29 and keeps
the audited Challenge SHA256 unchanged:
4600b1c3e2409edf2a68df53a2055516c99646e42750f966cf02e60437700de3.
The existing QPBT audit will build the compact dependency graph and check the
four aliases plus selector value; normal CI will compile the regenerated
standalone Challenge and preserve all existing checks. Focused regressions and
normal hooks are required. No full old-version build or publication is requested.
Author orc-774-20261002-02/thread01a0faad-c726-78b3-850e-6ffd9a9bb8ec;
prior2931seconds, phase ceiling4131seconds. Final rc2 integration remains due.
Admission record: #27comment5945129595.

## Compiler port continuation

The preceding1800second author tranche ended at its limit, exit124, with84files
modified and no commit. Total author cost15300seconds plus532seconds of separate
scouting. The latest full build log is
worktree-build-20261002T031758Z-2442562.log. Five new roots were exposed; four
received focused fixes, while ConditionalCollision still has a noncompiling
sum/filter normalization diagnostic. No full build success is claimed.

MAIN admits2700seconds of linked continuation, cumulative author ceiling18000,
under owner section9. Brief:/tmp/palomar-756-sixth-tranche.md. It preserves the
entire patch, statements, bounds and toolchain pins, and must finish actual
compatibility validation before publication. No automatic further extension or
gate waiver. The active #774writer uses a different worktree. A third slot is
available, but remaining final integration depends on these two inputs; no filler
assignment is admitted. Main remains the operator and no outside action is made.


## Wrapper draft and independent publication preparation

The third slot was subsequently used for concrete wrapper preparation rather
than left idle (#27comment5945229427). Authororc-776-20261002-02,thread
01a0fab8-79db-75c0-9e56-d579b53bcfb3, completed in488seconds with clean local
companion800af3b2989f96d1196e7ff6342469172b12dfbc. Cumulative776author1249seconds;
the earlier600second coverage scout remains separately charged.

The wrapper has the exact audited Challenge and immutable native caller fixture,
three compact Solution imports, the six-field configuration, consistent metadata,
and module headers in allthree actual Lean files. Only the obsolete split
Challenge mirror and unused legacyverify.sh were removed. Seventeen checker tests
passed. Its preparation report is deliberately21pass,4fail,4unknown: the retained
old toolchain/source pin and absent runtime evidence are not final verification.
No branch publication, CI trigger or submission occurred.

The #7741200second gate phase ended at its cap, exit124, during a second normal
commit hook. Total774author4131seconds. The first hook had found two integration-
train fixture assumptions (missing materialized --write output and an old Lake-
call count); both were repaired. Two focused train tests and17focused gate tests
pass. Allfive roots pass the exactthree-axiom check, and regenerated standalone
Challenge compiles at992lines52483bytes with its unchanged hash. The full hook
and local commit were still unfinished at the deadline. MAIN found no remaining
commit process or index lock and is running the unchanged staged patch through a
normal operator commit (handle63560, /tmp/palomar-774-main-commit.log), without
bypass. No rc2 or canonical approval is implied.

Source-independent #745 review tooling is now scheduled before756completion,
using the remaining776seconds of its earlier5698second author ceiling,4922spent.
Authororc-745-20261002-04/thread01a0fac1-3882-7d13-b4cf-c4922f500c9c owns its
existing worktree and refreshes/publishes the preparedacc repair against
publisheda2d98834. It retains the two adverse reviews/findings. Normal exact-head
CI and the already authorized additional1800second independent review still
follow publication. This scheduling choice changes no verification gate.

Current bounded compiler continuation: orc-756-20261002-07/thread
01a0fab4-96b0-7ac3-94b3-c63d69d11b56,2700seconds,authorceiling18000.
It repaired ConditionalCollision and passed a targeted build; the next fullbuild
exposed further downstream roots and is not yet green. Its log is
/tmp/qpbt-palomar-756-sixth-tranche.log. No new budget is silently allocated.

Prepared, not admitted, successor briefs:
/tmp/palomar-753-final-module-integration.md (must bind normally merged756/774,
actual worktree and budget before use), and
/tmp/palomar-final-companion-publication-plan.md (preserve exact verifiedH when
fast-forwarding owncompanionmain; store final local runtime evidence inPRIMARY).
The finalkeeper stopping rule has not been reached; goal remains active.
