# Palomar pilot CI and compact-interface work — 2026-10-02

Authoritative instructions remain owner briefing sections 8–9 and its section 6
stopping rule. B12:A is recorded as resolved on #500. MAIN decides internal
changes and records their costs; no submission, external contact, account or
host change is authorized by this checkpoint.

## Exact work and gates

- Pilot #744 / PR #758: head c0d8b6d1365179abbc7b8bf9db414a34c6effa7d.
  Full library build passed in 865 seconds; canonical CI remains active.
  Other checks and independent Sol review must pass before normal merge.
  Log: /tmp/qpbt-palomar-pattern-ci.log (exec handle 22590).
- Line representative #757 / PR #759: head
  f89fb0e5f3a742779147d6532962a7cf9c78e3af. Exact least-coordinate formula,
  including zero direction, proved with unchanged existing declarations.
  Canonical CI owns the full-build lock after the pilot build.
  Log: /tmp/qpbt-palomar-line-ci.log (exec handle 73532).
- Review routing #745 / PR #755: first exact-head CI green, review 5383425988
  requested changes. Sol repair orc-745-20261002-02 is live (handle 79395;
  /tmp/qpbt-palomar-review-route-fix.log), bounded to 1800 seconds with prior
  1618 author seconds retained. Fixes bind the check to the official Actions
  run/current-attempt job and pinned launcher bytes, and run the reviewer from
  primary trusted instructions. New CI plus second independent review required;
  no gate override and no third full tooling review.
- Metadata #754: local companion commit
  644578f3d1873bc0336e9bb3509ca0072d9988d7, branch
  issue-754-palomar-metadata, in .worktrees/qpbt-comparator-palomar. Schema and
  seven fixtures pass, report regeneration is identical. The report is
  intentionally red for old toolchain, missing modules, split Challenge imports
  and old library URL. No PR or publication by this worker.
- New proof packet #760: prover-760-20261002-01, Sol/Ultra, primary space-3,
  first attempt at most 3600 seconds; thread 01a0f8b9-8784-7ba1-b67b-af4117ca437c.
  Worktree .worktrees/issue-760-palomar-strategy-equivalences from f3f57e5d;
  primary setup/hook check passed. Implements additive Mathlib-only generic
  games/POVMs/unit pure strategies with exact value and projectivity/SPCC
  bridges. Full carriers, swap invariance, positive-support commutation and
  numerical bounds stay unchanged. No changes to existing conversion files.
  Contract /tmp/palomar-compact-foundation-issue.md; handle 66993;
  /tmp/qpbt-palomar-strategy-worker.log.

## Decisions and costs

The two Astra route reports consumed 620 + 521 = 1141 seconds of the original
1800-second budget. Register exactly fixedFieldModel as a named definition;
retain its full intrinsic field, cardinality, encoding, self-dual normal-basis
contract in Challenge and the existing proved selector in Solution. No other
helper holes are authorized. Textual saving: 375 lines / 16672 bytes. This is a
route decision, not final certification. Compact game/error definitions and
exact bridges, final single-file measurement and independent Astra review remain.

Live Palomar's minimum requires Lean v4.35.0-rc2, with matching Mathlib tag.
MAIN decision #756 supersedes the earlier retain-v4.32 choice: upgrade after the
pilot and before #746. Costs include dependency pins, necessary proof/API ports,
full build/axiom audits and review. No statements or bounds may change.

Conversion packet ownership/dependencies remain in the committed
palomar-module-packets-20261002.md and #743 children #744/#746–#753. Packet #746
now also depends on #756. P3 and P4 can proceed concurrently after P2.

Two model workers are active; the third slot is available for the next green
PR's independent review. No native agent, merge daemon or outside repository is
used. Real-build fixtures in the pilot CI compete with #759 for the shared
build lock; fixed timeout failures require an uncontended rerun, not a lock or
check bypass. No project completion or Palomar readiness is claimed.
