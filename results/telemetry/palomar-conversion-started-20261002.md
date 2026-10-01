# Palomar module conversion started after B12:A

Owner briefing section 8 authorizes all 742 tracked Lean sources to adopt the
module system, preserving Lean/Mathlib v4.32.0, every theorem statement and the
ordinary proof-integrity, full-CI, axiom-audit and independent-review gates.
The previous blocking instruction in section 5.4 is superseded for conversion
only. The existing B12 comment on #500 is resolved in place; #27 comment
5936240078 reports resumption. Goal status is active and the keeper stop flag
has been removed.

The parent issue is #743. The first implementation packet is #744, with branch
and worktree `issue-744-palomar-module-pattern`, based on published main
`97dc6e049b0ce966be18bf8801e14b30c0081919`. Hot-cache worktree setup and hooks
passed. It owns the five `Quantum/FiniteMatrix/` leaves, the aggregate module,
`scripts/Checkdecls.lean`, and `docs/module-conversion.md`; only necessary exact
comparator drift synchronization may extend that scope. Its seven baseline
Lean checks passed; the conversion and CI are still in progress.

Three independent Sol/Ultra external sessions use the three space-3 slots:

- `simplifier-744-20261002-01`: the pattern packet, at most 3,600 seconds;
  log `/tmp/qpbt-palomar-pattern-worker.log`. It opens the PR and runs canonical
  CI; MAIN dispatches independent review through `local/bin/review.sh` afterward.
- `scout-palomar-packet-map-20261002-01`: read-only import graph and packet
  boundaries, at most 900 seconds; log `/tmp/qpbt-palomar-packet-scout.log`.
  Preliminary evidence finds 742 singleton file SCCs and 1,849 resolved local
  import edges. `Quantum/ControlledUnitary` depends on QPBT games, so packets
  must split major directories by import layer. Await its final exact plan.
- `scout-743-20261002-01`: read-only engineering assessment of single-file
  Challenge size and closure, at most 900 seconds;
  log `/tmp/qpbt-palomar-challenge-scout.log`. No statement-equivalence decision
  or final faithfulness approval is delegated to this scout.

No bulk conversion starts before the pattern is settled and documented. The
next eligible worker is the independent Sol review of #744's exact CI-green
head; the remaining directory packets depend on the approved pattern and the
scout's import-order map. Final Challenge faithfulness review uses Astra under
the owner's hard-job authorization.

A fresh comparator clone is prepared at
`.worktrees/qpbt-comparator-palomar`, on remote main
`360402fdf4a39399f94331452d6e5d0a35c144be`. It is unchanged. The owner's existing
`~/QPBT-comparator` checkout was not accessed. The blocking-era submission note
is preserved at
`~/.cache/mipstarre-dev/palomar/palomar-submission-blocked-draft-20261002.md`;
the final note will return to `docs/palomar-submission.md` in a reviewed packet.

The comparator uses an independent repository and official Actions CI. Before
its publication, settle how the primary `review.sh` can review its exact head:
the current script resolves local branch/base objects only in the primary
library repository, despite accepting a GitHub repository override. Do not
invent approval or bypass CI to accommodate this. Library packets already have
the normal supported review path. No merge daemon is used; MAIN may call
`pr_merge.py` only after its ordinary gate passes.
