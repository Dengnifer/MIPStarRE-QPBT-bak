# First successful supported-version library build — 2026-10-02

The #756 compatibility work reached its first complete library build on the
chosen exact Lean/Mathlib v4.35.0-rc2 pin. The serialized helper's log is
`~/.cache/mipstarre-dev/logs/worktree-build-20261002T043941Z-2817385.log`.
It ends with `Build completed successfully (9633 jobs).` This is the complete
MIPStarRE root, including both inherited LDT and active QPBT mathematics.

The patch is still in its author worktree on the original pilot base; it is not
published or merged. Both axiom audits, original LDT/QPBT comparator regeneration
and drift, normal hooks/publication, canonical exact-head CI and independent
review remain required. The compact Palomar stack and full module packets are
separate prepared work and are not included in this build. No final submission
readiness or official comparator success is claimed.

The latest fixes removed the regression from globally unfolding the constructed
strategy, aligned the Naimark witness locally, updated a removed polynomial API,
and adjusted raw-operator branch proofs for the new simplifier. Public statements
and bounds are to remain unchanged and must be checked by the normal review.
The author is still within its current 1800-second tranche, cumulative author
ceiling19,800 seconds plus532 seconds of separate scouting.

In parallel, #745's routing repair has passed 14 focused cases and is running
normal commit hooks. #753's auxiliary preparation is also in a normal operator
commit hook after compiling all31 generated QPBT modules and proving normalized
byte equality. Both remain unmerged, with final gates still pending.
