## What changed

Added [Consistency.lean](/tmp/mipstarre-19-consistency/MIPStarRE/QPBT/Extraction/Consistency.lean) with five source-faithful obligations:

- Both marginal/point helper estimates with explicit `AA'`/`BA''` and `BB'`/`AB''` placements.
- Both directional point-measurement consistency declarations.
- Pulled-apart observable self-consistency.

Commit: `aada8d2da027a4c1438a67714e8628dab1a6dcfc`

## Evidence

- Focused Lean check passed in a temporary composite checkout containing issue-18 witnesses and the sibling observables interface.
- `rg -n "sorry|axiom"`: five expected `sorry`s at lines 59, 87, 108, 126, and 143; no axioms.
- Forbidden-token scan: clean.
- `git diff HEAD^ HEAD --check`: passed.
- Pre-commit hooks: passed.
- Worktree: clean.
- Full build skipped because this branch does not yet contain its parallel-wave imports.

## Statement integrity

Paper assumptions: admissible parameters, projective setting, and the global polynomial-pair measurement from `lem:qld-4-7`.

Lean assumptions: exactly `AdmissibleParams`, `ProjectiveSetting`, and `GlobalPairWitness`; no residual or package assumptions.

Paper conclusion: the two marginal absorption estimates, both point-consistency directions, and observable self-consistency with the stated uniform averages.

Lean conclusion: the same estimates, with symmetric placements represented explicitly.

Verdict: exact.

## Open obligations

- `sum_marginalPoly_pointMeas_approx_id`: agreement calculation from the two Chapter 15 point-consistency fields.
- `marginalPoly_sub_pointMeas_approx_zero`: projection contraction and expanded-point self-consistency.
- `tildeM_consistent_pointMeas`: non-encoding mass argument, tracked in `docs/paper-gaps/qpbt_decoding-identity.tex`.
- `tildeM_consistent_pointMeas'`: player-interchanged non-encoding mass argument.
- `tildeObs_selfConsistent`: pulling-consistency calculation and trace postprocessing.

## Handoff

The sibling `Observables.lean` draft currently duplicates the three consistency declarations. Remove that duplicated section when integrating this commit, then re-run the focused check and full build.