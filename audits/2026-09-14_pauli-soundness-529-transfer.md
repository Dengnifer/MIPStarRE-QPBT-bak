---
date: 2026-09-14
issue: 529
pr: 536
role: native-prover-continuation
base: b37ebc1faac601a5c2a8405fc4bdbb7f0f1359e7
started_at: 2026-09-14T19:51:07+09:00
elapsed_budget_seconds: 1500
status: supplied-extraction-transfer-proved
source_theorem_status: notready
supersedes_status:
  - audits/2026-09-12_pauli-soundness-529.md
  - audits/2026-09-12_pauli-soundness-529-attempt3.md
---

# Pauli soundness from supplied extraction data

## Summary

The concrete isometry transfer is proved for an actual supplied
`ExtractionWitness S w delta` in a projective setting. Adjoining each local
EPR state and applying the supplied swap unitary constructs a
`PauliSoundnessWitness P S.toStrategy`. Its squared state error is at most
`delta`, its unsquared state error is at most `sqrt delta`, and both Pauli
operator distances on the ideal state are at most `4 * delta`, for each
Pauli basis. A common bound is `max (sqrt delta) (4 * delta)`.

The source theorem `pauli_soundness` remains unchanged and not ready. This
report supersedes the earlier assertions that the supplied-data state and
operator transfer were outstanding. It preserves their provenance and cost
records; it does not retrospectively certify the unchecked draft.

## Source and scope

The paper was read before formalization:

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
  `thm:pauli`;
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`,
  the final local-EPR and swap construction;
- `docs/paper-gaps/qpbt_extraction-transfer.tex`, the missing range projection.

The assumptions are an admissible parameter tuple, a projective setting,
supplied global polynomial-pair data, and the actual extraction witness.
No operator-comparison, intertwining, or range-stability hypothesis was added.
The source-facing theorem acquires no new assumption. The two new blueprint
entries explicitly state the supplied-data and projective-setting scope.

## Mathematical construction

`StateTransfer.lean` constructs the local maps `phi = U J`, where `J` adjoins
the unit local EPR vector and `U` is the corresponding concrete swap map.
It proves the equality of the jointly prepared state with `psiHat`, the
equality of the joint isometry action with `applyBoth`, the ideal-state
reassociation, and equality of the squared state errors. The unit auxiliary
vector is the witness's actual `aux`, with its actual normalization field.

`OperatorTransfer.lean` constructs a complete POVM
`N_h = U (M_h tensor I tensor I) U.adjoint`. Positivity follows from positive
conjugation, and completeness uses `swap_right_unitary`. The preserved
ancilla theorem supplies `N_h phi = phi M_h` using `swap_left_unitary`.
Coordinate identities identify the original player placements, both
conjugated families, and both ideal Pauli readouts in the six-register and
soundness register orders. The one-point uniform average is exactly the
sum over all Pauli outcomes.

The jointly transformed actual state is fixed by
`conjIsometry phiA 1 tensor I` and `I tensor conjIsometry phiB 1`; this is
also exposed as `ExtractionWitness.transformed_state_in_ranges`.
The ideal comparison state is not assumed to lie in either range.
The saved local range-projection theorems give, separately for Alice and Bob,
`2 * delta + 2 * delta = 4 * delta`. The players' local spaces may differ.
There is no answer-count or dimension factor.

`pauli_soundness_ofExtractionWitness` packages all three bounds.
`pauli_soundness_deltaQld_ofExtractionWitness` composes them with
`deltaExtract_le_deltaQld`, `sqrt_deltaQld_le`, and `deltaQld_mono`.
For `C >= 1`, `a > 1`, `0 < b < 1`, and `0 <= epsilon <= 1`, it supplies
universal `a' >= 1`, `0 < b' < 1` bounding all three conclusions by
`deltaQld a' b' epsilon m d q`. The proof replaces the intermediate
coefficients `(A, B)` by `(4 * A, B / 2)`.

## Provenance

The sole writable worktree started clean at the base above. No merge was
needed. `Ancilla.lean`, `RangeProjection.lean`, and `ErrorBounds.lean` are
reused unchanged; their contents are not newly proved here.

The read-only worktree
`.worktrees/issue-529-independent-attempt3-20260912` supplied the uncommitted
`StateTransfer.lean` draft and its saved audit. Its last recorded check had
failed at `Matrix.submatrix_mulVec_equiv`; the subsequent `erw` edit was
unverified. This continuation recovered that mathematical content through
`apply_patch`, checked the `erw` proof successfully, exposed the ideal-state
identity, and updated obsolete documentation. The original draft and its
worktree were left untouched. The provenance audit's filename in the YAML
refers to that read-only worktree, not an added copy here.

The immutable PR #544 object
`6857f1c510f569b63b72ff022b2476d641f5ff5b` was read to confirm that its
`ExtractionWitness` header and fields agree with this base. The owner's
reported green conditional extraction result is separate evidence. Its
branch was not imported, and neither extraction existence theorem nor the
global-pair existence theorem is invoked in any new proof. In particular,
the old base's unfinished extraction constructor is not used as a proof.

## Statement integrity

- Paper assumptions: universal constants, admissible parameters, and a
  strategy succeeding with probability at least `1 - epsilon`.
- Public Lean assumptions: unchanged finite-dimensional carriers, the fixed
  field model, explicit nonnegative error, and the same success condition.
  Universal quantifier order and error expression are unchanged.
- Paper conclusion: local isometries, a unit auxiliary state, an unsquared
  state bound, and both complete Pauli-family comparisons on the ideal state.
- Public Lean conclusion: the same unchanged `PauliSoundnessWitness`, norm,
  and two finite sums of squared norms bounded by `deltaQld`.
- Verdict for `pauli_soundness`: unchanged faithful boundary encoding, with
  the inherited proof hole. Its declaration and docstring are unchanged;
  only the module imports and module description were updated.
- Verdict for the new theorems: proved conditional transfer from explicitly
  supplied extraction data in a projective setting. They are not advertised
  as the unrestricted source theorem and add no hypotheses to it.

## Validation

The pinned Lean toolchain is 4.32.0. Focused checks compiled
`StateTransfer.lean`, `OperatorTransfer.lean`, and their `Soundness.lean`
re-export, emitting only branch-private products. The new modules have no
warnings or forbidden proof-integrity tokens. The re-export reports only
the inherited `pauli_soundness` proof hole.

The full transitive axiom closure was checked for every new public
construction and theorem (13 declarations), including both player bounds,
the range identities, and both complete transfer theorems. Each closure is
exactly `[propext, Classical.choice, Quot.sound]`. In particular:

```text
pauli_soundness_ofExtractionWitness:
  [propext, Classical.choice, Quot.sound]
pauli_soundness_deltaQld_ofExtractionWitness:
  [propext, Classical.choice, Quot.sound]
```

These are complete closures, including private helpers, rather than a
textual scan of the new theorem bodies. The unchanged `pauli_soundness`
closure still contains `sorryAx`. The local reproducer is
`.lake/issue529-transfer-axioms.lean`.

`leanblueprint web` completed successfully. The first synchronization check
found 235 stale entries in the inherited, ignored `blueprint/lean_decls`;
regenerating that derived index with `blueprint_lean_sync.py
--update-lean-decls --ci` passed. It retains 14 existing warnings about
statement-only formalization marks elsewhere. The existing declaration
checker resolved all 1457 entries directly under `lake env`, avoiding a build
of its executable.
Whitespace checks and the installed-hook check passed. The initial normal
commit hook classified the two theorem environments as paper-facing and
rejected their conditional names. They were corrected to the existing
formalization-support `example` convention, as used by the adjacent
conditional extraction entry; their hypotheses and conclusions did not
change. Normal commit hooks are required; their terminal result accompanies
the final commit receipt.

No full `lake build`, CI, review session, descendant, publication, push, PR
mutation, or runtime/account change was performed. Issue #513 and frozen
PR #552 were not touched.

## Remaining obligations

No gap remains in this supplied-data transfer. Unrestricted soundness still
requires the genuine global-pair construction and its zero-error endpoint,
composition with the published conditional extraction theorem, transport
through projectivization back to an arbitrary original strategy, and the
documented source-domain and combined-lines error comparisons. The new
results do not discharge or conceal those obligations. The next owner gate
is integration with the published extraction result and the normal local
CI and independent review of PR #536.

## Cost and attribution

The preserved prerequisite records are:

| Session | Recorded wall seconds | Recorded status |
| --- | ---: | --- |
| Six prerequisite sessions in the 2026-09-12 audit | 6020 | Overlapping prerequisites |
| prover-529-20260912-01 | 1903 | Failed |
| prover-529-20260912-02 | 48 | Failed |
| prover-529-20260912-03 | 5722 | Done |
| prover-529-20260912-04 | 2295 | Done; preserved an unchecked draft |

Session 529-04 overlaps 529-03 in wall time. These spans are not summed or
presented as unique active time. The original prerequisite token subtotal
was 16,501,860 input, 15,693,824 cached input, and 110,688 output tokens.
The independent audit reports a later known lower bound of 24,170,157 input,
23,185,152 cached input, and 132,178 output tokens. These historical
subtotals are preserved, not added to each other. Usage for 529-01 and
529-02 remains unknown, as does the missing duration/usage attribution for
`prover-121-native-20260907`; unknown values are not zero.

The current native continuation has no independently measured per-session
token count in this worktree. Native token snapshots are cumulative and
nonadditive. MAIN records its terminal native receipt, including elapsed
time; this audit neither resets prior costs nor changes the primary registry.
