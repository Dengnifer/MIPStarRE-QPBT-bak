## What changed

Committed `d8f654606b6669d487a9c49ac73d3f6461cb67b2` (`feat(QPBT/Extraction): add observable extraction obligations`, body `Addresses #19`).

[Observables.lean](/tmp/mipstarre-19-observables/MIPStarRE/QPBT/Extraction/Observables.lean:1) now defines `selectPoly`, `decodeFq`, polynomial marginals, `tildeM`, `tildeObs`, and `swapUnitary`. It states the requested product-form, Hermitian/involution, corrected commutation, consistency, unitarity, and conjugation obligations.

## Evidence

- Focused Lean check passed against the parallel Chapter 15 foundation commit `1340f3b78b4fd2ba1e77da7da1dea3956276087a`.
- `rg -n "sorry|axiom"` reports 11 documented `sorry`s at lines 113, 127, 141, 160, 184, 205, 223, 251, 265, 282, and 300; no axioms.
- Hook installation check and pre-commit passed.
- Staged/final diff checks passed; only `Observables.lean` changed.
- Worktree is clean.
- Full `lake build` was skipped because this branch does not yet contain the parallel Chapter 15 `Combining.Witnesses` dependency.

## Statement integrity

Paper assumptions: the canonical field basis, projective global polynomial-pair measurements, the expanded strategy state, and the paper’s error parameter.

Lean assumptions: `AdmissibleParams`, `ProjectiveSetting`, and the Chapter 15 `GlobalPairWitness`; player/register arguments are explicit. No bridge, pointwise bound, or unrestricted decoding hypothesis was added.

Paper and Lean conclusions agree for product form, self properties, consistency, and swap conjugation. The commutation statement includes the documented uniform phase correction from `qpbt_cross-basis-phase.tex`.

Verdict: **faithful boundary hypotheses**, with one documented local correction.

## Open obligations

- `tildeObs_eq_heteroKron`: finite Fourier regrouping.
- `tildeObs_isHermitian`: product form plus measurement/Pauli Hermiticity.
- `tildeObs_mul_self`: projector orthogonality plus Pauli involution.
- `tildeObs_twisted_commutation`: product form and corrected Pauli phase; tracked by `qpbt_cross-basis-phase.tex`.
- `tildeM_consistent_pointMeas`: encoding/non-encoding mass split; tracked by `qpbt_decoding-identity.tex`.
- `tildeM_consistent_pointMeas'`: player-swapped version of the same argument.
- `tildeObs_selfConsistent`: measurement consistency transferred through trace postprocessing.
- `swapUnitary_mul_conjTranspose`: projector completeness and Pauli involution.
- `conjTranspose_mul_swapUnitary`: reverse unitarity calculation.
- `swapUnitary_conj_tildeObs`: diagonal projector reduction and phase cancellation.
- `swapUnitary_conj_tildeM`: exact relabeling using `lowDegreeEnc_eq_dotProduct`.

All direct proof debt is documented and tracked by issue #19.

## Handoff

Review the heterogeneous player-space placements and the corrected cross-basis phase first. Integration must include Chapter 15 commit `1340f3b78b4fd2ba1e77da7da1dea3956276087a` before running the direct branch-wide build.