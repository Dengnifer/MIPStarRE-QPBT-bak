# Issue 520: finite-character conversion checkpoint

Base: `fd83ecda4ec0bf8397687eff9ebcc034525d0dd6`.
Session: `prover-520-20260912-03`. The active work began at approximately
07:39:42Z after dispatch at 07:32:26Z. This is the third attempt, subject to
the 25 active minute limit; no new mathematical scope begins after 08:00Z.

## Prior evidence and cumulative cost

The immutable captures in `~/.cache/mipstarre-dev/sessions/` record failed
sessions `prover-520-20260912-01` and `prover-520-20260912-02`. The primary
telemetry register records 2679 and 43 wall seconds respectively, totaling
2722 seconds before this attempt. Both token totals are unknown, not zero.
The first capture ends with an account concurrency failure; the second ends
with HTTP 503. Neither has a successful final proof receipt. The first
worktree retains uncommitted difference-polynomial and placement arguments;
these were read without modification. Its placement comparison supplied a
reference for the elementary reindexing calculation here. None of its
unverified polynomial consistency results is imported or claimed as proved.
The saved branch commits `ae124f8f` and `230e7fdd` and current main retain the
target obligation. No saved open PR located in the snapshot supplies its proof.

## Mathematical result

Write chi(r a) for the sign of the fixed binary trace. For vectors v(a) in a
complex inner product space, the new module proves

    E_r ||sum_a chi(r a) v(a)||^2 = sum_a ||v(a)||^2.

The expectation has weight 1 / |F_q|; the outcome sum is unnormalized.
Multiplication of r by the fixed nonzero basis element e_j preserves the
identity. This reuses `sum_norm_sum_smul_sq_of_orthogonal` and
`sum_fixedCharacter_mul_fixedCharacter` from main's
`Combining/Points/Commutation.lean`, rather than reproving orthogonality.

A character average alone does not give a field-size-independent bound for
one fixed character. The paper instead uses binary trace postprocessing.
The new theorem `tildeObs_opDistSq_le_four_consistencyDefect` proves, for each
W and each fixed j, that the uniformly averaged observable distance is at
most four times the uniformly averaged field measurement consistency defect.
Both sides use the actual six-register state and `placeSide` placements.
The proof uses data processing, the factor-two agreement bound, and the
two-outcome instance of `povm_to_obs`. It assumes no bound on the defect.

Source: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-construct-the-paulis`, the paragraph immediately following
`eq:qld-pulling-12` and preceding its detailed justification; blueprint
`lem:qld-construct-the-paulis`, Item 2.

## Statement integrity and remaining obligation

Paper assumptions: the constructed projective measurements, passing strategy,
and construction error from the global polynomial measurements. The public
Lean target retains its original admissible parameters, epsilon in [0,1],
nonnegative deltaG, projective setting, and explicit `GlobalPairWitness`.
That witness remains a supplied conditional premise, not a proved source
construction. No new target hypothesis has been added.

Paper conclusion: observable self-consistency at a construction error absorbed
into deltaS, uniformly over register vectors, separately for every W and j.
Lean conclusion: the unchanged `deltaConstructPaulis C epsilon deltaG m d q`
bound, with one universal C and the same quantifiers. Verdict: public signature
and conclusion unchanged; the finite-character conversion is proved, but the
construction-scale measurement estimate `eq:qld-pulling-cons` remains open.
No source theorem is newly marked proved in the blueprint.

## Validation

Both `CharacterConsistency.lean` and `Consistency.lean` pass focused Lean
checks. The former has no proof holes. The latter retains its five inherited
holes, including the named target. The two Parseval lemmas, the general
fixed-character defect bound, and its `tildeObs` specialization have axiom
closure exactly `propext`, `Classical.choice`, `Quot.sound`.
`tildeObs_selfConsistent` still depends on `sorryAx` and is not discharged.
The hook installation check and whitespace check pass.

Publication and exact-head CI are subsequent gates; the session's final
receipt records their actual outcome. No review or merge is authorized here.
