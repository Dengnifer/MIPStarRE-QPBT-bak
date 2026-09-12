# Issue 510: direct projection estimate, attempt 3

The target `exists_extendedLinesWitness` remains unproved. Its signature and
proof body are unchanged at the pinned base
`fd83ecda4ec0bf8397687eff9ebcc034525d0dd6`.

## Operator estimate

Let Q and R be orthogonal projections and suppose W R = W. Put D = Q - W*.
The proved auxiliary `projection_complement_le_of_mul_eq` states the operator
inequality

    I - R <= 2 (I - Q) + 2 D* D.

Indeed, R W* = W*, so

    I - R = (I - R)(I - Q) + (I - R)D.

Apply the Gram-matrix inequality for a sum and contract the left projection
in each term. Idempotence of Q identifies (I-Q)*(I-Q) with I-Q. The proof
uses positivity of a Gram matrix and order preservation under conjugation.
It assumes no consistency estimate, line witness, or global-pair witness.

This is a direct operator prerequisite for replacing the nested scalar
Cauchy--Schwarz argument near paper `claim:17-3`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
For ordered point effects one takes W ending in the desired point projection
R. Applying the inequality in states weighted by line effects is a possible
next step toward a linear deficit estimate. That averaged estimate has NOT
been formalized here. Even such an estimate would leave the dimension
dependence and extended-line construction to be discharged.

## Predecessors and limits

The immutable receipts of `prover-510-20260912-01` and `-02` were read before
proof work. Attempt 1, commit `e31df23c592e0db8c55376cdbfe616c30597f2a1`,
proved the scalar quarter-power obstruction. Attempt 2, commit
`07fa14c1d1e55707d0156ceb49e7b53085b98a88`, proved the joint subline law
and a conditional 4 m^2 deltaP bound. Neither route was repeated or edited.
Saved histories were searched for the target and evaluation comparisons.
Commits `924d473e2a440d9199dc69fe4824a3f0791f7c32` and
`6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` contain conditional construction
content, but do not discharge the present target. No divergent branch was copied.

The prior recorded lower bound is 32,394 seconds through attempt 2's
06:39:57Z checkpoint. Attempt 3 began at 07:29:57Z and has a separate
25-minute cap. Its elapsed time must be added to that lower bound; dispatcher
token counters, including resumed counters, must not be summed blindly.

## Statement integrity

Paper `lem:qld-4-13` assumes the surrounding admissible passing projective
strategy and constructs extended-line POVMs, axis degree d, with both field
answer comparisons bounded by poly(m^2 epsilon, md/q).
Lean retains the same existing parameter and strategy quantification and
existential point witness. Its existing direct line carrier, completed Option
answers, and corrected sum interpretation of polynomial error remain as
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
Verdict: no statement change; the source-facing obligation remains open.
The new theorem is a separately proved operator inequality, not a claim of
closure for a paper theorem. No blueprint certification was changed.

## Checkpoint gate

Focused checks and axiom closure are recorded in the session receipt. Full
build, publication, exact-head CI, and independent review are required before
integration. The author does not launch a reviewer. If those waits exceed the
25-minute bound, the clean local commit is the authorized checkpoint.
