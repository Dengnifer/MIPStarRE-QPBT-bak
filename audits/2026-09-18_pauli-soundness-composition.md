---
title: "Pauli soundness composition: statement-integrity audit"
date: 2026-09-18
issue: "#529"
---

## Scope

This audit records the documentation of the kernel-checked declaration
`MIPStarRE.QPBT.pauli_soundness` at the checkpoint headed by
`067aace3615567ca204dd3a92d3006ae62c5972e`. The public declaration and its
checked proof are preserved. The source comparison is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
and the closing extraction argument is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.

## Statement comparison

Paper assumptions: an admissible tuple `(q,m,d)` and an arbitrary strategy for
the Pauli basis game whose value is at least `1 - epsilon`; the paper leaves
the finite-dimensional strategy domain and the nonnegative error boundary
implicit. Universal constants precede the tuple, error, and strategy.

Lean assumptions: `AdmissibleParams`, a real `epsilon` with `0 <= epsilon`,
and an arbitrary finite-dimensional `Strategy (pauliBasisTest P)` with
`1 - epsilon <= S.value`. The fixed self-dual field model selected by
`AdmissibleParams` and finite carrier types are faithful domain data. No
projectivity, global polynomial-pair witness, extraction witness, bridge, or
repair input is added to the public theorem.

Paper conclusion: local isometries into auxiliary tensor factors, a normalized
auxiliary state, one state-distance estimate, and both complete Pauli-family
operator comparisons for `W` in `{X,Z}`, all at the universal robustness
scale `a (md)^a (epsilon^b + q^(-b) + 2^(-bmd))`.

Lean conclusion: a `PauliSoundnessWitness` on the original strategy spaces,
with the unsquared state norm and the two complete summed squared operator
distances, universally bounded by the same `deltaQld` form for every Pauli
basis. The Naimark construction and both operator transfers are internal
proof steps; they are not theorem premises.

## Composition details

The two private scalar estimates are mathematically auxiliary. On
`0 <= epsilon <= 1`, `deltaQld_sq_le` absorbs the square of the intermediate
error by replacing `(a,b)` with `(3*a^2+2*a,b/4)`. For `epsilon >= 1`,
`deltaQld_mono_epsilon_ge_one` compares the endpoint value at `1` with the
value at `epsilon`. The unit-interval composition first applies the checked
projective-setting result to the questionwise Naimark dilation, then applies
the Alice and Bob operator transfers and absorbs `3*d + 6*d^2` into a common
universal scale. The endpoint branch reuses the witness at `epsilon = 1`;
strategy-value nonnegativity supplies its passing premise. Thus `epsilon=0`
is included without division, and `epsilon>1` is handled without adding an
upper-bound hypothesis to the public theorem.

## Source-game qualification

The checked result is for the repository's existing formalized game. It does
not prove the printed source's claimed tensor-code correspondence or the
associated auxiliary-parameter `K` bound; those remain tracked by issue #527
and `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. Issues #598 and #524
are separate obligations. Consequently the source-labelled blueprint node
`thm:pauli` is not marked as an unrestricted paper match. The separate node
`thm:pauli-formalized-game-support` records the checked formalized-game result.

## Verdict

Paper assumptions versus Lean assumptions: faithful finite-dimensional and
nonnegative-error boundary encoding; no extra load-bearing proof data.
Paper conclusion versus Lean conclusion: all three conclusions and their
quantifier order are preserved, with the project-local `PauliSoundnessWitness`
and `deltaQld` encodings. Verdict: **formalized-game theorem complete;
printed-source correspondence remains open**.

## Evidence and limits

The supplied kernel evidence reports a fresh 9258-job root build and axiom
closure `propext`, `Classical.choice`, and `Quot.sound` for
`pauli_soundness`, `exists_projective_setting_isometry_bounds`, and both Naimark
operator-transfer bounds. The normal merge of PR605 parent
`ffec0957019fedb5f7877adaec924e3791faa007` was attempted but was blocked by
the worktree's read-only shared Git metadata when Git tried to create
`ORIG_HEAD.lock`; no proof source was rewritten and no public merge/status,
CI, or review action was performed in this task. The incoming Naimark-removal
path was treated as a substantive conflict and was not adopted.
