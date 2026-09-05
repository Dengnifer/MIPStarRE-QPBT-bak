# Issue 118: point-error dependence in the line construction

Session: `prover-118-20260906-01`, September 6, 2026 (worktree local date).
Inspected head: `691b671`. No theorem statement or proof was changed.

## Source and proved prerequisite

The primary handoff is
`/home/drx/MIPStarRE-qpbt/results/telemetry/sessions/mathfix-201-20260906-03.last.md`.
The corresponding source passages are `lem:pasting` in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525` and
`lem:qld-xz-lines` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`.
The latter proof uses the particular point measurements obtained in
`lem:qld-4-10`. Its two marginal comparisons, `eq:pasting-q1`, have error
controlled polynomially by the strategy error. This control is used together
with the conditional collision estimate `md/q` when invoking pasting.

At committed prerequisite `fe74413`, `exists_pasting_error` is proved using
the one-sided argument, not the conditional register-exchange theorem. Its
error is `(3 C + 19) (eta^(1/4) + delta^(1/8))`. Thus the marginal comparison
error remains an input to the resulting estimate. The additive correction
is essential; the product-form `IsPolyErr₂` still present at `691b671` is
not the corrected predicate supplied by that prerequisite.

## Obstruction in the current helper

`exists_combinedLinesWitness_ofPointsWitness`, in
`MIPStarRE/QPBT/Combining/Lines.lean`, quantifies over every real `δQ` and
every `points : CombinedPointsWitness S δQ`, but promises a bound
`deltaP ε (md/q)` independent of `δQ`. The witness fields in
`MIPStarRE/QPBT/Combining/Witnesses.lean` control self-consistency and the
two ordered-product comparisons only by `δQ`. They do not bound `δQ` by
a function of `ε`. Pasting therefore does not justify dropping that parameter.

This is a precise missing quantitative implication in the proposed proof,
not a formal counterexample to the existential line construction. No claim
that the full `ProjectiveSetting` assumptions are inconsistent or admit a
specific counterexample is made here. In particular, a new point witness
constructed by issue 117 cannot simply replace the supplied witness: the
conclusion compares the lines with that supplied witness's `Q` effects.

The source-facing theorem already quantifies the point error function and
the point construction together. A source-aligned repair should keep that
public statement and use an internal estimate retaining the actual point
error, then specialize it to the constructed points. This would require
changing the current helper interface and adapting its callers; it is not
implemented here. No bound on the arbitrary witness is assumed, and no
model or X-marginal field is chosen.

This issue is separate from the established extended-line bound
`m * poly(epsilon, md/q)` documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. Nothing here establishes
the stronger printed bound or changes the completed claims 17-2 and 17-3.

## Statement integrity audit

- Paper assumptions: a projective strategy and the points constructed in
  `lem:qld-4-10`, with their polynomially controlled errors.
- Helper assumptions: a projective setting and an arbitrary point witness
  with arbitrary error `δQ`.
- Paper conclusion: paired line POVMs consistent with the constructed points,
  with error polynomial in `ε` and `md/q`, including the symmetric comparisons.
- Helper conclusion: the same kind of consistency with the supplied points,
  uniformly in their unrestricted error.
- Verdict: the helper strengthens the quantification over point witnesses;
  its quantitative dependence is not justified by the cited pasting proof.
  The source-facing theorem's statement is left unchanged.

## Integration and validation record

An attempted history-preserving `git merge --no-commit --no-ff fe74413`
used the primary checkout's hooks. It conflicted in `Apply.lean`,
`Lines.lean`, direct-low-degree transport, conditional linearity, and
documentation. Because `Apply.lean` is explicitly outside this session's
ownership, the merge was aborted without resolving any conflict. Neither
prerequisite history was rewritten; issue 117 was inspected through Git
objects, not modified in its sibling worktree.

The original Lean tree is restored. No Lean validation, full build, review,
push, or commit was run. The primary hook integration was not completed,
so these diagnostic notes are left uncommitted rather than bypassing the
required hook prerequisite. The next owner action is to reconcile the
prerequisite histories and authorize the internal helper-interface repair
while preserving the source-facing theorem and downstream proved claims.
