# Issue 118: point-error audit and immutable dependency boundary

## Attempt 2: proved point marginals and the paired-line construction

Session `mathfix-118-20260906-02`, starting September 6, 2026,
04:27:21 +0800, on integration baseline `b49beae`. The original gap start
remains September 5, 2026, 19:24 UTC. This is attempt **2 of 10**; neither
the count nor the approximately one-and-a-half-working-day limit is reset.

**Verdict: useful partial proofs, not a converged correction.** The integration
baseline removes the dependency reconciliation obstruction described in attempt
1 below. This attempt proves the previously missing uniform-point marginal
estimates, joint self-consistency in the defect convention, and the sandwich
POVM with both axis-degree bounds. It does not adopt a corrected quantitative
signature for the arbitrary-point line helper. Its existing hole and all three
holes in `Apply.lean` remain explicit. No witness field, source theorem
statement, game, or source definition is changed.

### Mathematical statements proved

Fix directed opposite placements and a joint point witness with supplied
error `t`. Write `Q_ab` for its effects on the first placement and `X_a,Z_b`
for the expanded point effects on the second; all averages below are over
independent uniform points `x,z`. The actual witness fields give

\[
 \mathbb E\sum_{a,b}\|(Q_{ab}-X_aZ_b)\psi\|^2\le t,
 \qquad
 \mathbb E\sum_{a,b}\|(Q_{ab}-Z_bX_a)\psi\|^2\le t.
\]

The new declarations in `Combining/Lines.lean` prove:

1. `CombinedPointsWitness.absorb_X_le` and `absorb_Z_le`: the same average
   of `||Q_ab-X_a Q_ab||²` and `||Q_ab-Z_b Q_ab||²`, respectively, is at
   most `t`.
2. `CombinedPointsWitness.marginal_X_distance_le` and
   `marginal_Z_distance_le`: the squared operator distances of the marginal
   sums `sum_b Q_ab` from `X_a` and `sum_a Q_ab` from `Z_b`, respectively,
   are at most **`4 * t`**. These are uniform-point estimates, not yet the
   evaluated-line comparisons under the line-point distribution.
3. `CombinedPointsWitness.self_consistency_defect_le`: joint consistency
   defect under the uniform point-pair law is at most **`t`**, from the
   existing projectivity and squared-distance self-consistency fields.
4. `ProjectiveSetting.combinedLineMeasurement`: for every side and line
   pair, the effects `X_fX Z_fZ X_fX` form a POVM on the existing local
   space. The two `combinedLineMeasurement_axis_degree_*` lemmas prove
   vanishing outside the degree-`d` answers on the respective axis line.
   `combinedLineMeasurement_sum_Z` proves the exact X marginal identity
   **for this construction only**, not for arbitrary line witnesses.

The two generic estimates `norm_sub_projective_mul_sq_le` and
`norm_marginal_sub_sq_le` isolate the linear algebra. The first follows by
applying the contraction `I-B_b` to `A-B_b D`. For the second, fix a marginal
fiber of orthogonal projections `Q_b` commuting with the corresponding
projective effects `B_b`. Set

\[
 U=\sum_b Q_b(Q_b-B_bQ_b),\qquad
 V=\sum_b B_b(Q_b-B_bD).
\]

Projectivity, commutation, and completeness of `B` imply
`U+V = sum_b Q_b-D`. Orthogonal left multiplication bounds `||U psi||²`
by `sum_b ||(Q_b-B_bQ_b) psi||²`, and the contraction estimate bounds
this by `sum_b ||(Q_b-B_bD) psi||²`. Orthogonality of `B` gives the same
bound for `||V psi||²`. The squared triangle inequality supplies the factor
four. For the X marginal take `B_b=Z_b,D=X_a`, and use `consistent_ZX`;
for the Z marginal interchange the indices and use `consistent_XZ`.
Orthogonality comes from `points.projective`; commutation comes from opposite
placements, not a new assumption on the source theorem. This is the source
calculation at `14_analysis_of_the_pauli_basis_test.tex:902-935`, made
quantitative. The generic proof does not require completeness of the fixed
fiber `Q_b`, nor commutation of `B_b` with `D`.

Joint self-consistency uses the agreement identity for projective measurements,
as required at paper lines 955--960. The line POVM proof specializes
`pastedMeasurement_isMeasurement` with the Z measurement inside the X
measurement, and relabels the answer pair. Its support proof uses the existing
expanded line degree bounds. These are precisely the construction and support
argument at paper lines 942--949. No marginal identity is postulated.

### Counterexample checks and statement integrity

The original obstruction is still an unsupported quantification, not a
constructed counterexample to the printed theorem. The estimates proved here
retain `t`, so they do not infer zero error when `epsilon=0` but the supplied
witness has positive error. At `t=0` the two marginal distances and absorption
distances vanish. There is no restriction `t<=1`, no division by `t`, and no
alphabet-size loss. In the generic marginal estimate the zero fiber `Q_b=0`
is allowed; completeness is used only for `B`. Noncommutation of the two
line measurements does not affect sandwich positivity or its axis support.
Only the X marginal of the X-Z-X sandwich is asserted to be exact. These are
algebraic edge-case checks, backed by universal Lean proofs; no finite
strategy counterexample search is claimed.

**Statement audit:** the source point calculation assumes the constructed
projective points, their ordered product comparisons, and opposite placements,
and concludes closeness of their two marginals to expanded point measurements.
The auxiliary Lean statements assume an arbitrary witness with those actual
fields at error `t` and conclude squared-distance bounds `4*t` for both
marginals. Verdict: explicit quantitative auxiliary with faithful boundary
types, not a replacement of the source theorem. The generic commutation and
orthogonality assumptions are discharged from projectivity and placements in
both witness applications. The source sandwich assumes projective expanded
line measurements and their axis support, and concludes a POVM with the same
support; Lean derives exactly these properties from `ProjectiveSetting`.
The source-facing `exists_combinedLinesWitness`, Claims 17-2 and 17-3, and
all `Apply.lean` statements and proofs are unchanged.

### Remaining construction and use analysis

The complete source/blueprint use inventory in attempt 1 below remains the
consumer inventory. In particular the paper uses are restricted averages
(1058--1061), construction and degree of extended lines (1118--1132), their
consistency calculation (1241--1246), global pairs (1278--1282), and the
extraction calculations listed below. The blueprint descendants and three
prose references listed there remain unmodified. The new auxiliary nodes are
`lem:combined-point-marginal-projection-estimates`,
`lem:combined-point-marginals-supplied-error`, and
`lem:combined-line-sandwich-construction`; only these completed statements and
proofs receive new completion markers. The combined-line source entry stays
`notready`.

The next construction steps are now more specific:

1. Express the proved marginal sums as the postprocessed point measurements,
   transport their `4*t` bounds and joint self-consistency to the product
   line-point law, and handle the completed `Option` answers faithfully.
2. Combine them with the expanded line comparisons, retaining dependence on
   both `epsilon` and `t`. These must prove both actual marginal hypotheses
   of the one-sided `exists_pasting_error`; they must not be new inputs to
   the source theorem.
3. Establish the conditional line-evaluation collision bound, carry out
   pasting for every directed opposite placement, and prove consistency of
   the already constructed `combinedLineMeasurement`.
4. Correct the internal quantitative interface with its proved dependence
   on `t`, specialize to the constructed `K * epsilon^(1/8)` error, and
   discharge the additive polynomial error composition. Adapt both
   arbitrary-point extended-line helpers without changing source statements.

Sufficiency for the complete consumer set and minimality of a final repair
are **not established**. In particular this attempt does not claim that a
compiled source wrapper proves the source theorem. The factor four is a
proved sufficient constant for the intermediate marginal estimate, not an
optimality claim. Dropping `t`, replacing the supplied points, or assuming
line marginals remains unjustified. The stronger extended-line error and
direct-to-source game transport remain the separate obligations documented
in the baseline; PR 205's paper-gap corrections are not edited here.

### Validation and operator handoff

All checks reuse `/tmp/issue118-lean-validation/lib`. The changed Lean file
passes targeted type checking. Fresh private artifacts then type-check the
complete affected import chain `Lines`, `EvalDeficit`, `SubLineDeficit`,
`Claims`, `QPBT`, and the project root, together with `Apply` as an additional
task-requested consumer check. Only the existing one line-helper warning and
three `Apply` warnings remain. There is no new `sorry`, axiom, or bypass.
All twelve new declarations have axiom dependencies exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

The declaration checker resolves **1,798** listed declarations, including the
twelve new links in the locally generated, ignored `blueprint/lean_decls`.
Blueprint web generation exits successfully, but retains the two unresolved
labels `lem:qld-sublines-restricted-blocks` and `lem:qld-sublines-seed-blocks`
and bibliography warnings already present in the integration baseline log;
it is not a diagnostic-free build. The LaTeX convention check passes. The
paper-gap style check finds no changed notes. The full blueprint
synchronization check continues to report the **231 pre-existing stale
declaration-list entries**; those unrelated entries are not removed. New
links are present in both the chapter and `blueprint/lean_decls`.
Logs are `/tmp/issue118-attempt2-*.log`. No full build, shared-cache write,
subagent, sibling modification, push, post, or merge is performed.

Draft operator announcement for #27: **Attempt 2 proves both uniform-point
marginals at `4*deltaQ`, joint self-consistency at `deltaQ`, and the line
sandwich with axis support; pasting and quantitative specialization remain
open, so no correction is adopted.** No adopted-correction event or design
decision is appropriate yet. Cumulative working time remains operator-owned;
the supplied original start and attempt count above are unchanged. At local
04:47 on September 6, this session has used approximately twenty minutes;
the elapsed wall time from the original gap start is approximately eighty-three
minutes, not a measurement of cumulative working time. No new mathematical
definition or game change requiring an owner decision has been identified.

---

## Attempt 1 record (preserved)

Session `mathfix-118-20260906-01`; attempt **1** for this gap, independently
of issue 201. Dispatch start: September 6, 2026, 03:24:48 +0800.
Inspected worktree head: `691b67159f9ead45b9de144df3bd46e015430e70`.

**Verdict: not converged.** The reported obstruction is a missing quantitative
implication in an internal helper, not a demonstrated counterexample to the
source theorem. No public signature, definition, game, or proof was changed.
This report does not adopt a corrected theorem or claim consumer convergence.
The previous uncommitted brief and telemetry changes are preserved.

## Source assertion and obstruction

The primary source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
Lemma `lem:qld-xz-lines`, lines 882--894, asserts that for the strategy under
analysis there is a function polynomial in the strategy error and `md/q`,
and paired-line POVMs on both expanded player spaces, consistent with the
joint points, in every symmetric placement. Answers have degree at most `md`,
and degree at most `d` on an axis-parallel line. The points are those constructed
by `lem:qld-4-10`, not an independently supplied family with arbitrary error.
This dependence is explicit at line 900. The proof at lines 937--961 uses
`eq:pasting-q1` and joint-point self-consistency as the consistency inputs to
`lem:pasting`.

The latter lemma is at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
It assumes a distribution of questions, a conditionally collision-bounded
second function family, projectivity of the second measurement and joint
answer measurement, two marginal consistency bounds, and joint-answer
self-consistency. Its sandwich conclusion depends on **both** the collision
parameter and the consistency parameter.

In contrast, `exists_combinedLinesWitness_ofPointsWitness` at
`MIPStarRE/QPBT/Combining/Lines.lean:65` quantifies over every real point error
and every `CombinedPointsWitness` at that error, while its output error is
independent of that parameter. The fields `self_consistent`, `consistent_XZ`,
and `consistent_ZX` in `Combining/Witnesses.lean` supply only bounds by the
given point error. No field bounds that error in terms of the strategy error.
Replacing the supplied points by another witness is invalid: the conclusion
is consistency with the original witness's effects.

There is no concrete `ProjectiveSetting` counterexample here. In particular,
a positive numerical value for the missing error does not construct a
strategy. The sound conclusion is that the cited argument does not justify
the internal helper's stronger quantification.

## Quantitative correction to pursue, not an adopted statement

Write `rho = md/q`, `t` for the supplied point error, and `u(epsilon,t)`
for a bound to be **proved internally** on both marginal defects and joint
self-consistency. Retain this dependence in the line estimate before
specializing to the source points. At the immutable pasting prerequisite
listed below, the available estimate is

\[
  (3C+19)\bigl(\rho^{1/4}+u(\varepsilon,t)^{1/8}\bigr).
\]

The missing marginal theorem must derive `u` from the witness fields and
the expanded line--point comparisons. It must not assume those marginal
comparisons as new hypotheses of a source-facing theorem. Merely changing
the number of arguments of `deltaP` would not prove that theorem.

For example, if the marginal calculation establishes
`u(epsilon,t) <= A * (epsilon^a + t^b)` with positive universal exponents,
then subadditivity of the power `1/8` gives an upper bound by a constant times
`rho^(1/4) + epsilon^(a/8) + t^(b/8)`. Substitution of the constructed error
`t = K * epsilon^(1/8)` gives an additive polynomial bound in `epsilon,rho`:
on `[0,1]`, use exponent `min(a/8,b/64)` for the strategy error. For larger
strategy errors the normalized POVM consistency defect is at most one.
This is a scalar composition argument, **not a proof of the missing marginal
calculation**; no values of `A,a,b` are asserted by this report.

The edge cases distinguish the intended correction from the old interface:
at zero collision error and positive marginal error the estimate retains the
marginal term; at zero marginal error it retains the collision term; both
terms vanish when both errors vanish. An unrestricted large point error does
not imply a small output error. These checks concern the estimate, not the
existence of strategies at each boundary.

No mathematical definition change is proposed. In particular, this session
does not implement its own replacement for `IsPolyErr₂` or duplicate PR205.

## Consumer inventory and limits of sufficiency

The direct paper uses of `lem:qld-xz-lines` are the restricted-law comparison
at lines 1058--1061, the extended-line construction at 1118--1132, and the
consistency estimate at 1241--1246. Retaining the same line witness type and
specializing to the constructed points would preserve these uses of pair
consistency and axis degree. The error correction alone does not establish
the stronger printed error of `lem:qld-4-13`; that separate discrepancy
remains in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The global polynomial-pair argument at 1278--1282 uses extended lines.
Its consumers include the extraction calculations at 1423, 1465--1492,
1584, 1627, and 1671. This session does not certify those calculations by
compiling only the immediate wrapper.

A comment-stripped scan of statement/proof `\uses{}` blocks, attaching
`\proves{}` blocks to their named statements, gives the following descendants
of `lem:qld-xz-lines` in the current blueprint:

- Chapter 15: `lem:restricted-line-mixture-bounds`,
  `lem:qld-sublines-one-point-deficit`, `lem:claim-17-1`, `lem:claim-17-2`,
  `lem:claim-17-3`, `lem:qld-4-13`, `lem:qld-4-13-established`, `lem:qld-4-7`.
- Chapter 16: `def:s-w-marginals`, `lem:s-w-marginals-projective`,
  `def:tilde-m-measurement`, `lem:tilde-m-projective`, `def:tilde-w-observables`,
  `lem:tildew-product-form`, `lem:qld-nonencoding-mass-bound`,
  `lem:qld-constructing-the-paulis-helper`, `lem:qld-construct-the-paulis`,
  `def:v-swap-unitary`, `lem:v-swap-conjugation`, `lem:qld-unitary`,
  `lem:qld-unitary-given-global-pair`, `lem:qld-extraction-error-form`, `thm:pauli`.
- Chapter 13: `cor:pauli-binary`, `def:introparams`, `lem:delta-bound`.

Actual prose references also discuss the construction and its scope in
`rem:claim-17-2-line-marginal`, `rem:qld-4-13-source-defects`, and
`rem:qld-4-7-divisibility`. A dependency scan is an inventory, not a proof
that every descendant's mathematics is repaired.

In Lean, the only direct invocation of the arbitrary-point combined-lines
helper is `exists_combinedLinesWitness` in `Lines.lean`. The restricted
consistency theorem in that file, `EvalDeficit.lean`, `SubLineDeficit.lean`,
and `Claims.lean` use supplied witnesses, rather than invoking that helper.
Their existing error dependence must be preserved, including the proved
claims 17-2 and 17-3. `Apply.lean` independently repeats the arbitrary-point
quantification in `exists_extendedLinesWitness_ofPointsWitness` and
`exists_extendedLinesWitness_established_ofPointsWitness`; their existential
wrappers instantiate it with constructed points. These helpers need the same
quantitative treatment, not a new assumption on their source-facing wrappers.

Minimality is not established. Dropping `t`, substituting a different point
witness, or assuming the required point-to-line conclusion is not a repair.
Restricting the source theorem itself to a new external error hypothesis is
unnecessary: its own point construction supplies the error. The weakest
sufficient internal interface remains to be proved and compared.

## Immutable prerequisites and integration experiment

- Pasting: `fe74413d25ddb7b5bba5f1d043a20c0b18351ec4`,
  `Games/Sandwich.lean:242`, `exists_pasting_error`. This is the one-sided
  theorem, not `exists_pasting_error_of_register_exchange`.
- Constructed points: `6b4b75d408be5399a1867166bffcc3aa56de6e4b`,
  `Combining/Points.lean:353`, `exists_combinedPointsWitness`. Its proof
  chooses a universal error of the form `K * epsilon^(1/8)`.
- Current head still has the product-form `IsPolyErr₂` at
  `Games/ErrorFunctions.lean:36`. The pasting prerequisite has the corrected
  sum form, on the closed nonnegative quadrant. These are different contracts,
  not interchangeable implementations of an unchanged imported theorem.

No merge was performed. Git 2.34.1 does not support `merge-tree --write-tree`.
A read-only three-tree screen using merge base `c21c70c` shows conflict
markers in `Combining/Apply.lean`, `Combining/Lines.lean`, four
`Observables` files (`Anticommuting`, `Defs`, `LineDefs`, `Setup`),
`Test/CanonicalParams.lean`, `Test/PauliBasisTest.lean`, blueprint Chapters
13 and 14, and the gap register. There are **four** merge bases, so this screen
is not the definitive conflict set of a recursive merge. The previous brief
records additional conflicts in a real merge attempt; it is not contradicted
by this single-base diagnostic.

The prerequisite histories also contain workflow changes outside the allowed
edit trees. A whole-branch replacement or a selection of the current side
would not be faithful integration. In particular, incoming-only paths include
`DirectLowDegree/SeedIndexedSoundness.lean`,
`DirectLowDegree/Transport/PointAgreement.lean`, and
`DirectLowDegree/Transport/Simultaneous.lean`; none was removed or overwritten.
The precise dependency is a scope-safe reconciliation of the additive-error
pasting history and the constructed-point history with the current claims,
not a reimplementation of the already proved pasting theorem. During the
reported downstream propagation, this session uses the task's dependency-report
fallback rather than adopting signatures against mismatched prerequisites.

## Validation and statement integrity

All checks below use the unchanged worktree source and its existing dependency
artifacts; they are baseline evidence, not validation of either prerequisite
or a corrected consumer chain.

- `lake env lean MIPStarRE/QPBT/Combining/Lines.lean`: exit 0; existing
  `sorry` warning at the arbitrary-point helper.
- `lake env lean MIPStarRE/QPBT/Combining/Claims.lean`: exit 0, no diagnostics.
- `lake env lean MIPStarRE/QPBT/Combining/Apply.lean`: exit 0; existing
  `sorry` warnings at lines 45, 96, and 143.
- The `sorry|axiom` scan confirms one direct hole in `Lines.lean`, three in
  `Apply.lean`, and none in `Claims.lean`; docstring matches are not new holes.
- No full build, blueprint edit, paper-gap edit, review, push, or runtime-state
  edit. Only this audit is added. No paper mirror is changed.
- Hook check fails: `core.hooksPath` points to the primary checkout's
  `.githooks` rather than this worktree's `.githooks`. No hook bypass or
  repository configuration change is attempted; this report is uncommitted.

Statement audit: the paper assumes its constructed points with polynomially
controlled errors; the internal helper allows arbitrary witness errors.
Both conclusions concern paired-line consistency and axis degree, but the
helper promises independence of the arbitrary error. Verdict: unsupported
strengthening of the internal quantifiers; no source counterexample proved.
All existing public statements and proved claims are unchanged.

## Operator handoff

Suggested unposted progress line: “#118 attempt 1 confirms the arbitrary-point
error omission; no source counterexample or correction adopted. Immutable
pasting/point prerequisites identified; claims 17-2/17-3 remain unchanged.”

Issue 119 must not erase the point error when assembling extended lines.
Reconcile the prerequisite histories, prove the two marginal estimates with
their actual point-error dependence, construct lines, specialize to the
constructed points, and only then assemble the established extended-line
bound. The printed stronger extended-line estimate and the source-game
transport remain separate obligations. No owner decision to change a game or
definition is requested or implied by this audit. This is attempt 1, not an
exhausted-budget escalation; issue 201's attempt count is not inherited.
