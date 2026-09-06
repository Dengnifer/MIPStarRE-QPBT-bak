# Issue 118: point-error audit and immutable dependency boundary

## Attempt 7: actual conditional pasting and restored source-law defect

Session `mathfix-118-20260906-07`, baseline
`857681fc1cc60ec13925b1533c7269fdcf634b28`, attempt **7/10**. The original
anchor remains September 5, 2026, 19:24 UTC. The resumed session started
at 23:29:11 UTC with **9852 cumulative working seconds** supplied by the
operator for attempts 1--6. Read-only process inspection confirms actual
arguments `-m gpt-6-astra -c model_reasoning_effort="xhigh"`; no new session
was launched. Earlier attempt sections below are historical records, not
the current verdict.

### Mathematical statement and proof

The printed existence theorem `lem:qld-xz-lines`, paper lines 882--894,
is still not disproved. Its quantifiers concern the constructed point
family, both expanded player spaces, every pair of line descriptors, and
all directed opposite placements. The conclusion is polynomial consistency
on independent source line-point samples and axis-degree support. The
internal arbitrary-point helper, unlike that source theorem, quantifies an
arbitrary supplied point error but omits it from the bound. Zero-X-direction
completed collisions of `T` and `T+1` remain a separate proof obstruction.

Two new theorems in `Combining/Lines.lean` now apply the actual construction,
rather than adding another representation interface. There exist a universal
`C >= 1` and `f` satisfying the current additive `IsPolyErr₂` such that, for
every admissible parameter tuple, projective setting with error `epsilon`,
supplied point witness of error `t`, and directed opposite placement pair,

```
rho = md / card(ScalarQ),  u = 8*t + C*(epsilon + sqrt epsilon),
d_E <= f(rho, u/r),
d   <= r*f(rho, u/r) + 1/(2*card(ScalarQ)).
```

Here `r > 0` is the retained mass of nonzero X directions, `d_E` is the
actual conditional defect with completed answers ordered Z then X, and `d`
is the original product-law defect with answers ordered X then Z. The
supplied points are on the first placement and the actual XZX line POVM
on the second. Field-model cardinality identifies `card(ScalarQ)` with `q`.
The quantifier order is `exists C, exists f, forall parameters and witnesses`;
neither constant depends on the supplied witness.

For correctness, apply `exists_pasting_error_heterogeneous` with the actual
right Z and X line families, in that order, and the two supplied projective
joint families with completed answers exchanged. The earlier two marginal
bounds are `u/r`, the joint comparison is `t/r`, and the actual product
collision estimate is `rho`. The witness's nonnegative squared distance
proves `t >= 0`, hence `t/r <= u/r`; the setting proves `epsilon >= 0`.
No additional error or consistency premise is introduced. The source
grounding is pasting at paper lines 950--963, its marginal comparisons at
936--949, and `lem:pasting` in Section 6.

All four bipartitions transport the supplied state and effects exactly,
retaining the unused EPR pair. Pulling the defined question map back to the
conditioned original samples resolves duplicated descriptors: common and
local descriptors are then the same components of the sample. We do not
require equality for ambient questions outside the map's image. The proved
evaluated identity identifies the output with the actual XZX POVM. This
proves `exists_combinedLine_conditioned_defect_le`. Bijectively exchange
both answers and apply the existing actual-POVM restoration estimate to
prove `exists_combinedLine_restored_defect_le`, with both `r` and `1/(2q)`
unchanged.

### Counterexample audit and remaining convergence criteria

The zero-X collision example is outside the retained event, and its full-law
mass is paid for rather than removed from the game. Zero Z directions are
retained. Unequal carrier dimensions, unequal supplied families, spectator
entanglement, `q=2`, and evaluations with collisions introduce no additional
assumption. A positive supplied `t` remains in the error even at `epsilon=0`.
Inconsistent duplicated descriptors are handled by the pushforward identity,
not by a new domain restriction. These are symbolic checks and general
proofs, not an exhaustive computational enumeration of strategies.

**Correctness:** both displayed actual bounds are proved, and axiom audits
exclude dependence on the unfinished source theorem. **Sufficiency:** actual
conditional application, descriptor identification, answer order, and mass
restoration are discharged. Full source/consumer convergence remains open:

1. Specialize the constructed point error `t=K*epsilon^(1/8)` and formalize
   additive polynomial composition, including large parameters. The current
   pasting API exposes general positive exponents, not the specific powers
   in its construction. If `f(x,y)<=A*(x^a+y^b)`, `r>=3/4` gives
   `r*f(rho,u/r)<=A*rho^a+A*max(1,(4/3)^(b-1))*u^b`. On the unit square,
   `u<=(8*K+2*C)*epsilon^(1/8)` and `1/(2*q)<=rho/2`; exponents `b/8`
   and `min(a,1)` suffice. This calculation does not assume `f` monotone.
2. Assemble the source-facing line witness, including exchange of opposite
   placements in the consistency expression and the already proved axis
   degree properties. Only then discharge or replace the wrong internal
   arbitrary-point helper; no speculative public signature is committed.
3. Adapt both arbitrary-point extended-line helpers and their constructed
   point wrappers in `Apply`. Recheck the restricted-average prefactors and
   the error absorption at each mathematical consumer in the complete
   inventory below. Claims 17-2 and 17-3 remain unchanged.

The complete paper-use, blueprint-descendant, actual prose-reference and Lean
inventory under **Consumer inventory and limits of sufficiency** remains
applicable. In particular source uses at 1058--1061, 1118--1132, 1241--1246,
1278--1282, 1423, 1465--1492, 1584, 1627, and 1671 are not certified by these
two auxiliary inequalities alone. The separate stronger-error discrepancy
for `lem:qld-4-13` is not eliminated.

**Minimality:** no final source correction is adopted. Retaining arbitrary
supplied `t` in this proved bound is weaker than requiring it to be small
externally. The source construction supplies its own error. Dropping `t`,
replacing the witness, assuming equal dimensions/families or reverse marginal
bounds, or discarding Z directions remains unnecessary or unjustified.
No definition/game change requiring an immediate owner decision is identified.

### Validation and operator record

The edited file and all six consumer/import-closure files (`EvalDeficit`,
`SubLineDeficit`, `Claims`, `Apply`, QPBT, and the project root) type-check
against fresh private artifacts in `/tmp/issue118-lean-validation/lib`.
Logs use prefix `/tmp/issue118-attempt7-`. Both new declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Existing debt remains one
hole in `Lines` and three in `Apply`, with no new debt. This is Lean
convergence of the bounded increment, not of the final correction.

All **1867** generated blueprint declaration references resolve against the
fresh private root artifact. Blueprint web generation passes with unchanged
warning/error lines; static synchronization retains **231 baseline stale
entries** and **15 baseline header-only proof-status entries**. Paper-gap
style, blueprint LaTeX conventions, source-header integrity, whitespace,
and hook-installation checks pass. The revised gap note compiles with its
bibliography to a thirteen-page PDF under `/tmp/issue118-attempt7-gap-pdf`.
No full build, baseline rebuild, or shared-cache write is performed.

At the validation cutoff, September 6, 2026, 00:09:33 UTC, this session has
used **2422 working seconds (40 minutes 22 seconds)**; adding the supplied
9852 seconds gives **12274 seconds** through that cutoff, without resetting
either budget. Commit preparation and the final report follow this cutoff.
Attempt 7 leaves at most three further sessions under the count limit;
neither the count nor the working-time cap requires immediate escalation.

Statement integrity: public source assumptions, conclusions, games and
witness fields are unchanged. The new auxiliary statements explicitly retain
the arbitrary supplied error in the conclusion and derive all pasting inputs
from the setting and witness. The blueprint adds only the separate auxiliary
`lem:combined-line-actual-pasting-bound`; the source-labelled theorem remains
unfinished. The paper-gap note records the exact inequalities and the
remaining scalar calculation. No paper mirror or PR 205 implementation file
is edited, and no publication, merge, runtime-state edit, subagent dispatch,
or independent-review action is performed.

Unposted operator draft: "#118 attempt 7 proves actual conditioned pasting and
source-law mass restoration, retaining both supplied errors; scalar
specialization and Apply remain open. No final correction adopted."

## Attempt 6: heterogeneous pasting and all directed register placements

Session `mathfix-118-20260906-06`, baseline
`391c86e05b7d96f8879f76169ffa2510bf035365`, attempt **6/10**. The original
budget anchor remains September 5, 2026, 19:24 UTC; this session started at
22:56:19 UTC. The cumulative working-time total remains operator-owned and
was not supplied. A read-only inspection of the executing binary's arguments
confirmed `-m gpt-6-astra -c model_reasoning_effort="xhigh"`, with multi-agent
features disabled. The legacy dispatch spelling did not result in medium
effort. No other session was launched or contacted.

### Source boundary and proved mathematical increment

The printed `lem:qld-xz-lines`, paper lines 882--894, asserts the existence
of paired-line POVMs for the constructed joint points, on either expanded
player space, with polynomial error in `epsilon, md/q`, independent source
line-point samples, all directed opposite placements, and degree at most
`d` on axis lines. Its proof calls pasting at lines 950--963. It remains
**not disproved**. The missing arbitrary supplied-point error and the
zero-X-direction collision of `T` with `T+1` remain the two separate
obstructions recorded in earlier attempts. No public signature is changed
and no final source correction is adopted.

Seventeen new declarations (fourteen theorems and three proof-only
definitions) in `Combining/Lines.lean` establish the following:

1. For any finite carriers `left, right`, include a vector on their tensor
   product into just the `(inl,inr)` sector of two copies of their direct
   sum. This preserves its norm and gives the exact correlation identity
   `<U psi, (A ⊕ B) ⊗ (C ⊕ D) U psi> = <psi, A ⊗ D psi>`.
   Both unused blocks are arbitrary; no exchanged state is added.
2. Direct sums commute with postprocessing and evaluated ordered pasting.
   All consistency defects therefore transport exactly.
3. `exists_pasting_error_heterogeneous` proves the existing one-sided
   pasting estimate for distinct finite player spaces and the two supplied
   projective joint families, with **the same error function**. The two
   forward marginal comparisons and the joint comparison retain their
   actual errors. The only line projectivity assumption is on the right
   second family. Deterministic projective measurements are constructed
   internally only on unused complementary blocks; their outcomes exist
   by normalization, probability, and completeness. They never replace
   the supplied measurements. No equal-space, equal-family, reverse
   marginal, or symmetric-strategy assumption is used.
4. `ProjectiveSetting.exists_opposite_bipartition` constructs all four
   directed regroupings, `AA' | BA''(B'B'')`, `BA'' | AA'(B'B'')`,
   `BB' | AB''(A'A'')`, and `AB'' | BB'(A'A'')`. The accompanying general
   consistency identity applies to every family on these registers.
   The unused EPR pair is retained on the right, not traced out.
5. Adjoining its identity commutes with evaluated pasting. Swapping the
   completed joint answers preserves their conditional self-consistency
   bound `deltaQ/r`. Evaluating the **actual** combined-line POVM in order
   `(Z,X)` is exactly the pasting output with `G1=Z, G2=X`. These identities
   hold for all descriptors and evaluation points, even off the support.

These are independently proved representation and pasting results, not
conditional replacements for the unfinished source theorem. The
heterogeneous theorem uses the existing one-sided API without editing the
PR 205 publication-repair lane. It does not call the conditional
register-exchange pasting theorem.

### Correctness and boundary checks

The isometric proof expands finite coordinate sums. Only the left-right
sector survives, so no dimension-dependent factor, averaging factor, or
normalization loss occurs. It remains valid on unequal carriers (in
particular dimensions two and three). Empty carriers give only the zero
state, so the norm identity still holds; the normalized pasting theorem
correctly excludes them without a new nonemptiness hypothesis. A probability
law supplies a sample, and completeness on the nonzero right space supplies
both deterministic complementary outcomes.

The unused EPR pair may remain entangled with other registers: the transport
identities use the whole state, not a product-state assumption. The two
supplied point families can differ. Answer exchange is bijective but the
evaluation functions need not be; thus the new identities are valid for
degree zero, large degree, `q=2`, zero Z directions, and even zero X
directions. The collision theorem itself continues to use the proved
nonzero-X restriction. These are symbolic edge-case checks within universal
proofs, not claims of exhaustive finite-strategy enumeration. They do not
remove the original unrestricted collision counterexample.

### Remaining obligations, sufficiency, and minimality

Attempt 5's unequal-carrier obstruction and all four register identities
are discharged. The answer-swapped joint input and evaluated sandwich are
also identified. What remains is the actual quantitative application:

1. Instantiate the heterogeneous pasting theorem with the conditioned
   families and the constructed bipartition, using the identity on the
   unused right factor. The two marginal bounds are already in `(Z,X)`
   order and the new swapped joint bound has error `deltaQ/r`. Derive the
   common nonnegative bound from the supplied witness and setting.
2. Transfer the resulting conditional line defect back to `(X,Z)` order
   and reconcile the duplicated descriptors on the support of
   `nondegenerateLinePastingDist`. The unrestricted identities for the
   actual sandwich are proved, but this whole conditional inequality is
   **not yet a Lean theorem**.
3. Use the existing mass-restoration inequality, preserving its factor
   `r` and additive `1/(2q)`. Specialize `deltaQ=K*epsilon^(1/8)`, prove
   additive polynomial composition and the large-parameter bound, and
   only then repair the arbitrary-point helpers and adapt `Apply`.

The full source/blueprint/Lean consumer inventory in attempt 1 is unchanged:
source uses at 1058--1061, 1118--1132, 1241--1246, 1278--1282, 1423,
1465--1492, 1584, 1627, and 1671; all listed Chapter 15, 16, and 13
descendants and the three prose references remain to be justified by a
converged final construction. The new blueprint auxiliary
`lem:combined-line-bipartite-transport` explicitly states its representation
scope. The source node remains unfinished. Claims 17-2 and 17-3, games,
witness fields, and public source declarations are unchanged.

**Sufficiency:** the representation obstruction is removed, but the actual
conditional line bound and the full mathematical consumer chain are still
open. **Minimality:** no final correction is claimed. Exact isometries add
no mathematical restriction or error; equal dimensions, equal point
families, symmetrizing the state, discarding Z mass, or replacing the point
witness are unnecessary for this increment. Neither dropping `deltaQ` nor
using unrestricted completed collisions becomes valid.

### Lean evidence and operator handoff

The edited-file check uses freshly emitted private artifacts, not shared
cache writes. The structural import closure is `Lines`, `EvalDeficit`,
`SubLineDeficit`, `Claims`, QPBT, and the project root; `Apply` is checked
separately as a semantic consumer of the unchanged witness contract.
All seven files pass, with fresh private artifacts at
`/tmp/issue118-lean-validation/lib`, prefixed inside the `lake env` child
shell. Validation logs have prefix `/tmp/issue118-attempt6-`. Direct proof
debt remains one hole in `Lines` and three in `Apply`. Each of the seventeen
new declarations has axiom set exactly `{propext, Classical.choice,
Quot.sound}`; none depends on a source-theorem hole, `sorryAx`, or native
decision procedures. The source-header audit reports no changed public
source-labelled signatures. The worktree hook-installation check passes.

Paper-gap style and blueprint LaTeX checks pass. The paper-gap note also
compiles to a twelve-page PDF in `/tmp/issue118-attempt6-gap-pdf`.
Blueprint web generation succeeds with exactly the same warning/error
lines as attempt 5 (including the two inherited unresolved subline labels
and missing bibliography entries). All **1,865** generated declaration
references resolve against the fresh private root artifact. Static sync
still reports **231 baseline stale entries** and **15 baseline statements
with header-only proof-status tags**; it is not a clean global sync report.
All seventeen new declarations have explicit auxiliary blueprint links.
No full build, baseline rebuild, shared-cache write, paper-mirror edit,
PR 205 lane edit, independent-review action, publication, merge, or runtime
state edit is performed.

Statement integrity: the paper and public Lean assumptions and conclusions
are unchanged. The new heterogeneous assertion explicitly quantifies a
normalized state, probability law, two projective supplied joint families,
right line POVMs with the second projective, nonnegative errors, the
conditional collision bound, two forward marginal bounds, and joint
consistency. Its conclusion is the same one-sided pasting estimate, with
unchanged error function. The coordinate and answer identities have no
error assumptions. Verdict: proved formalization auxiliaries; not an
adopted correction of the source existence theorem. No definition/game
change requiring an owner decision has been identified.

Unposted operator draft: "#118 attempt 6 proves unequal-dimensional
one-sided pasting, all directed expanded bipartitions, and swapped joint
and evaluated-sandwich identities; the actual conditional application and
quantitative specialization remain open. No correction adopted."
The operator owns any announcement and telemetry entries; none is posted
or edited by this session.

## Attempt 5: the product collision predicate and conditioned operator families

Session `mathfix-118-20260906-05`, baseline
`3f359f9dbfc86ed78f44aa2b45670d2a7783ac09`, attempt **5/10**. The original
budget anchor is September 5, 2026, 19:24 UTC; this session started at
21:55:22 UTC. The cumulative working-time total remains operator-owned
and has not been supplied. This entry continues attempt 4, rather than
resetting the investigation. No corrected public theorem is adopted.

### Mathematical results proved in this attempt

The printed assertion is still `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:882-894`: for the constructed
points there are paired-line POVMs, on either player's expanded space,
consistent on independent source line-point samples in every directed
opposite placement, with additive polynomial error in `epsilon, md/q`
and degree at most `d` on axis lines. The two recorded obstructions remain
the internal arbitrary-point helper's missing dependence on `deltaQ`, and
the collision of `T` with `T+1` at completed value `none` on zero-direction
fibers. Neither is a counterexample to this printed existence assertion.

Let `D` be the unchanged source line-point distribution, write
`sX=(lineX,x)` and `sZ=(lineZ,z)`, and let `E` be the event that the X
direction is nonzero. The proof-only probability law now defined in Lean is

```
nondegenerateLinePastingDist = map (D ⊗ D | E)
  ((sX,sZ) ↦ (((lineX,lineZ),sZ),sX)).
```

The common question is the line pair; the first and second evaluation
questions are the Z and X line-point samples. The latter retain line
descriptors so completed evaluation is a function of its own question.
On the support they agree with the common question. No game or evaluation
definition is changed, and no Z direction is discarded.

The following are kernel-checked results, not hypotheses supplied to a
source theorem:

1. The law is normalized, with retained mass `r>0`.
2. It satisfies **`HasConditionalCollisionBound`**, with `G2=X` and
   parameter `b/q` for degree bound `b`. The proof fixes the common question
   and the whole Z sample, uses their indicator as a nonnegative function
   of the X line, applies the previously proved weighted root bound, and
   averages over Z. Multiplying by `r` removes normalization. A finite-sum
   adapter identifies these fiber averages with the predicate's weights.
3. The actual supplied completed point marginals, reordered as `(Z,X)`,
   have conditioned defects at most
   `(8 * deltaQ + C * (epsilon + sqrt epsilon)) / r`. The two line
   families depend only on the common question. Both errors are retained;
   no marginal identity is assumed.
4. Supplied completed joint self-consistency is at most `deltaQ/r`, in
   the common `(X,Z)` order. The witness is not replaced.
5. Complete POVMs on opposite placements have pointwise defect at most
   one, since the diagonal overlap is nonnegative. Their original and
   conditioned defects therefore satisfy `d <= r*dE + 1/(2q)`.
   This is specialized to the **actual** `combinedLineMeasurement` and
   the supplied completed points. It is not a bound on `dE` itself.

The code adds eleven proved theorems and two proof-only definitions in
`MIPStarRE/QPBT/Combining/Lines.lean`, starting with
`collision_bound_of_fiber_averages`. Each of the thirteen declarations
has axiom set contained in `{propext, Classical.choice, Quot.sound}`.
None uses `sorryAx`, a native decision procedure, an assumed collision
identity, or the unfinished combined-line existence helper.

### Counterexample and boundary audit

The zero-X-direction counterexample cannot enter the conditioned law.
Zero Z directions remain allowed and are already covered by the supplied
marginal errors and the restoration estimate. Inconsistent duplicated line
descriptors have zero mass; the fiber-average proof actually establishes
the collision inequality without needing positivity of that fiber.
For degree zero the root estimate gives zero collisions of distinct
constant polynomials. For `b>=q`, the possibly trivial bound remains valid.
For `q=2` and dimension one, positivity still follows from `r>=3/4`.
These are symbolic consequences of the proofs, not claims of an exhaustive
computational search. The distribution of Z need not be nondegenerate.

### Exact remaining construction obligations

The product/question part of attempt 4's first obligation is discharged.
The genuine conditioned marginal and joint estimates and the actual POVM
restoration inequality are also discharged. The remaining work is:

1. Transport the expanded operator families and state to the bipartite
   presentation for every directed opposite placement. Existing
   `Points/Placement.lean` and `Points/Orthonormalization.lean` identify
   the heterogeneous bipartitions, including the unused EPR pair.
   The current one-sided `exists_pasting_error` is typed on `ι × ι`.
   A proved isometric enlargement or a heterogeneous-carrier version is
   required before calling it on arbitrary player dimensions. Do not add
   equal-dimension, equal-family, or symmetric-strategy hypotheses.
2. Apply pasting with `G1=Z`, `G2=X` to the actual completed point family.
   Transfer the answer permutation, including the self-consistency input
   if using the existing public API, and identify the postprocessed
   sandwich. The source's X-outer orientation is already proved.
   The new conditional marginal theorems alone do not prove this step.
3. Bound the actual conditional defect, then use
   `combinedLineMeasurement_consistency_le_conditioned` without losing
   its factor `r` or its additive `1/(2q)`.
4. Specialize `deltaQ=K*epsilon^(1/8)`, prove additive polynomial
   composition and the large-parameter case, and only then repair the
   internal arbitrary-point helper and adapt the two helpers in `Apply`.
   Their source-facing wrappers and supplied witnesses must remain faithful.

No mathematical definition/game change has been found necessary. These are
unproved construction steps, not a reason to request a new source hypothesis.
Minimality of a final correction and full downstream mathematical sufficiency
are **not** established. The weaker unrestricted collision candidate is
false; discarding Z mass would be unnecessarily stronger for this argument.

### Consumers, integrity, and validation

The source uses and complete blueprint descendant list in attempt 1 below
are unchanged. In particular source uses are 1058--1061, 1118--1132,
1241--1246, 1278--1282, 1423, 1465--1492, 1584, 1627, and 1671. The new
auxiliary node `lem:combined-line-conditioned-product` explicitly states
its restriction and its still-unbounded conditional defect. The source node
`lem:qld-xz-lines` remains unfinished. The separate Chapter 15, 16, and 13
descendants and three prose references are not certified by import checks.

Fresh private-artifact checks pass for `Lines`, `EvalDeficit`,
`SubLineDeficit`, `Claims`, `Apply`, `MIPStarRE/QPBT`, and the project root.
The first edited-file check and all consumer checks use the private library
`/tmp/issue118-lean-validation/lib` before the dependency paths obtained by
`lake env printenv LEAN_PATH`. No full build, baseline rebuild, or shared
cache write is performed. Direct proof debt remains one hole in `Lines`
and three in `Apply`; Claims 17-2/17-3 and their proofs are unchanged.
All thirteen new declarations pass the axiom audit. The public source-header
audit reports no changed headers; paper-gap style and blueprint LaTeX checks
pass, and every new declaration has a blueprint reference. Blueprint web
generation succeeds; its warning/error messages are unchanged from attempt 4
(including the baseline unresolved subline labels and bibliography entries).
All **1,848** generated blueprint declaration references resolve with the
fresh private artifacts. The static sync report retains its **231** baseline
stale entries; this is not claimed as a clean whole-repository sync report.
The worktree hook-installation check also passes.

Statement integrity: printed assumptions and conclusion are unchanged in
the public source theorem. The added auxiliary hypotheses are the actual
finite field parameters, distinct degree-bounded polynomials where relevant,
supplied point witness, and opposite placements. The conditioning is internal,
with positive mass proved and discarded mass restored. Verdict: proved
formalization auxiliaries; the unfinished source theorem remains unfinished.

Unposted operator draft: “#118 attempt 5 proves the conditioned product
collision predicate, actual marginals with both errors, and mass restoration
for the XZX POVM; bipartite pasting and quantitative specialization remain
open. No correction adopted.” Main owns the telemetry and any announcement.

## Attempt 4: nondegenerate collisions and restoration of probability mass

Session `mathfix-118-20260906-04`, baseline
`46322dda15c6618ba52e6c9409ad692fe70ae320`. This is attempt **4 of 10**.
The original budget anchor remains September 5, 2026, 19:24 UTC; the session
started at 21:22:32 UTC. Cumulative working time remains operator-owned and
was not supplied separately. This attempt proves distributional components
of the source line construction; it does **not** adopt a corrected public
signature or claim that the combined-line consistency proof is complete.

### Source statement and the precise collision obstruction

The source remains `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`,
using `lem:pasting` at 950--963. Its constructed points admit paired-line
POVMs, consistent on independent line-point samples in every directed
opposite placement, with additive polynomial error in `epsilon,md/q` and
axis-degree support. The paper does not quantify over an arbitrary supplied
point witness while dropping its error `t = deltaQ`; the old internal helper
still does, and remains unproved.

On a zero-direction coefficient presentation, the distinct polynomials
`T` and `T + 1` both have completed evaluation `none`. For `1 <= md < q`
their conditional collision probability one exceeds `md/q`. This is the
same obstruction as attempt 3, not a new counterexample to the source
existence theorem. The source line sampler, coefficient answers, evaluation
convention, strategy, and supplied point witness are all unchanged.

### Nineteen proved declarations

The new declarations are in `MIPStarRE/QPBT/Combining/Lines.lean`.

1. `evalOpt_affine_parameter_of_direction_ne_zero` identifies completed
   evaluation with ordinary polynomial evaluation on a nonzero direction.
2. `polynomial_ofFn_eval_eq_evalCoefficient` connects coefficient tuples
   to the evaluation of Mathlib's `Polynomial.ofFn`.
3. `evalCoefficient_collision_card_le` proves the root-count bound for
   distinct coefficient tuples, with no assumption that the degree is less
   than the field size.
4. `evalOpt_uniform_parameter_collision_le` proves the collision ratio
   `bound / card(field)` on a uniform parameter of a nondegenerate line.
5. `avgOver_restrict_mul_mass` identifies a conditional average times its
   mass with the original unnormalized restricted sum.
6. `avgOver_le_restrict_add_discarded_mass` restores the original average
   with the discarded mass explicitly added, for a function bounded by one.
7. `dLinePointDist_zero_direction_mass_le` bounds diagonal degeneracy by
   `1/q`: the last raw direction coordinate must be zero and is uniform.
8. `aLinePointDist_zero_direction_mass` proves zero axis degeneracy.
9. `linePointDist_zero_direction_mass_le` gives the source mixture's
   degeneracy bound `1/(2q)`.
10. `avgOver_lineRepMap_resample_parameter` preserves jointly the canonical
    representative and point when resampling a uniform affine parameter.
11. `avgOver_aLinePointDist_resample_parameter` proves the exact axis-law
    resampling identity.
12. `avgOver_dLinePointDist_resample_parameter` proves the exact diagonal
    identity, including zero directions.
13. `avgOver_linePointDist_resample_parameter` proves the mixture identity.
14. `linePointDist_nondegenerate_weighted_collision_le` proves the collision
    bound with any nonnegative line-dependent weight, restricted to nonzero
    directions. It derives, rather than assumes, the conditional point law.
15. `linePointDist_nondegenerate_fiber_collision_le` specializes the weight
    to any nondegenerate line fiber. Dividing by its positive mass gives
    its conditional collision probability bound.
16. `linePointDist_nondegenerate_mass_ge` proves retained mass at least
    `3/4`, using only that a field has at least two elements.
17. `prod_linePointDist_zero_X_direction_mass_le` bounds the discarded
    mass by `1/(2q)` when only zero X directions are excluded in the
    independent product law.
18. `avgOver_restrict_le_div_mass` bounds inflation of a nonnegative
    average by the inverse retained mass.
19. `ProjectiveSetting.combinedLineMeasurement_effect_eq_pastedMeasurement`
    identifies the **existing** X-outer sandwich with one-sided pasting at
    `G1 = Z`, `G2 = X`, exchanging the polynomial answer coordinates.

The resampling argument uses the already proved uniformity of
`lineRepMap direction point + parameter * direction`, but preserves the
representative as well as the point. In particular it does not infer a
conditional law merely from a uniform point marginal. Independent raw
point and seed-direction blocks yield the source axis and diagonal laws.
On a nonzero direction the parameter is unique, and the difference of two
distinct degree-bounded polynomials has at most that many roots. The
coefficient-to-polynomial map is injective, so equality of evaluations on
too many parameters cannot hide distinct coefficient answers.

The discarded-mass calculation uses the **last** direction coordinate,
which survives every prefix projection, regardless of the seed. Thus no
false independence of a seed-selected coordinate is assumed. The argument
also avoids discarding degenerate Z directions: only X supplies the
collision-bounded second family for the actual X-Z-X sandwich.

### Edge cases, correctness, and the quantitative calculation

The zero-direction counterexample is outside the nondegenerate collision
claim, but is still inside the original game; its probability is retained
explicitly. Degree zero gives a zero collision bound for distinct constants.
When the degree is at least `q`, the root-count bound is valid but may be
trivial. At `m = 1`, the last coordinate exists, and at `q = 2` the retained
mass lower bound is still `3/4`. Indeed `m = 1, q = 2` attains the worst
mixture mass `1/4`. No division by a strategy or point error occurs.
These are mathematical boundary checks, not numerical evidence in place
of proof; the Lean lemmas quantify over all their stated parameters.

The already proved marginal estimate is
`u = 8t + C(epsilon + sqrt(epsilon))`. If `r` is the mass of nondegenerate
X lines, conditioning yields `u/r` and joint self-consistency `t/r`.
The latter is bounded by `u/r` for nonnegative `t`. Once the question and
register transports are completed, one-sided pasting and restoration give
the proposed estimate

\[
 rD_0\bigl((md/q)^{1/4}+(u/r)^{1/8}\bigr)+(1-r)
 \le D_0\bigl((md/q)^{1/4}+u^{1/8}\bigr)+1/(2q).
\]

The factors of `r` cannot be silently omitted before this calculation:
the second term is `r^(7/8) * u^(1/8)`, at most `u^(1/8)` since `r <= 1`.
For constructed points `t = K * epsilon^(1/8)`, on the unit square the
bound becomes a constant times `(md/q)^(1/4) + epsilon^(1/64)`, since
`u <= (8K + 2C) * epsilon^(1/8)` and `1/(2q) <= (md/q)/2`.
Outside the unit square normalized POVM consistency is bounded by one.
This explains a source-valid route to additive polynomial composition; it
is **not** a Lean proof of the missing operator application or an adopted
error function.

### Exact remaining obligations and consumer boundary

1. Form the normalized restriction of the **product** source law to nonzero
   X directions, and reindex questions into the one-sided pasting
   presentation. Derive `HasConditionalCollisionBound` from the proved
   single-line fiber estimate and independence of the Z sample. The
   single-line theorem is not yet a term of that product-law predicate.
2. Reindex both completed marginal defects, completed joint measurement,
   and expanded state into the bipartite presentation, for every directed
   opposite placement. Use the exact restricted-average identity to retain
   `u/r` and `t/r`. No new marginal or state hypothesis may be introduced.
3. Apply the existing `exists_pasting_error` with `G2 = X`. Exchange the
   answer coordinates and identify the postprocessed output with
   `combinedLineMeasurement`; the new effect identity proves only its
   algebraic orientation, not its consistency. Restore the discarded mass
   using the actual unit bound for these POVMs.
4. Only then replace the internal helper's unsupported error independence
   by its proved quantitative dependence on `t`; specialize to the
   constructed point error and formalize additive polynomial composition.
   Preserve the public source existence statement and supplied witnesses.
5. Adapt the two arbitrary-point helpers and their source-facing consumers
   in `Apply.lean`, retaining the established extended-line error and all
   separate source-game transport obligations. Claims 17-2/17-3 stay intact.

The complete source and blueprint consumer inventory in attempt 1 below
still applies, including all Chapter 15, 16, and 13 descendants and the
three prose-only references. The direct paper uses remain 1058--1061,
1118--1132, and 1241--1246; subsequent global-pair and extraction uses are
1278--1282, 1423, 1465--1492, 1584, 1627, and 1671. Their mathematical
sufficiency is not certified by this partial construction. The new
blueprint node `lem:combined-line-nondegenerate-collisions` displays the
nondegeneracy restriction and mass restoration explicitly. The source node
`lem:qld-xz-lines` remains `notready`.

Minimality of a final correction is not established. The false uniform
collision claim is rejected. Restricting only the proof distribution,
rather than the source theorem or game, avoids an unnecessary public
hypothesis. Excluding both directions would discard more than the
one-sided collision argument needs. Dropping `t`, replacing the point
witness, or assuming the product collision predicate is still impermissible.

Statement audit: the printed theorem assumes the source-constructed points
and concludes paired-line consistency and axis-degree support. The source
Lean statement, witness fields, strategy, and game are unchanged. The new
auxiliary lemmas instead assume finite field parameters, distinct bounded
coefficient tuples, and explicitly nondegenerate lines where needed;
the restriction lemmas state their positivity and unit-bound hypotheses.
Their conclusions are the precise collision, resampling, and probability
estimates above. Verdict: faithful auxiliary facts with explicit proof-only
restrictions; the source construction and its sufficiency remain incomplete.

### Validation and operator record

All **19** new declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`, not `sorryAx`. The changed `Lines` file compiles with a
fresh private artifact, followed by `EvalDeficit`, `SubLineDeficit`,
`Claims`, `Apply`, QPBT, and the project root. The first downstream command
used incorrect `Combining/Lines/` paths; it did not validate anything and
was replaced by the successful run using the actual `Combining/` paths.
Only the existing one `Lines` hole and three `Apply` holes remain.

All **1,835** blueprint declarations resolve. Blueprint web generation
succeeds with the inherited unresolved-label and bibliography warnings.
The synchronization report retains the **231 baseline stale entries**;
no unrelated list entries are removed. The LaTeX convention, changed
paper-gap style, and statement-origin checks pass, as does hook
installation verification. Logs and the axiom-check source are
`/tmp/issue118-attempt4-*`; all Lean checks prefix the private artifact
directory inside the `lake env` child shell. No full build, whole-baseline
rebuild, shared-cache write, other-worktree edit, subagent, push, post,
review, or merge occurs.

At September 5, 2026, 21:49 UTC, approximately 27 minutes of this session
and 145 minutes wall time from the original anchor have elapsed; these are
not measurements of cumulative working time. The attempt limit is not
reached. No source/game change is shown necessary, so no owner decision is
requested. Main retains responsibility for telemetry and adoption records.

Unposted #27 draft: **Attempt 4 proves nondegenerate conditional line
collisions, exact parameter resampling, and restoration of discarded mass;
product/register pasting and quantitative specialization remain open.
No correction adopted.** No adopted-correction event or design decision
is appropriate yet. Commit evidence is recorded in the session's final
report, not by modifying runtime state.

---

## Attempt 3: completed marginals on the product line-point law

Session `mathfix-118-20260906-03`, on baseline
`a571fe01c1dd9d35f834ebcfba78fe9ade87c69f`. The cumulative count is **3 of
10**; the original budget anchor remains September 5, 2026, 19:24 UTC.
Cumulative working time is operator-owned and was not supplied separately.
This attempt continues the construction rather than adopting a speculative
signature for the arbitrary-point helper.

### Mathematical result

Write `t = deltaQ` for the supplied point error. There is a universal
constant `C >= 1`, preceding all parameters, strategies, point witnesses,
and directed opposite placements, such that both completed point marginals
have squared distance and consistency defect at most

\[
  8t+C(\varepsilon+\sqrt{\varepsilon})
\]

from the corresponding evaluated expanded line measurement, on the product
of two line-point laws. The completed joint self-consistency defect is at
most `t`. These are the actual marginal measurements of the supplied joint
measurement after the relabeling `(a,b) -> (some a,some b)`, not measurements
assumed equal to its marginals. The relations are proved for every directed
opposite placement, with no identification of the players' local spaces.

The proof uses `lem:alnf` and `lem:dlnf` to obtain uniform point marginals of
the mixed line-point law. Independent sampling then gives the uniform point
pair law. Fiber sums identify the two postprocessings, and composition of
postprocessings proves that completion commutes with taking either marginal.
The added answers have zero effect, so completing one or both answer
coordinates preserves squared distance exactly. These identities transport
the existing `4t` estimates without changing their constants.

Let `Cp` and `Cl` be the universal constants in `expPoint_self_cons` and
`expLine_point_cons'`. The latter compares a line on the second placement
with a point on the first placement at squared distance `Cl * sqrt(epsilon)`.
The former compares that point with the point on the second placement at
distance `Cp * epsilon`. The squared triangle inequality therefore gives
the same-placement line--point bound
`2 * (Cp + Cl) * (epsilon + sqrt(epsilon))`. A second squared triangle
inequality with the transported `4t` marginal bound gives the displayed
bound, with `C = 4 * (Cp + Cl)`. Projectivity of all relevant
postprocessings, followed by `fact:agreement`, bounds each consistency
defect by its squared distance. The joint self-consistency estimate is
transported and completed in the same way.

The proof is valid at zero strategy error and retains the `8t` term. At
`t = 0`, it retains the strategy-error contribution. No division by either
error, small-error assumption, or replacement point witness occurs. Large
errors cause no exception: the upper bounds remain valid, though not sharp.
This proves sufficiency of these intermediate constants, not optimality.

### Conditional collision obstruction and remaining construction

The printed paired-line assertion is `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:882-894`: its constructed points
admit consistent paired-line POVMs with error polynomial in `epsilon,md/q`
and the stated axis-degree support. Its proof invokes `lem:pasting` at
lines 950--963. The pasting lemma requires a collision estimate **on every
positive-mass conditional fiber**, not merely an unconditional estimate.
The old helper's omission of the arbitrary supplied `t` remains an
unsupported strengthening; no counterexample to the printed existence
theorem is asserted.

There is an additional obstruction to applying the collision predicate
directly to the unchanged completed evaluation law. The diagonal CL map
allows a zero projected direction (source `def:line-point-dist`,
`08_classical_and_quantum_low_degree_tests.tex:276-287`; Lean
`Test/LowDegreeGame.lean`, `ldDLineCL`, and `Observables/LineDefs.lean`).
For such a line, every parameter represents its base point. The distinct
coefficient polynomials `T` and `T + 1`, when `md >= 1`, are nonconstant
functions of the parameter. Neither has a value in the universal-parameter
sense of `EvaluatesTo`; both completed evaluations are `none`. Their
collision probability on that conditional fiber is therefore one, not
`md/q` when `md < q`. Zero projected directions have positive sampling
mass, since the raw zero direction has positive uniform mass. This is a
mathematical counterexample to that direct conditional-collision claim,
not a Lean-verified counterexample theorem and not a counterexample to
paired-line consistency. The existing zero-direction completion is
documented in `docs/paper-gaps/qpbt_win-implications-corrections.tex`.

One possible next argument is to restrict the *proof's distribution* to
nonzero directions, establish conditional uniformity and the polynomial
root bound there, and restore the excluded mass using the unit bound for
POVM consistency. This does not change the game, the witness fields, or
the mathematical definition of evaluation. Its normalization factors and
excluded mass have not been proved here. An alternative direct estimate
on degenerate fibers has not been established either. Thus no game change
is shown necessary, and no owner decision authorizing one is requested.

The exact remaining obligations are:

1. Handle the zero-direction fibers without asserting the false direct
   collision predicate; prove the nondegenerate conditional law and the
   collision estimate, together with the needed mass/normalization bounds.
2. Reindex the already proved completed marginal relations into the
   bipartite presentation of one-sided `exists_pasting_error`, retaining
   both errors. For the existing X-outer sandwich, instantiate `G2` with X
   and `G1` with Z, and explicitly exchange the answer coordinates.
3. Apply pasting for all directed opposite placements and identify its
   output with the existing `combinedLineMeasurement`. Do not replace that
   measurement or the supplied points.
4. Only after this proof, correct the internal helper's error dependence,
   specialize to the constructed `K * epsilon^(1/8)` point error, and
   prove the additive polynomial composition including the excluded mass.
5. Adapt both arbitrary-point helpers in `Apply.lean`, retaining its
   source-facing statements and the separate established-error restriction.

### Use analysis and statement integrity

The complete inherited source and blueprint descendant inventory in attempt
1 below still applies. The direct paper uses are restricted averages
(1058--1061), extended-line construction and degree (1118--1132), and
extended-line consistency (1241--1246). Subsequent uses are global pairs
(1278--1282) and the extraction calculations at 1423, 1465--1492, 1584,
1627, and 1671. Their mathematical sufficiency is **not** certified by
these intermediate marginal lemmas.

The two new auxiliary blueprint nodes are
`lem:combined-point-line-sampling` and
`lem:combined-line-marginals-both-errors`. Their statements display the
supplied error and the completed answer alphabet explicitly. They support,
but do not complete, the source-labelled combined-line theorem. Its
`notready` status is preserved. Claims 17-2/17-3 and all `Apply.lean`
statements remain unchanged. The affected Lean import consumers are
`EvalDeficit`, `SubLineDeficit`, `Claims`, QPBT, and the project root;
`Apply` is also a required explicit validation target.

Statement audit: the new lemmas assume only a projective setting, an
existing point witness at its supplied error, and directed opposite
placements. Their conclusions are exactly the completed marginal bounds
stated above, not the source existence theorem. The source assumptions,
conclusion, games, witnesses, and public `exists_combinedLinesWitness`
statement are unchanged. Verdict: faithful auxiliary estimates with
explicit error dependence; no converged correction or minimality claim.

### Validation record

All eighteen new declarations pass the axiom audit with exactly `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx`. The changed
`Lines.lean` type-checks and emits a fresh private artifact. Using it, fresh
checks of `EvalDeficit`, `SubLineDeficit`, `Claims`, `Apply`, QPBT, and the
project root all exit zero. The existing one line-helper hole and three
`Apply` holes remain; there is no new hole or proof bypass. The completed
self-consistency proof uses exact preservation of defect under completion,
avoiding the expensive repeated projective-comparison elaboration tested
earlier in this attempt.

The declaration checker resolves all **1,816** blueprint declarations,
including the eighteen new links. Blueprint web generation succeeds. Its
distinct warning messages are identical to attempt 2, including unresolved
`lem:qld-sublines-restricted-blocks` and `lem:qld-sublines-seed-blocks` and
the existing bibliography warnings. The synchronization check still reports
the **231 baseline stale entries**; no unrelated entries are removed.
The LaTeX convention check passes, and the paper-gap style check has zero
changed note files. The hook installation check passes for this worktree.
Logs and axiom-check source are `/tmp/issue118-attempt3-*`.

Use the private artifacts **before** the worktree artifacts
in `LEAN_PATH`: `lake env` prepends its own paths to an inherited
`LEAN_PATH`, so set the prefix inside its child shell. Initial experiments
with the inherited variable alone are superseded by the explicitly
prefixed checks. No full baseline rebuild, shared-cache write, subagent,
other-worktree edit, push, post, review, or merge is performed.

At September 5, 2026, 21:18 UTC (September 6, 05:18 +0800), this attempt
has used approximately 26 minutes; elapsed wall time since the original
anchor is approximately 114 minutes, not cumulative working time. The
attempt limit has not been reached and no definition/game change has been
shown necessary. The commit identifier is in the final session report.

Draft unposted #27 announcement: **Attempt 3 proves completed point--line
marginals at `8*deltaQ + C*(epsilon + sqrt(epsilon))` and completed joint
self-consistency at `deltaQ`; conditional collisions, pasting, and
specialization remain open. No correction is adopted.** No adopted-result
event or design decision is appropriate; the operator owns telemetry.

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
