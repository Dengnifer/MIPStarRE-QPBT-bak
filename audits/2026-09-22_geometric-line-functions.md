# Polynomial Functions on Geometric Lines

Issue #698 starts at `23207298a8dfecd1026038c1a0d4a6a3362d5828`, retaining
all five declarations of #695. Main authorized a separate function carrier
and its algebraic comparison with coefficient answers. The assignment does
not authorize a change of games, strategies, sampling laws, answer carriers
of existing measurements, probabilities, or completion criteria.

## Source and Representation

The source is `eq:combine-lines` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The line definition at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`
includes zero directions. The polynomial convention at
`references/qpbt-paper/04_preliminaries.tex:835-845` identifies polynomials
with functions; the coefficient answer format at
`08_classical_and_quantum_low_degree_tests.tex:337-391` must be compared
separately with this convention.

For a field `K`, write `ell(u,v) = {u + tv : t in K}`. The new carrier
`LinePolynomialFunction u v c` is the subtype of functions from this point
set to `K` whose pullback along `t |-> u + tv` has a polynomial
representative of degree at most `c`. This is an existential property of a
function, not a chosen representative or a hypothesis concerning the
combining operation. Equality is equality of functions. The carrier is
finite over a finite field by the standard finite function and subtype
instances, so it can serve as a measurement outcome type in a separately
authorized comparison.

The theorem `exists_reduced_representative` makes the connection to the
source's reduced convention explicit. Taking the remainder of a pullback
representative modulo `T^q-T` preserves its values, does not increase its
degree, and gives degree less than `q`. The proof uses Mathlib's polynomial
division and finite-field identities. Thus allowing arbitrary bounded
representatives in the existential property does not enlarge the class of
functions relative to bounded reduced representatives.

The combining function evaluates `alpha f(x) + beta g(z)` at each geometric
point. To prove its pullback bound, #695 constructs affine parameters from
the projection inclusions. Bounded representatives of the input functions
are converted with Mathlib's `Polynomial.toFn` and `Polynomial.ofFn`.
The existing `combineLinePolynomial` and
`combineLinePolynomial_natDegree_le` supply the polynomial and its bound.
No coordinate is divided by a direction component. Thus the argument also
applies when the extended line is a singleton, either containing line is a
singleton, or either projection is constant.

The predecessor obstruction is retained: `T` has no value on a singleton
under `EvaluatesTo`. Conversely, the nonzero formal polynomial `T^q-T`
induces the zero function over a field of size `q`, on every parameter
fiber. Constancy of the induced function, rather than formal degree zero,
is the correct singleton condition. These facts do not contradict the
source combining formula for actual functions.

## Statement Integrity

| Item | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
| --- | --- | --- | --- | --- | --- |
| Line function domain | A geometric line, possibly a singleton, and a degree bound `c = md`. | A field, vectors `u,v`, and `c : Nat`; a function on `linePoints u v` with an existential degree-`c` polynomial pullback. | A polynomial function on the line. | The function itself, with proof of its bounded pullback; no formal representative is stored in the outcome. | Exact on the source finite field; arbitrary fields and bounds are also supported. |
| Line combining map | Every extended-line point projects into the two containing lines; two degree-`md` functions on those lines. | Exactly those projection inclusions and two `LinePolynomialFunction` inputs of bound `c`. | A degree-`md+1` function satisfying the affine-weighted pointwise identity. | `combineLineFunction` has bound `c+1`; `combineLineFunction_apply` is the identity at every geometric point. | Exact after `c = md`; no descent, compatibility, or nonzero-direction premise is added. |
| Choice comparison | The formula must define a function independently of parameter descriptions. | Any compatible affine parameters and any bounded coefficient representatives of the fixed input functions. | The same combining function. | `combineLineFunction_pullback` identifies every such coefficient construction pointwise with the source function. | Exact algebraic independence; the representative premises belong only to the comparison lemma. |
| Line presentation | A function is defined on the geometric point set. | Inclusion of two line point sets and a degree-`c` function on the containing line. | Restriction preserves the degree bound, hence equal presentations have the same bounded functions. | `restrictToLine` constructs the restriction by affine composition; `restrictToLine_apply` preserves its pointwise values. | Exact; no nonzero direction is needed. |
| Reduced convention | Polynomial functions over `F_q` have reduced representatives. | A finite field and a degree-`c` geometric polynomial function. | A representative of degree less than `q` without increasing the bound. | `exists_reduced_representative` supplies both bounds and every pullback evaluation. | Exact; no bound such as `c < q` is imposed. |
| Coefficient comparison | Separate from the source function construction. | A coefficient list whose evaluation factors through the line parameterization, expressed by Mathlib's `Function.FactorsThrough`. | A function with the original parameter values, when descent holds. | `ofCoefficients` and `ofCoefficients_apply` construct it; `ofCoefficients_eq_iff` uses equality of parameter functions; `ofCoefficients_evaluatesTo_iff` agrees with the existing universal evaluation relation. | Explicitly restricted algebraic adapter, not an added source hypothesis. |
| Coefficient combination | Separate representation comparison. | Two descending coefficient lists and any compatible affine parameters under the projection inclusions. | Their coefficient combination descends to the source combining function. | `combineLinePoly_descends` constructs the output fiber condition and proves equality of geometric functions. | Exact on the stated adapter domain; no arbitrary coefficient outcome is identified with a function. |
| Degenerate directions | Singleton lines are permitted. | An arbitrary coefficient list and line vectors. | Descent on a singleton requires constant parameter evaluation; nonzero directions have unique parameters. | `coefficients_factorsThrough_iff` proves exactly the disjunction of nonzero direction and constant parameter function. | Exact characterization, over any field. |
| Global combining map | Individual degree at most `d`, with the standing positive degree. | The unchanged `combinePoly`, `combinePoly_eval`, and `combinePoly_mem_polyFunc`, the last with `1 <= d`. | The global affine-weighted polynomial, preserving individual degree. | The existing construction and degree proof are reused. | Faithful boundary hypotheses, unchanged by this assignment. |

The source construction is not a conditional coefficient helper. Polynomial
representatives and affine parameters occur only inside its degree proof.
The comparison lemmas explicitly concern different representations of its
already-defined function. No previous public declaration is restated.

## Consumer Inventory

All paths in this table are relative to `MIPStarRE/QPBT/`.

| Consumer | What remains necessary before measurement or game transport |
| --- | --- |
| `Algebra/Coefficients.lean`, `Observables/LineDefs.lean` | Compare coefficient equality with equality of induced functions and preserve the universal meaning of `EvaluatesTo` and `evalOpt`. |
| `Test/LowDegreeGame.lean`, `Test/PauliBasisTest.lean` | Compare answer equality and line-point acceptance; replacing coefficients by functions can identify different answers. |
| `Observables/LineMeasurement/Expanded.lean`, `Evaluation.lean` | Account for every coefficient outcome, including non-descending answers and undefined evaluation mass. |
| `Combining/Lines/SubLineExtended.lean`, `SubLineConstruct.lean` | Their affine compatibility geometry remains valid, including zero directions. No sampling-law comparison follows from the new function carrier. |
| `Combining/Witnesses.lean` | Stored incidence and compatibility are preserved. Removing redundant fields is separate work. |
| `Combining/ExtendedLines/Measurement.lean` | Compare `affineData`, `combinedPolynomial`, `extendedMeasurement`, axis degree support, and optional evaluation formulas with function-valued postprocessing. |
| `Combining/DirectLowDegree/Game.lean`, `ExtendedLineGame/ParameterCompletion.lean` | Compare `DirectDegPoly`, `DirectEvaluatesTo`, `directEvalOpt`, parameter evaluation, and completed evaluation without omitting undefined mass. |
| `Combining/ExtendedLines/Overlap.lean`, `Estimates.lean`, `Apply.lean` | Transport overlap and consistency from completed evaluations to the field-valued assertions before claiming the source `lem:qld-4-13` or its use in `lem:qld-4-7`. |

The blueprint dependencies include `lem:qld-comm-line-cons`,
`lem:qld-xz-lines`, the combined line construction in `lem:qld-4-13`
(paper lines 1128-1132), and its use in `lem:qld-4-7`. None of these
measurement assertions is established merely by constructing the source
combining function. The global combining polynomial, the separated-image
results, and `lem:qld-4-12` are preserved. The source-law, dimension,
completed-to-field transport, and printed-rate obligations remain separate;
their source entries receive no new marks.

## Prior Costs and Authority

This is one additional 3600-second assignment, beginning at
`2026-09-22T21:05:58+09:00`, with no automatic continuation or
self-extension. The original #118 anchor remains
`2026-09-05T19:24:00Z`, with the historical ten-attempt, 19931-second
baseline. The thirteen canonical #118 rows total 26509 seconds and overlap
that baseline; they must not be added to it.

The reconciled history in
`audits/2026-09-22_combining-map-source-domain.md` is retained in full,
including #117/#118/#119, Fable and interrupted records, #414, #474, #480,
#512, and the overlapping 14637-second subtotal recorded by #515. The #689
proof and integration records remain separate costs of 1684 and 1071
seconds. The completed #695 assignment remains charged as recorded by its
dispatcher and receipt. Missing durations remain unknown, not zero. No
historical attempt, cost, or review record is reset or counted twice.

Main retains publication, full CI, and independent review of both the
representation and implementation. This audit makes no approval claim.

## Validation and Remaining Boundaries

Every proof milestone passed `lake env lean` and was committed with the
normal hooks before the next lemma. The final new module has no diagnostic,
proof hole, axiom declaration, forbidden proof-integrity token, debugging
command, or line exceeding 100 characters. The umbrella import is the only
change to an existing Lean file. No predecessor declaration or proof changes.

Focused checks pass for `Combining/LinePolynomial.lean`,
`Combining/GeometricLineFunctions.lean`,
`Combining/Lines/SubLineConstruct.lean`,
`Combining/ExtendedLines/Measurement.lean`, `MIPStarRE/QPBT.lean`, and
`MIPStarRE.lean`. Single-file Lean invocations generated worktree-local
objects for the predecessor module, new module, and umbrellas. No shared
build cache was written and no full `lake build` was run.

The scratch harness
`~/.cache/mipstarre-dev/prover-698-CheckGeometricLineFunctions.lean`
checks all fourteen proof-bearing declarations' axiom closures: only
`propext`, `Classical.choice`, and `Quot.sound` occur. It also checks:

- the finite outcome instance;
- an actual singleton `LineDesc` with the predecessor `T` obstruction;
- the nonzero formal polynomial `T^q-T` descending to the zero function on
  every geometric line, including singletons;
- a singleton extended line with singleton containing lines;
- a nonzero extended direction in dimension four with two zero projections
  into dimension one, whose combined function is the parameter itself;
- arbitrary coefficient descent on a nonzero-direction line;
- restriction in both directions between equal line presentations.

Bibliography generation and `leanblueprint web` pass with no web warnings
or errors. After rendering, the ignored declaration list was regenerated
with `blueprint_lean_sync.py --update-lean-decls`. Strict synchronization
and changed-declaration coverage pass. `lake exe checkdecls
blueprint/lean_decls` resolves all 1896 entries. The four orphan marks and
two missing proof marks in unchanged chapters remain sync warnings. The
LaTeX checker and whitespace check pass. The source-statement checker
finds no changed existing source-labelled public headers.

Declaration claims were recorded with `dup_check.py`. Its short-name matches
for `ext` and `restrictToLine` concern different existing structures and
the restriction of global formal polynomials to coefficient lists. These
overlaps were inspected and the distinct new namespaced claims recorded
with that explanation; no existing declaration was replaced.

The proof-integrity comparison with A1--A6 distinguishes the input type's
bounded-pullback definition from an assumption of the combining conclusion.
The constructor actually proves the output degree bound. Its pointwise
identity is the defining source formula. The restricted adapter uses a
surjective parameterization, with no default parameter or omitted outcome.
Mathlib supplies finite function types, polynomial division, coefficient
conversion, and inverse selection; there is no custom quotient machinery or
new external mathematical premise.

No obligation remains in this algebraic construction. The measurement
comparison for non-descending answers, completed-to-field evaluation,
source-law comparison, and printed error bounds remain open in the consumer
inventory and the existing subline, dimension, and error gap notes.
`def:combine-map` is marked for the source function construction, with its
coefficient helpers attached to separate auxiliary nodes. This grants no
completion exemption and no mark to those remaining source assertions.

The exact commit, check, and budget receipt is
`/tmp/main-fullspeed-geometric-lines-20260922-result.md`; the prepared PR body
is `/tmp/main-geometric-lines-pr-body-20260922.md`.
