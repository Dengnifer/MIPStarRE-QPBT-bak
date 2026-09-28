# Issue 728 LDT Linear Error Bound Audit

## Source and scope

- Final theorem: `references/ldt-paper/test_definition.tex:180-202`,
  `thm:main-formal`.
- Final construction and scalar cascade:
  `references/ldt-paper/inductive_step.tex:68-234`.
- Printed consistency triangle:
  `references/ldt-paper/preliminaries.tex:649-684`,
  `prop:simeq-triangle-inequality`.
- Existing boundary corrections retained unchanged:
  `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and
  `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

This change adds a stronger Lean-only quantitative theorem.  It does not edit
the paper mirrors, the statement of `Test.mainFormal`, or any existing error
definition.

## Baseline first

`Test.main_formal_explicit_baseline` unfolds `mainFormalError` in the existing
theorem.  It has the same strategy, finite-space, field-model, test-passing,
`k >= 400md`, and `k > 0` hypotheses; it returns the same two projective
polynomial measurements and all three consistency conclusions at

`100000 k^2 m^4 (eps^(1/40000) + (d/q)^(1/40000)
  + exp(-k/(2560000m^2)))`.

This declaration and its new standard-axiom audit were typechecked before the
improvement modules were added.

## Complete-measurement triangle

For a complete measurement `A`, define

`u_A = sum_a ev psi (A_a - A_a*A_a)`.

Each summand is nonnegative by `Quantum.sq_le_self`.  Expanding the squared
distance gives the exact identity

`2 qConsDefect(A,B) = qSDD(A,B) + u_A + u_B`.

Combining this identity with `questionSDD_triangle_three`, and discarding only
nonnegative projectivity defects, proves

`C(A,D) <= 3(C(A,B) + C(C,B) + C(C,D))`.

The heterogeneous indexed theorem averages this pointwise inequality over an
arbitrary question distribution.  Every family in its statement is an
`IdxMeas`; no corresponding claim is made for arbitrary submeasurements.

The source construction uses the following checked placements:

| Application | `A` | `C` | `B` | `D` |
| --- | --- | --- | --- | --- |
| First polynomial triangle | `gAEval` | `pointA` | `pointB` | `gBEval` |
| Final Alice triangle | `pointA` | `qAEval` | `gBEval` | `qBEval` |
| Final Bob triangle | `qAEval` | `gAEval` | `qBEval` | `pointB` |

## Literal source errors

Let `I` be the existing main-induction error at `(3eps,3eps,3eps)` and put
`s = 2I`.  The first linear triangle and the existing Schwartz-Zippel step give

`z = 6s + 9eps + md/q`.

The existing projectivization, completion, and repaired line-169 declarations
are reused without changing their statements.  Their literal errors are

`c = 200z^(1/4) + 40z^(1/8) + 2z`,

`eta = z + 10z^(1/8)`, and

`v = 6z + 6c`.

The two point conclusions have error `3(s + eta + v/2)`; evaluated and global
polynomial consistency have error `v/2`.  For `0 <= z <= 1`, both public errors
are at most `2221z^(1/8)`, using `s <= z/6`, `z <= z^(1/8)`, and
`z^(1/4) <= z^(1/8)`.

## Scalar absorption

The small branch is selected by `T < 1`, where

`T = 10000 k^(1/4) m^(1/2)
  (eps^(1/8192) + (d/q)^(1/8192) + exp(-k/(640000m^2)))`.

This branch itself implies `eps <= 1` and `d <= q`: otherwise one envelope
summand is at least one and the prefactor is at least `10000`.  Therefore the
existing `CascadeHypotheses` estimates apply without assuming anything about
the old error.

Writing

`E = eps^(1/1024) + (d/q)^(1/1024) + exp(-k/(80000m^2))`,

the existing induction estimate gives `I <= 10000 k^2m^4 E`, hence

`z <= 120010 k^2m^4 E`.

Three applications of the square-root envelope lemma give
`E^(1/8) <= E_8192,640000`.  The exact numerical certificates
`120010 <= (9/2)^8` and `2221*(9/2) <= 10000` then imply
`2221z^(1/8) <= T`.  The proof derives `z <= 1` from `T < 1`; it does not use
the old theorem's small-error branch.

For `T >= 1`, normalized bipartite consistency defects are at most one, so
arbitrary projective polynomial measurements prove all three conclusions at
`min(1,T) = 1`.  This retains the `d = 0` and `k > q` cases.

## Before and after

Baseline:

`100000 k^2m^4
  (eps^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000m^2)))`.

Improved:

`min(1, 10000 k^(1/4)m^(1/2)
  (eps^(1/8192) + (d/q)^(1/8192) + exp(-k/(640000m^2))))`.

On `eps >= 0` and `k > 0`, the improved capped error is at most
`min(1, mainFormalError)`.  If `mainFormalError < 1`, the scalar proof gives
`10T <= mainFormalError`; since the exponential summand makes `T > 0`, the
improvement is strict.

## Statement-integrity audit

### Existing source theorem `Test.mainFormal`

- Paper assumptions: a projective strategy passes the LDT with failure at most
  `eps`; the paper prints `k >= md`.
- Existing Lean assumptions: the same mathematical data, finite/decidable and
  field-model boundary instances, plus the documented corrections
  `k >= 400md` and `k > 0`.
- Paper conclusion: two projective polynomial measurements satisfying the two
  point-evaluation consistencies and global polynomial consistency.
- Existing Lean conclusion: the same three conclusions.
- Verdict: unchanged by issue #728; faithful boundary hypotheses with the two
  pre-existing documented source corrections.

### Explicit baseline

- Lean assumptions and conclusions: exactly those of the existing corrected
  `mainFormal` theorem.
- Change: only unfolds the named old error.
- Verdict: exact explicit sibling of the existing corrected theorem; Lean-only
  blueprint entry, not a replacement source label.

### Linear-triangle headline

- Lean assumptions: exactly those of the existing corrected `mainFormal`.
- Lean conclusion: the same witness types and the same three consistency
  relations, all at `min(1,T)`.
- Extra assumptions or bridge inputs: none.
- Verdict: stronger Lean-only quantitative theorem.  It is not advertised as
  the paper's printed bound and does not alter the source-labelled node.

### Complete-measurement triangle

- Domain: four complete measurement families on the two tensor factors.
- Conclusion: linear error `3(eps + delta + gamma)`.
- Verdict: proved auxiliary sharpening with its completeness restriction
  explicit.  It is not generalized to submeasurements.

## Validation evidence

- Baseline focused check:
  `lake env lean MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`.
- Baseline audit check after rebuilding its object:
  `lake build MIPStarRE.LDT.Test.MainTheorem.MainFormal` followed by
  `lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean`.
- Focused checks for the triangle, source construction, scalar module, and
  improved headline all exited zero.
- `lake build MIPStarRE.LDT.Test.MainTheorem.LinearTriangle.MainFormal`: passed.
- `lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean`: passed with the new audit
  entries.
- `lake build MIPStarRE`: passed; downstream aggregate imports rebuilt.
- `lake exe checkdecls blueprint/lean_decls`: all 1925 declarations resolved.
- `leanblueprint web`: passed; only the checkout's pre-existing missing-BBL
  bibliography warnings were emitted.
- Changed Lean files contain no `sorry`, `admit`, `axiom`, prohibited kernel
  bypass, or unsafe cast match.
- `git diff --check`: passed.
- An optional repository-wide `python3 -m unittest discover -s scripts/tests`
  run emitted two error markers and did not terminate after an extended wait;
  it was interrupted.  It is not part of the Lean validation ladder for this
  change.  Canonical PR CI remains for the integration coordinator.

The sandbox exposes this linked worktree's Git metadata read-only.  The
attempted baseline checkpoint commit failed while creating the worktree
`index.lock`; no commit could be created in this session.  The implementation
and validation artifacts remain in the worktree for the integration
coordinator to commit and run through canonical PR CI and independent review.

## 2026-09-29 exact-head review repair

The adopted review findings for PR #731 were resolved without changing any
theorem hypothesis, conclusion, error function, or numerical constant.

- F1: the newly introduced theorem names now follow snake case.  Camel-case
  substrings remain only where they are the exact names of definitions such as
  `mainFormalLinearTriangleError`, `qConsDefect`, or `stepEnvelope`.
- F2: the blueprint now states the indexed triangle for finitely supported
  nonnegative weights, without a normalization hypothesis; finitely supported
  probability distributions are identified as a special case.
- F3: the quantitative proof first assumes `T < 1`, derives `eps <= 1` and
  `d <= q`, proves `2221 * z^(1/8) <= T < 1`, derives `z <= 1`, and only then
  applies the orthogonalization and completion estimates.
- F4: all 23 declarations added by issue #728 now have blueprint links.  The
  auxiliary nodes state the projectivity defect, its decomposition identity,
  the pointwise triangles, both error functions, both measurement
  constructions, the branch theorems, and the scalar estimates.
- F5: statement dependencies now record only the objects needed to state each
  result, while proof dependencies record the construction, scalar estimate,
  and branch theorems actually used.
- F6: the explicit-baseline proof is expressed as a mathematical specialization
  of the displayed value in `thm:main-formal`.
- F7: current prose uses orthogonalization, completion to projective
  measurements, the consistency estimate after completion, and uncapped error.
  These terms supersede the process-shaped wording in the earlier audit entry.
- F8: the complete-measurement linear triangle is an alternative bound, not a
  uniform improvement over the paper's mixed bound
  `eps + 2 * sqrt (delta + gamma)`.  Both require complete measurements.  The
  proved strict comparison applies to the final capped quantitative error when
  `mainFormalError < 1`.

Focused validation after the repair:

- `lake env lean` passed for the complete-measurement triangle, the role-register
  construction, the scalar estimates, the final linear-triangle theorem, and
  `MIPStarRE/LDT/Test/AxiomAudit.lean`.
- Focused `lake build` targets for the three renamed dependencies and the final
  linear-triangle module passed.  A full unlocked build was not run; the
  integration coordinator retains exact-head CI ownership.
- `leanblueprint web` passed.
- `python3 scripts/blueprint_lean_sync.py --root . --ci` passed; the remaining
  orphan and missing-proof warnings are in unchanged QPBT chapters.
- `python3 scripts/blueprint_leanok_axioms.py --ci` checked 1932 declarations
  with zero failures and no proof-level `sorryAx` dependency.
- `lake exe checkdecls blueprint/lean_decls` resolved all 2197 generated
  declaration entries.
- `git diff --check`, the hook installation check, the changed-file proof-hole
  scan, and the added-token proof-integrity scan passed.

The remaining new theorem stem was subsequently corrected to
`cascade_hypotheses_of_mainFormalLinearTriangleRawError_lt_one`, with its two
Lean occurrences and blueprint link updated. Its focused Lean check and module
build passed. After the web build regenerated the declaration inventory, the
inventory was regenerated from the active blueprint references and the global
synchronization check passed. The four orphan tags and two missing proof-level
tags reported by that check are in unchanged QPBT chapters.
