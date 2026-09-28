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
