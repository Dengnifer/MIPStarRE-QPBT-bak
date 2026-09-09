# PR 398: third-review repair

This author audit records the bounded repair of the
[third review](https://github.com/Dengnifer/MIPStarRE-A/pull/398#pullrequestreview-5151384716)
at `c9784bc726ddcc9283449bb60746fab98b0d15b5`. It is not an independent review.
The prior commits and all existing proof obligations are preserved.

## Finding dispositions

- **F1:** The combined-lines gap note now identifies the XZX POVM, its
  outcome-exchanged pasting identity, and both axis-degree support properties as
  proved. The conditioned defect, conditioning mass, opposite-placement symmetry,
  and combined-line existence proofs remain open.
- **F2:** `expLine_point_cons_linear` exposes the existing linear estimate with
  a universal constant preceding every parameter, strategy, placement, and basis.
  Chapter 14 links it alongside the unchanged common square-root theorem.
  Neither the source statement nor the stronger sentence in the blueprint was
  weakened. No new assumption or proof obligation was introduced.
- **F3:** `lem:combined-point-distance-support` states the five public results
  in `Combining/Points/Closeness.lean`, with declaration links, both completion
  markers, and an explicit dependency from the combined-point proof. The
  conditional triangle estimates are displayed with all their assumptions and
  are distinguished from the source theorem.
- **F4:** The point module introduction describes the completed construction.
- **F5:** The conditional line theorem is described as a formalization-only
  auxiliary. Its statement and proof obligation are unchanged.
- **F6:** The expanded-line proof describes the alternative mathematical
  argument without referring to its implementation.

These are author dispositions for main to assess against the existing reviews;
no review findings or review statuses were changed by this session.

## Statement integrity

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
Lemma `lem:qld-comm-line-cons` at lines 523--545 and its proof at lines 560--596,
especially `eq:qld-comm-line-pt-cons-eps`.

**Paper assumptions.** An admissible Pauli basis test, a projective strategy
winning with probability at least `1 - eps`, its expanded state and measurements,
and the line-point distribution. The assertion holds in either basis and for
all symmetric equivalents of the opposite register placements.

**Lean assumptions.** `P : AdmissibleParams`, `eps : Real`,
`S : ProjectiveSetting P eps`, and opposite placements `p1`, `p2`, with an
arbitrary `W : PauliKind`. Nonnegativity of `eps` is derived from `S`.
No new boundary condition or load-bearing hypothesis is added.

**Paper conclusion.** The squared distance between an expanded line effect
and that effect followed by its selected opposite point effect is `O(eps)`.
The lemma collects all three consistency conclusions at a common polynomial
error, with the proof choosing `sqrt(eps)`.

**Lean conclusion.** `expLine_point_cons_linear` states this same distance
bound as `C * eps` for one universal `C >= 1`. It includes every directed
opposite-placement pair and the existing completed-evaluation convention for
zero-direction lines. `expLine_point_cons` retains its exact original signature
with `C * deltaLine eps`; `deltaLine`, `ExpandedLineConclusions`, and
`exists_deltaLine` are unchanged.

**Verdict: faithful boundary hypotheses.** Finite coefficient representatives,
canonical lines, and completed evaluation retain the existing formal encoding.
The new theorem exposes the source's linear intermediate estimate, without
altering the common-error conclusion or requiring a consistency hypothesis.

The proof composes the existing projective-refinement and evaluation-class
bounds for each placement with `win_low_degree` and its interchanged version.
If their universal constants are `C1` and `C2`, then `2 * (C1 + C2)` works
uniformly. The original square-root theorem applies the existing scalar bound
to this estimate and the independent distance bound `4`.

The source-facing combined-point and combined-line signatures are unchanged.
The auxiliary support node uses arbitrary POVMs in the triangle calculation,
projective measurements only in the product-square identities, and explicitly
requires `0 <= eps <= 1` and `C0 >= 1` in the scalar estimate. The author check
against anti-patterns A1--A6 found no new displaced obligation, changed object,
default witness, external premise, or duplicate foundational proof.

## Focused validation

- `lake env lean` passed for `Observables/LineMeasurement.lean`,
  `Combining/Points/Closeness.lean`, `Combining/Points.lean`, and
  `Combining/Lines.lean`. Only the seven pre-existing warnings below remain.
- `rg -n "sorry|axiom"` on those files found only the seven existing `sorry`
  sites in `Combining/Lines.lean` (66, 95, 116, 135, 158, 192, 214).
- After recompiling the edited line module, axiom checks passed for the new
  linear theorem, its square-root consequence, `exists_deltaLine`, all five
  support declarations, `exists_combinedPointsWitness`, and the paired-line
  POVM and its two axis-support theorems. Each uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `texra-blueprint bbl` and `leanblueprint web` passed.
- `lake exe checkdecls blueprint/lean_decls` resolved all 1,675 declarations.
- Hook installation/check and `git diff --check` passed.

Publication and canonical CI evidence belong to the resulting commit's GitHub
statuses. No fourth review is dispatched by this repair.

## Unchanged open obligations

All seven sites below are in `MIPStarRE/QPBT/Combining/Lines.lean`.

| Declaration | Discharge target or argument | Existing tracker or note |
| --- | --- | --- |
| `exists_combinedLinesWitness_ofPointsWitness` | Prove `exists_combinedLine_restored_defect_le`, `nondegenerateLinePastingMass_bounds`, and `consistencyDefect_opposite_symm`; use the proved scalar bound | Issue #389; `docs/paper-gaps/qpbt_combined-lines-error-term.tex` |
| `exists_combinedLinesWitness` | Combine the preceding result with `exists_combinedPointsWitness` | Issue #389; same note |
| `linePointDist_eq_mixture_restricted` | Expand restrictions and equal fibers of `chiIndex` | Issue #18 |
| `avg_restricted_le` | Use the mixture identity and nonnegativity | Issue #18 |
| `avg_restricted_prod_le` | Apply `avg_restricted_le` in each coordinate | Issue #18 |
| `restricted_lines_consistency_bound` | Apply `avg_restricted_prod_le` to the witness's consistency estimate | Issue #18 |
| `exists_subLineWitness` | Prove the two sampling cases for `DirectLineDesc` | Issue #18; `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` |

The source combined-lines blueprint entry remains `notready`. The completed
XZX construction does not certify any of these open consistency conclusions.
