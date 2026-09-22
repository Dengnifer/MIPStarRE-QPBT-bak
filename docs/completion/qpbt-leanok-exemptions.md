# QPBT blueprint exemptions

The source-adoption audit of issue #667 granted no permanent exemption
at source snapshot `e947a49e14080b46642be21ce551d911032a05f4`.
The following later exemption records the owner-authorized documentary
disposition of the combined-lines intermediate assertion (2026-09-22,
issue #713). It does not mark that assertion proved.

| Blueprint label | Reason |
|---|---|
| `lem:qld-4-13` | Documented deviation: the source's `poly(m^2 epsilon, md/q)` assertion remains unproved and unrefuted. `PrintedExtendedLinesWitnessClaim` is an unasserted `Prop` in `MIPStarRE/QPBT/Combining/Apply.lean`, using `ExtendedLinesWitness` on directly indexed lines, the direct line-point law, and completed evaluations. The proved `exists_extendedLinesWitness_established` instead constructs a polynomially controlled point family and line POVMs with error `C m poly(epsilon, md/q)`; its separate node `lem:qld-4-13-established` states those replacements and carries the proof marks. The scalar obstruction refutes absorption of the displayed upper bound, not existence of better measurements; the quadratic counterexample concerns only the former unrestricted supplied-point helpers. The proved global-pair construction absorbs the actual auxiliary error without changing its source conclusion. See [the mathematical note](../paper-gaps/qpbt_combined-lines-error-term.tex), [the matching blueprint remark `rem:qld-4-13-source-defects`](../../blueprint/src/chapter/ch15_qpbt_combining.tex), and [DEVIATIONS a1](../DEVIATIONS.md#a1-the-error-form-of-the-combined-lines-lemma). This exemption certifies documentary disclosure only; it does not settle the separate source-law/evaluation or sum/product-convention deviations. |

The following other entries remain unresolved matches, not exemptions. Their
continued absence of a formalization mark must keep C4 failing. Construction
targets and the row-by-row adoption evidence are in the
[gap register](../paper-gaps/qpbt-gap-register.md#source-adoption-audit-2026-09-22).

1. `def:canonical-complement`: `canonicalComplement` uses prefix ranks;
   the source uses the nonpivot columns of reduced row echelon form
   (`04_preliminaries.tex:303-340`). Their equality, basis independence,
   cardinality, independence of the selected vectors, and the register-subspace
   case are proved. The remaining obligation is a deterministic executable
   Gaussian-elimination construction, with correctness and a polynomial bound
   on field operations and zero tests. Abstract RREF existence and an executable
   decomposition given an RREF matrix do not establish that claim. This
   obligation remains open until issue #690 receives CI, independent review,
   and merge. See the
   [canonical-complement audit](../../audits/2026-09-22_issue-676-canonical-completion.md).
2. `lem:qld-xz-lines`: the complete unconditioned line construction is proved,
   but its witness states consistency on completed evaluations. The source
   uses field-valued evaluations, including its unresolved zero-direction
   convention. See [the subline note](../paper-gaps/qpbt_subline-claims-line-marginal.tex).
3. `def:combine-map`: global polynomial combination and the coefficient formula
   are proved. Issue #695 derives affine compatibility from projection inclusion,
   including constant projections and zero directions, and proves the parameter
   formula and degree bound in `exists_combineLinePoly_of_projection_mem`.
   Field-valued evaluation on the full coefficient carrier is still unavailable:
   `not_evaluatesTo_parameter_on_zero_direction` proves that the answer `T`
   has no value on a singleton line. The source uses functions on lines, so
   carrier correspondence and representative independence remain required
   (`14_analysis_of_the_pauli_basis_test.tex:970-989`). See
   [the focused audit](../../audits/2026-09-22_combining-map-source-domain.md).

`lem:canonical-complement` is now marked at both statement and proof level.
`isCompl_span_rows_canonicalComplement` derives an RREF presentation and its
correspondence with the intrinsic complement from the independent input rows,
then proves the source complement conclusion using the pivot-coordinate
decomposition. No RREF, correspondence, or complement hypothesis is assumed.
This resolves the former canonical-complement lemma row without exempting the
definition's remaining algorithmic assertion.

`def:generalized-pauli` is marked, and `lem:pauli-observable-expansion` is
marked at both statement and proof level. The general-prime eigenvectors,
projectors, and both Fourier identities are formalized, closing their former
unresolved rows. See
[the scope note](../paper-gaps/qpbt_characteristic-two-pauli-scope.tex).

The four CL definition nodes audited in chapter 12 now carry marks for their
faithful recursive predicates and shared-seed sampling laws. No theorem or
definition was weakened to obtain those marks, and no proof-level mark was added.
