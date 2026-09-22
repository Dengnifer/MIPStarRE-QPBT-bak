# QPBT blueprint exemptions

No permanent exemption is granted by the source-adoption audit of issue #667
at source snapshot `e947a49e14080b46642be21ce551d911032a05f4`.
The table intentionally has no data rows.

| Blueprint label | Reason |
|---|---|

The following are unresolved matches, not exemptions. Their continued absence
of a formalization mark must keep C4 failing. Construction targets and the
row-by-row adoption evidence are in the
[gap register](../paper-gaps/qpbt-gap-register.md#source-adoption-audit-2026-09-22).

- **`def:canonical-complement`:** `canonicalComplement` uses prefix ranks;
   the source uses the nonpivot columns of reduced row echelon form
   (`04_preliminaries.tex:303-320`). The equality of these presentations and
   the algorithmic assertion are not formalized.
- **`lem:canonical-complement`:** `isCompl_registerSubmodule_canonicalComplement`
   proves complementarity for the prefix-rank definition. The same
   presentation comparison is needed for the source node
   (`04_preliminaries.tex:342-373`). A different proof strategy alone would
   not justify withholding a mark; the remaining issue is the represented object.
- **`lem:qld-xz-lines`:** the complete unconditioned line construction is proved,
   but its witness states consistency on completed evaluations. The source
   uses field-valued evaluations, including its unresolved zero-direction
   convention. See [the subline note](../paper-gaps/qpbt_subline-claims-line-marginal.tex).
- **`lem:qld-4-13`:** `PrintedExtendedLinesWitnessClaim` is unasserted and uses
   the directly indexed carrier and completed evaluations. Its error form is
   not established by the proved `C m poly(epsilon,md/q)` auxiliary. See
   [the error note](../paper-gaps/qpbt_combined-lines-error-term.tex) and
   [the dimension note](../paper-gaps/qpbt_ld-dimension-divisibility.tex).

Issue #698 matches **`def:combine-map`** on its source function domain
(`14_analysis_of_the_pauli_basis_test.tex:970-989`). The new
`LinePolynomialFunction` carrier consists of functions on geometric lines with
bounded polynomial pullbacks. `combineLineFunction` constructs the function
and degree bound from projection inclusion, including singleton lines and
constant projections. The pointwise formula and independence of affine choices
and coefficient representatives are proved. The existing global combining map
is retained. See [the function audit](../../audits/2026-09-22_geometric-line-functions.md).
This is a source construction, not a completion exemption. Its coefficient
adapter applies only to answers that descend on parameter fibers. The existing
coefficient-indexed games and measurements are unchanged, and `T` still has no
value on a singleton under their universal evaluation relation. Transport of
non-descending outcomes, completed-to-field evaluation, the source law, and
the printed error bounds remain open; their entries remain unmarked.

The four CL definition nodes audited in chapter 12 now carry marks for their
faithful recursive predicates and shared-seed sampling laws. No theorem or
definition was weakened to obtain those marks, and no proof-level mark was added.
