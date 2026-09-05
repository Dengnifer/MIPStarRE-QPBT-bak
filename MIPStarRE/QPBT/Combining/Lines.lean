import MIPStarRE.QPBT.Combining.Lines.ConsistencyPositivity
import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineBind
import MIPStarRE.QPBT.Combining.Lines.SubLineBlocks
import MIPStarRE.QPBT.Combining.Lines.SubLineBranch
import MIPStarRE.QPBT.Combining.Lines.SubLineConstruct
import MIPStarRE.QPBT.Combining.Lines.SubLineExtended
import MIPStarRE.QPBT.Combining.Lines.SubLineMixture
import MIPStarRE.QPBT.Combining.Lines.SubLinePrefix
import MIPStarRE.QPBT.Combining.Lines.SubLineProduct
import MIPStarRE.QPBT.Combining.Lines.SubLineSeed
import MIPStarRE.QPBT.Combining.Lines.SubLineShuffle
import MIPStarRE.QPBT.Combining.Lines.SubLineSource
import MIPStarRE.QPBT.Combining.Lines.SubLineSupport
import MIPStarRE.QPBT.Combining.Lines.SubLineTransport
import MIPStarRE.QPBT.Combining.Lines.SubLineUniform
import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Combining.Witnesses
import MIPStarRE.QPBT.Games.Sandwich

/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

The mixture identity, the two inflation estimates, and their instance for the
evaluated line measurement are proved in the submodules
`Combining.Lines.RestrictedMixture` (the uniform coordinate-index mixture),
`Combining.Lines.RestrictedAverage` (the `2 m` and `4 m ^ 2` inflation
factors), and `Combining.Lines.ConsistencyPositivity` (nonnegativity of the
consistency defect on opposite placements).

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open scoped Matrix MatrixOrder

noncomputable section

/-! ## Combined line measurements -/

/-- Removing the component outside a projective effect is a contraction.
This is the projection step preceding `eq:qqm`, paper
`14_analysis_of_the_pauli_basis_test.tex:902-915`. No commutation of the
two operators being compared is required. -/
theorem norm_sub_projective_mul_sq_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : Quantum.Measurement α ι)
    (hM : Measurement.IsProjective M) (a : α) (A D : Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - M.effect a * A) ψ‖ ^ 2 ≤
      ‖applyOperatorToState (A - M.effect a * D) ψ‖ ^ 2 := by
  have hidem := (hM a).isIdempotentElem.eq
  have hgram : (1 - M.effect a)ᴴ * (1 - M.effect a) ≤ 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (hM a).isSelfAdjoint.isHermitian.eq]
    calc
      (1 - M.effect a) * (1 - M.effect a) = 1 - M.effect a := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]
        abel
      _ ≤ 1 := sub_le_self _ (M.pos a)
  have heq : A - M.effect a * A =
      (1 - M.effect a) * (A - M.effect a * D) := by
    simp only [sub_mul, mul_sub, one_mul, ← mul_assoc, hidem]
    abel
  rw [heq, DistanceCalculus.applyOperatorToState_mul]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (MagicSquareRigidity.norm_applyOperatorToState_le hgram _) 2

/-- Summing a projective refinement close to `B_b D` recovers `D` with
four times the squared-distance error. This is the calculation from
`eq:qqm` to `eq:qld-qxz-close-to-point`, paper lines 912--932. Completeness
is required of `B`, not of the fixed marginal fiber `Q`. -/
theorem norm_marginal_sub_sq_le {β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι] (Q : β → Op ι)
    (hQ : ∀ b, IsProj (Q b))
    (horth : ∀ {b c}, b ≠ c → Q b * Q c = 0)
    (B : Quantum.Measurement β ι) (hB : Measurement.IsProjective B)
    (hcomm : ∀ b, Q b * B.effect b = B.effect b * Q b)
    (D : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((∑ b, Q b) - D) ψ‖ ^ 2 ≤
      4 * ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
  classical
  let U : Op ι := ∑ b, Q b * (Q b - B.effect b * Q b)
  let V : Op ι := ∑ b, B.effect b * (Q b - B.effect b * D)
  have hU : ‖applyOperatorToState U ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
    refine le_trans (DistanceCalculus.norm_finset_sum_projector_mul_sq_le
      Q (fun b => Q b - B.effect b * Q b) hQ horth Finset.univ ψ) ?_
    exact Finset.sum_le_sum fun b _ => norm_sub_projective_mul_sq_le B hB b (Q b) D ψ
  have hV : ‖applyOperatorToState V ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 :=
    DistanceCalculus.norm_finset_sum_projector_mul_sq_le B.effect
      (fun b => Q b - B.effect b * D) hB
      (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero B hB hbc)
      Finset.univ ψ
  have hsum : (∑ b, Q b) - D = U + V := by
    have hfirst : U = ∑ b, (Q b - B.effect b * Q b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_sub, ← mul_assoc, hcomm b, mul_assoc,
        (hQ b).isIdempotentElem.eq]
    have hsecond : V = (∑ b, B.effect b * Q b) - D := by
      dsimp [V]
      simp only [mul_sub, ← mul_assoc, (hB _).isIdempotentElem.eq,
        Finset.sum_sub_distrib, ← Finset.sum_mul, B.sum_eq_one, one_mul]
    rw [hfirst, hsecond, Finset.sum_sub_distrib]
    abel
  rw [hsum]
  have htriangle : ‖applyOperatorToState (U + V) ψ‖ ≤
      ‖applyOperatorToState U ψ‖ + ‖applyOperatorToState V ψ‖ := by
    simpa only [applyOperatorToState, map_add, LinearMap.add_apply] using
      norm_add_le (applyOperatorToState U ψ) (applyOperatorToState V ψ)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖applyOperatorToState U ψ‖ - ‖applyOperatorToState V ψ‖)]

/-- The joint point witness absorbs the opposite X point projector with
error at most its actual parameter. This is the X counterpart of the first
projection step of `lem:qld-xz-lines`, paper lines 902--915, obtained from
`consistent_XZ` rather than from an assumed marginal identity. -/
theorem CombinedPointsWitness.absorb_X_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_XZ p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.1 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2)) S.psiHat

/-- The joint point witness absorbs the opposite Z point projector with
error at most its actual parameter. This is the first projection step in
`lem:qld-xz-lines`, paper lines 902--915, derived from `consistent_ZX`. -/
theorem CombinedPointsWitness.absorb_Z_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2) *
        S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab)) S.psiHat ≤ δQ := by
  refine le_trans ?_ (points.consistent_ZX p1 p2 hopp)
  unfold opFamilyDistSq
  apply avgOver_mono
  intro xz
  apply Finset.sum_le_sum
  intro ab _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul]
    using norm_sub_projective_mul_sq_le
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      ab.2 (S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1)) S.psiHat

set_option maxHeartbeats 800000 in
/-- The X marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite X point measurement. This is
`eq:qld-qxz-close-to-point`, paper lines 917--932, with the supplied witness
error retained; the source later specializes to its constructed points. -/
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hbc (congrArg Prod.snd hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun b => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat

set_option maxHeartbeats 800000 in
/-- The Z marginal of any joint point witness is within squared distance
`4 * δQ` of the opposite Z point measurement. This is the symmetric
calculation `eq:qld-qxz-close-to-point-2`, paper lines 933--935. -/
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  apply avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
    (fun a => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hac => DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hac (congrArg Prod.fst hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun a => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat

/-- Joint self-consistency in the consistency-defect convention required by
`lem:pasting`, retaining the point witness error. This establishes the
uniform-point estimate; transporting it to line-point samples is separate.
Source: `eq:qld-q-self-cons` and paper lines 955--960. -/
theorem CombinedPointsWitness.self_consistency_defect_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    consistencyDefect
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab))
      S.psiHat ≤ δQ := by
  exact le_trans (consistencyDefect_le_opFamilyDistSq_of_projective _
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
    (fun xz : (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P) =>
      S.placedMeasurement p2 (points.Q p2.side xz.1 xz.2)) S.psiHat
    (fun xz => S.placedMeasurement_isProjective p1 _ (points.projective _ xz.1 xz.2))
    (fun xz => S.placedMeasurement_isProjective p2 _ (points.projective _ xz.1 xz.2)))
    (points.self_consistent p1 p2 hopp)

/-- The paired-line POVM in the proof of `lem:qld-xz-lines`, paper
`14_analysis_of_the_pauli_basis_test.tex:942-949`. The X effect is the outer
projector. This construction does not assert consistency with a point witness. -/
def ProjectiveSetting.combinedLineMeasurement {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams) :
    Quantum.Measurement (DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d)) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun fs => (S.lineMeasExp side .X lineX).effect fs.1 *
      (S.lineMeasExp side .Z lineZ).effect fs.2 *
      (S.lineMeasExp side .X lineX).effect fs.1)
    (fun fs => (pastedMeasurement_isMeasurement
      (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
      (S.lineMeasExp_isProjective side .X lineX)).1 (fs.2, fs.1))
    (by
      classical
      have hsum := (pastedMeasurement_isMeasurement
        (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
        (S.lineMeasExp_isProjective side .X lineX)).2
      simp only [pastedMeasurement, Fintype.sum_prod_type] at hsum ⊢
      rw [Finset.sum_comm]
      exact hsum)

/-- The effects of the paired-line POVM are the source's X-Z-X sandwiches. -/
@[simp] theorem ProjectiveSetting.combinedLineMeasurement_effect
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX *
        (S.lineMeasExp side .Z lineZ).effect fZ *
        (S.lineMeasExp side .X lineX).effect fX := rfl

/-- The X-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_X
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineX.kind = .axis) (hf : ¬ fX.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .X lineX haxis fX hf, zero_mul]

/-- The Z-axis degree bound for the constructed POVM, from the support
argument at paper `14_analysis_of_the_pauli_basis_test.tex:949`. -/
theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineZ.kind = .axis) (hf : ¬ fZ.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .Z lineZ haxis fZ hf, mul_zero, zero_mul]

/-- Summing out Z recovers the X line effect exactly for the constructed
sandwich. This identity is not assumed of an arbitrary `CombinedLinesWitness`. -/
theorem ProjectiveSetting.combinedLineMeasurement_sum_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX : DegPoly P.toLdParams (P.m * P.d)) :
    ∑ fZ, (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX := by
  simp only [S.combinedLineMeasurement_effect, ← Finset.sum_mul, ← Finset.mul_sum,
    (S.lineMeasExp side .Z lineZ).sum_eq_one, mul_one]
  exact (S.lineMeasExp_isProjective side .X lineX fX).1

/-- Conditional joint X/Z line measurements for `lem:qld-xz-lines`.

**Source statement:** `lem:qld-xz-lines` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:345-443`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
The error depends polynomially on `ε` and `md/q`, and the witness retains all
directed opposite-placement comparisons.  This is the formalization-only form
with an already constructed point witness; the source-facing theorem below
supplies that witness existentially.  The proof is tracked by issue #18.
Discharge: formalize the sandwich measurement and the pasting argument in the
cited proof.

**Quantitative gap (issue #118):** This unproved internal interface still
omits dependence on the unrestricted supplied point error `δQ`. The proved
`marginal_X_distance_le` and `marginal_Z_distance_le` retain the bound `4 * δQ`;
`self_consistency_defect_le` retains `δQ`. The sandwich and its degree bounds
are constructed above, but the line-point marginal comparisons, pasting, and
specialization to the constructed point error remain to be proved. See
`audits/2026-09-06-issue118-point-error-dependency.md`, attempt 2. No corrected
quantitative interface is adopted by these partial results.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness_ofPointsWitness :
    ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ),
        Nonempty (CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  sorry

/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form used by downstream calculations. -/

/-- The source-facing joint X/Z line measurement construction of
`lem:qld-xz-lines`, paper lines 882--894.

Unlike the formalization-only `_ofPointsWitness` companion, this declaration
does not assume a `CombinedPointsWitness` as an external bridge input.  It
quantifies the point error function and witness construction together with the
line construction, as the preceding source lemma supplies those points.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (CombinedLinesWitness S points
              (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaP, hdeltaP, hlines⟩ := exists_combinedLinesWitness_ofPointsWitness
  refine ⟨deltaQ, hdeltaQ, deltaP, hdeltaP, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε (deltaQ ε) S points⟩

/-! ## Restricted line distributions -/

/-- The axis and diagonal line-point laws are uniform mixtures of their
coordinate-index restrictions.

**Source statement:** `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, formalizing the
unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
`Distribution.bind` is the finite uniform-mixture operation.  The two halves
are proved in `Combining.Lines.RestrictedMixture` from the equal-fiber
decomposition of `chiIndex` and the fact that every line conditioning map
retains the shared scalar seed. -/
theorem linePointDist_eq_mixture_restricted (L : LdParams) :
    aLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedALineDist L) ∧
      dLinePointDist L =
        Distribution.bind (uniformDistribution (Fin L.m))
          (restrictedDLineDist L) :=
  ⟨aLinePointDist_eq_bind_restricted L, dLinePointDist_eq_bind_restricted L⟩

/-- Restricting a nonnegative average from the line-point distribution to one
fixed line kind and coordinate inflates its bound by at most `2m`.

**Source statement:** item 1 of `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`.
The restricted component carries mixture weight `1 / (2 m)`, so a nonnegative
average bounded by `δ` bounds it by `2 m δ`. -/
theorem avg_restricted_le {P : AdmissibleParams}
    (f : (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver (linePointDist P.toLdParams) f ≤ δ)
    (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * δ := by
  refine (avgOver_restrictedLinePointDist_le f hf kind i).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Restricting both variables of a nonnegative average over two independent
line-point samples inflates its bound by at most `4m^2`.

**Source statement:** item 2 of `lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from the unlabelled
estimate at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1056-1058`.
The one-variable estimate is applied successively to the two product
coordinates. -/
theorem avg_restricted_prod_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) -> ℝ)
    (hf : ∀ sample, 0 ≤ f sample) {δ : ℝ}
    (havg : avgOver
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams)) f ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * δ := by
  refine (avgOver_prod_restrictedLinePointDist_le f hf kindX kindZ i j).trans ?_
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- Formalization-only auxiliary for item 3 of
`lem:restricted-line-mixture-bounds`: a consistency defect of two complete
measurements placed on opposite registers inflates by at most `4 m ^ 2` when
both line-point coordinates are restricted.  Blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`. -/
theorem consistencyDefect_restricted_prod_le {P : AdmissibleParams}
    {ε δ : ℝ} {α : Type*} [Fintype α] [DecidableEq α]
    (S : ProjectiveSetting P ε) (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : ((LineDesc P.toLdParams × (Fin P.m -> PauliScalar P)) ×
        (LineDesc P.toLdParams × (Fin P.m -> PauliScalar P))) ->
      MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side))
    (hbound : consistencyDefect
      (Distribution.prod (linePointDist P.toLdParams)
        (linePointDist P.toLdParams))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ δ)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    consistencyDefect
      (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j))
      (fun sample answer => S.place p₁ ((M₁ sample).effect answer))
      (fun sample answer => S.place p₂ ((M₂ sample).effect answer))
      S.psiHat ≤ 4 * (P.m : ℝ) ^ 2 * δ := by
  unfold consistencyDefect at hbound ⊢
  refine le_trans
    (avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j) ?_
  · intro sample
    exact consistencyDefect_integrand_nonneg S p₁ p₂ hopp (M₁ sample)
      (M₂ sample)
  · exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The evaluated joint line measurement remains consistent with the joint
point measurement on every product of restricted line distributions.

**Source statement:** item 3 and Equation `eq:qld-xz-lines-restricted` of
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:595-646`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1058-1061`.
Here `consistencyDefect` is the finite POVM form of the displayed expectation
against `Id - Q` after both measurements are postprocessed by evaluation.
The universal constant is outside all strategy and parameter quantifiers, and
is the exact inflation factor `4` of `avg_restricted_prod_le`. -/
theorem restricted_lines_consistency_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : AdmissibleParams} {ε δQ δP : ℝ}
        (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP)
        (p1 p2 : Placement), p1.IsOpposite p2 ->
        ∀ (kindX kindZ : LineKind) (i j : Fin P.m),
          consistencyDefect
            (Distribution.prod (restrictedLinePointDist P kindX i)
              (restrictedLinePointDist P kindZ j))
            (fun sample answer => S.place p1
              (((lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
                (evalOpt sample.1.1 sample.1.2 fs.1,
                  evalOpt sample.2.1 sample.2.2 fs.2)).effect answer))
            (fun sample answer => S.place p2
              (((points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
                (some ab.1, some ab.2)).effect answer))
            S.psiHat ≤ C * (P.m : ℝ) ^ 2 * δP := by
  refine ⟨4, by norm_num, ?_⟩
  intro P ε δQ δP S points lines p1 p2 hopp kindX kindZ i j
  exact consistencyDefect_restricted_prod_le S p1 p2 hopp
    (fun sample => (lines.T p1.side sample.1.1 sample.2.1).postprocess fun fs =>
      (evalOpt sample.1.1 sample.1.2 fs.1, evalOpt sample.2.1 sample.2.2 fs.2))
    (fun sample => (points.Q p2.side sample.1.2 sample.2.2).postprocess fun ab =>
      (some ab.1, some ab.2))
    (lines.consistent p1 p2 hopp) kindX kindZ i j

/-! ## The sub-line distribution -/

/-- Existence of the directly indexed sub-line distribution with its two
separate projected point marginals and axis-line closure.  It supports
`lem:qld-sublines` and `rem:qld-sublines-property-three` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1069` with
its proof at lines 1071--1116.

This is a formalization auxiliary assertion, not the source-labelled
`lem:qld-sublines`.  The extended line uses the directly indexed carrier and
line-point law of `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` in
place of the seed-indexed line-point distribution over `F_q^(2m+2)` of the
source statement, so the statement carries no divisibility hypothesis and its
transport to the source carrier remains open.  Its `source_mixture` field
asserts only the separate X and Z marginal mixtures, not a stronger joint
conditional law.

The witness is the sub-line law `subLineDist` of the sampling procedure: a
line kind and an extended coordinate are drawn uniformly, an extended point
and an extended direction are drawn uniformly and independently, and two
scalar seeds are drawn independently in the coordinate-index fibers of the two
source indices of that coordinate; the triple is the canonical line of the
drawn kind through the extended point together with the two source lines of
the same kind decoded from the two coordinate blocks and from the two seeds.
Its pointwise fields are `subLineTripleOf_incidence`,
`subLineTripleOf_compatibility` and `subLineTripleOf_axis_closure`, applied to
the auxiliary randomness supplied by `exists_raw_of_mem_subLineDist_support`;
its extended-line marginal is `subLineDist_map_fst`; and its two projected
point marginals are the mixtures of `subLineDist_source_mixture`. -/
theorem exists_subLineWitness (P : AdmissibleParams) :
    Nonempty (SubLineWitness P) := by
  refine ⟨{ D := subLineDist P
            isProbability := subLineDist_isProbability P
            extended_marginal := subLineDist_map_fst P
            incidence := ?_
            compatibility := ?_
            source_mixture := subLineDist_source_mixture P
            axis_closure := ?_ }⟩
  · intro sample hsample u hu
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_incidence P kind k w hx hz hu
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_compatibility P kind k w hx hz
  · intro sample hsample haxis
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_raw_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_axis_closure P kind k w haxis

end

end MIPStarRE.QPBT
