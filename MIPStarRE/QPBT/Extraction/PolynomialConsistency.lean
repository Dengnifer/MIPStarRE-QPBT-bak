import MIPStarRE.QPBT.Extraction.TraceConsistency
import MIPStarRE.QPBT.Extraction.PointConsistencyPrime
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity

/-!
# Polynomial outcomes of the pulled-apart measurement

The joint outcome of a polynomial marginal and the last Pauli register is
`(g,h)`. Relabeling it as the polynomial `g - g_h` retains enough information
to recover every pulled-apart measurement. Polynomial collision estimates can
therefore be applied before the full-field decoder.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1503-1554`,
  especially `eq:qld-pulling-2b` and `eq:qld-pulling-12`.
- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- Issue #520.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

-- Side-indexed local spaces and the concrete extraction carriers are definitionally equal.
set_option backward.isDefEq.respectTransparency false

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

/-- A complete measurement placed on one extraction block. -/
def sideMeasurement {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    {α : Type*} [Fintype α] (M : Measurement α (ExtractionBlock P (S.LocalSpace side))) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  cases side
  · exact reindexMeasurement (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (leftPlacedMeasurement M)
  · exact reindexMeasurement (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (rightPlacedMeasurement M)

/-- Extraction-block placement has exactly the effects of `placeSide`. -/
theorem sideMeasurement_effect {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    {α : Type*} [Fintype α] (M : Measurement α (ExtractionBlock P (S.LocalSpace side)))
    (a : α) : (S.sideMeasurement side M).effect a = S.placeSide side (M.effect a) := by
  cases side <;> rfl

/-- Extraction-block placement preserves projectivity. -/
theorem sideMeasurement_isProjective {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide)
    {α : Type*} [Fintype α] (M : Measurement α (ExtractionBlock P (S.LocalSpace side)))
    (hM : Measurement.IsProjective M) : Measurement.IsProjective (S.sideMeasurement side M) := by
  cases side <;> apply reindexMeasurement_isProjective <;> intro a
  · exact MakingMeasurementsProjective.isProj_kronecker (hM a) (IsStarProjection.one _)
  · exact MakingMeasurementsProjective.isProj_kronecker (IsStarProjection.one _) (hM a)

/-- Consistency is unchanged when the six registers are regrouped into the
two extraction blocks. -/
theorem consistencyDefect_placeSide_eq {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] (μ : Distribution X)
    (A : X → α → Op (ExtractionBlock P S.toStrategy.ιA))
    (B : X → α → Op (ExtractionBlock P S.toStrategy.ιB))
    (ψ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    consistencyDefect μ (fun x a => S.placeSide .alice (A x a))
        (fun x a => S.placeSide .bob (B x a)) ψ =
      consistencyDefect μ (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (B x a))
        (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) ψ) := by
  unfold consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp only [hab, if_true]
  · simp only [if_neg hab, consistency_term_eq_stateQForm]
    rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul]
    rfl

end ProjectiveSetting

/-- The joint measurement of the polynomial outcome and last Pauli register,
whose tensor effects occur in `eq:qld-pulling-2b`. -/
def pulledJointMeasurement {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P × PauliRegister P) (ExtractionBlock P (S.LocalSpace side)) :=
  Measurement.ofSumEqOne
    (fun gh => heteroKron ((w.marginalPoly side W).effect gh.1) (pauliProj W gh.2))
    (fun gh => kronecker_nonneg ((w.marginalPoly side W).pos gh.1)
      (posSemidef_pauliProj W gh.2).nonneg)
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← heteroKron_finset_sum_right, sum_pauliProj_eq_one]
      rw [← heteroKron_finset_sum_left, (w.marginalPoly side W).sum_eq_one,
        heteroKron_one_one])

/-- The polynomial `g - g_h` appearing in the pulling calculation, measured
by relabeling the joint tensor effects. Its individual degree is at most `d`
because admissibility gives `1 ≤ d`. -/
def pulledPolyMeasurement {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P) (ExtractionBlock P (S.LocalSpace side)) := by
  classical
  exact (pulledJointMeasurement w side W).postprocess
    (fun gh => gh.1 - encodingPoly gh.2)

/-- The polynomial-difference measurement is projective, since its joint
measurement has tensor-product projectors. -/
theorem pulledPolyMeasurement_isProjective {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) :
    Measurement.IsProjective (pulledPolyMeasurement w side W) := by
  apply SandwichProduct.postprocess_isProjective
  intro gh
  apply MakingMeasurementsProjective.isProj_kronecker (w.marginalPoly_isProjective side W gh.1)
  constructor
  · change pauliProj W gh.2 * pauliProj W gh.2 = pauliProj W gh.2
    simp only [pauliProj_mul_pauliProj, if_true]
  · exact (posSemidef_pauliProj W gh.2).isHermitian

/-- Evaluating the difference polynomial gives the scalar convolution used
in the pulling calculation. This identity holds for every polynomial outcome. -/
theorem pulledPolyMeasurement_eval_effect
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (a : PauliScalar P) :
    ((pulledPolyMeasurement w side W).postprocess
      (fun g => MvPolynomial.eval u g.1)).effect a =
        ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
          (tauDotProj W (indicatorVec u) (MvPolynomial.eval u g.1 - a)) := by
  classical
  unfold pulledPolyMeasurement
  rw [Measurement.postprocess_comp, Measurement.postprocess_effect]
  change (∑ gh ∈ Finset.univ.filter
      (fun gh : Poly P × PauliRegister P =>
        MvPolynomial.eval u (gh.1 - encodingPoly gh.2).1 = a),
      heteroKron ((w.marginalPoly side W).effect gh.1) (pauliProj W gh.2)) = _
  have heval (g : Poly P) (h : PauliRegister P) :
      MvPolynomial.eval u (g - encodingPoly h).1 =
        MvPolynomial.eval u g.1 - dotProduct h (indicatorVec u) := by
    change MvPolynomial.eval u (g.1 - lowDegreeEncoding h) = _
    rw [MvPolynomial.eval_sub]
    congr 1
    exact lowDegreeEnc_eq_dotProduct h u
  simp only [Finset.sum_filter, Fintype.sum_prod_type, heval,
    tauDotProj, bracketOp, heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have heq : MvPolynomial.eval u g.1 - dotProduct h (indicatorVec u) = a ↔
      dotProduct h (indicatorVec u) = MvPolynomial.eval u g.1 - a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [heq]
  split_ifs <;> simp [heteroKron]

/-- Decoding the difference polynomial gives the difference of the decoded
labels. This uses linearity, not decoder/evaluation agreement for arbitrary
polynomials; compare the symmetry argument at paper line 1550. -/
theorem decodeFq_sub_encodingPoly {P : AdmissibleParams}
    (g : Poly P) (h : PauliRegister P) :
    decodeFq (g - encodingPoly h) = decodeFq g - h := by
  have hsub : decodeFq (g - encodingPoly h) = decodeFq g - decodeFq (encodingPoly h) := by
    funext y
    simp [decodeOn, decodeAt, evalPoly, MvPolynomial.eval_sub]
  rw [hsub, decodeFq_lowDegreeEncoding]

/-- The original pulled-apart measurement is a relabeling of the polynomial
`g - g_h` measurement. This is an exact finite-sum form of the constraints in
`eq:qld-pulling-2b` and the symmetry step at paper line 1550. -/
theorem tildeMeasurement_eq_pulledPoly_postprocess
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    tildeMeasurement w side W u =
      (pulledPolyMeasurement w side W).postprocess
        (fun g => dotProduct (decodeFq g) u) := by
  classical
  unfold pulledPolyMeasurement
  rw [Measurement.postprocess_comp]
  apply MIPStarRE.Quantum.Measurement.ext
  intro a
  simp only [Measurement.postprocess_effect, decodeFq_sub_encodingPoly, sub_dotProduct]
  change (∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
      (tauDotProj W u (dotProduct (decodeFq g) u - a))) =
    ∑ gh ∈ Finset.univ.filter
      (fun gh : Poly P × PauliRegister P =>
        dotProduct (decodeFq gh.1) u - dotProduct gh.2 u = a),
      heteroKron ((w.marginalPoly side W).effect gh.1) (pauliProj W gh.2)
  simp only [tauDotProj, bracketOp, heteroKron_finset_sum_right,
    Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have heq : dotProduct h u = dotProduct (decodeFq g) u - a ↔
      dotProduct (decodeFq g) u - dotProduct h u = a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [heq]
  split_ifs <;> simp [heteroKron]

/-- Distinct bounded polynomial representatives collide at a uniform point
with probability at most `md/q`. This specializes the existing
Schwartz--Zippel theorem to the extraction outcome type. -/
theorem poly_eval_collision_le {P : AdmissibleParams} (g h : Poly P) (hne : g ≠ h) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u h.1
        then (1 : ℝ) else 0) ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by
  rw [polynomialAgreement_avg_eq_agreementProbability]
  have hsz := schwartzZippel_individualDegree g h hne
  have hcard : Fintype.card (PauliScalar P) = P.q := P.model.card
  have hreal : (polynomialAgreementProbability P.m (PauliScalar P) g.1 h.1 : ℝ) ≤
      ((P.m * P.d : ℕ) : ℝ) / (Fintype.card (PauliScalar P) : ℝ) := by
    simpa only [NNRat.cast_div, NNRat.cast_natCast] using
      (NNRat.cast_le (K := ℝ)).mpr hsz
  simpa only [hcard] using hreal

/-- The evaluated difference measurement and the original point measurement
have the same overlap as the polynomial marginal and expanded point
measurement. This is `eq:qld-pulling-2b` summed over the scalar outcome. -/
theorem sum_pulledPoly_eval_mul_point_bob
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P,
      S.placeSide .alice (((pulledPolyMeasurement w .alice W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
      ∑ g : Poly P, S.place .AA' ((w.marginalPoly .alice W).effect g) *
        S.place .BA'' ((S.pointMeasExp .bob W u).effect (MvPolynomial.eval u g.1)) := by
  classical
  simp only [pulledPolyMeasurement_eval_effect, S.placeSide_alice_finset_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub]

/-- The register-interchanged overlap identity for the evaluated difference
measurement. No decoding identity is used. -/
theorem sum_point_alice_mul_pulledPoly_eval
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ a : PauliScalar P, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
      S.placeSide .bob (((pulledPolyMeasurement w .bob W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a)) =
      ∑ g : Poly P, S.place .BB' ((w.marginalPoly .bob W).effect g) *
        S.place .AB'' ((S.pointMeasExp .alice W u).effect (MvPolynomial.eval u g.1)) := by
  classical
  simp only [pulledPolyMeasurement_eval_effect, S.placeSide_bob_finset_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
  rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub]

/-- The point-measurement consistency defect is unchanged by adjoining the
two local EPR pairs in the expanded state. -/
theorem point_consistencyDefect_placePlayer_eq
    {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a)) S.toStrategy.ψ := by
  classical
  unfold consistencyDefect
  apply avgOver_congr
  intro u
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp only [hab, if_true]
  · simp only [if_neg hab, consistency_term_eq_stateQForm]
    change stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
        S.placePlayer .bob ((S.pointMeas .bob W u).effect b)) =
      stateQForm S.toStrategy.ψ
        (@heteroKron S.toStrategy.ιA S.toStrategy.ιB ((S.pointMeas .alice W u).effect a)
            (1 : Op S.toStrategy.ιB) *
          @heteroKron S.toStrategy.ιA S.toStrategy.ιB (1 : Op S.toStrategy.ιA)
            ((S.pointMeas .bob W u).effect b))
    rw [placed_product_stateQForm_eq]
    have hA := measurement_effect_hermitian (S.pointMeas .alice W u) a
    have hB := measurement_effect_hermitian (S.pointMeas .bob W u) b
    have hp := S.stateQForm_place_AB''_mul_BB'
      ((S.pointMeas .alice W u).effect a) ((S.pointMeas .bob W u).effect b)
      (1 : Op (PauliRegister P)) hA hB Matrix.isHermitian_one
    have hplace : S.place .AB''
        (heteroKron ((S.pointMeas .alice W u).effect a) (1 : Op (PauliRegister P))) =
        S.placePlayer .alice ((S.pointMeas .alice W u).effect a) := by
      ext row col
      simp [ProjectiveSetting.place, ProjectiveSetting.placePlayer, heteroKron,
        Matrix.kronecker, Matrix.one_apply]
      split_ifs <;> simp_all
    rw [hplace, heteroKron_one_one, stateQForm_one, eprState_norm, one_pow, mul_one] at hp
    exact hp

set_option maxHeartbeats 800000 in
-- Reindexing and two nested finite outcome sums require additional elaboration.
/-- Schwartz--Zippel and decoding postprocessing reduce pulled-apart
consistency to consistency of the evaluated difference polynomials. This is
the collision and symmetry portion of `eq:qld-pulling-12`. -/
theorem tildeM_consistencyDefect_le_pulledPoly_eval_add
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) :
    consistencyDefect (uniformDistribution (PauliRegister P))
      (fun u a => S.placeSide .alice (tildeM w .alice W u a))
      (fun u a => S.placeSide .bob (tildeM w .bob W u a)) S.psiHat ≤
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (((pulledPolyMeasurement w .alice W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a))
      (fun u a => S.placeSide .bob (((pulledPolyMeasurement w .bob W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a)) S.psiHat +
      ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by
  classical
  let χ := reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat
  let A : Measurement (Poly P) (ExtractionBlock P S.toStrategy.ιA) :=
    pulledPolyMeasurement w .alice W
  let B : Measurement (Poly P) (ExtractionBlock P S.toStrategy.ιB) :=
    pulledPolyMeasurement w .bob W
  have hχ : ‖χ‖ = 1 := (reindexState_norm_eq _ _).trans S.psiHat_norm
  have hcollision := SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    A B χ (fun g u => MvPolynomial.eval u g.1)
    (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) hχ (by positivity) poly_eval_collision_le
  rw [S.consistencyDefect_placeSide_eq, S.consistencyDefect_placeSide_eq]
  change consistencyDefect (uniformDistribution (PauliRegister P))
    (fun u a => heteroKron (tildeM w .alice W u a) 1)
    (fun u a => heteroKron 1 (tildeM w .bob W u a)) χ ≤ _
  have hpost (u : PauliRegister P) := consistencyDefect_postprocess_le
    (uniformDistribution Unit) (fun _ => A) (fun _ => B) χ
    (fun g => dotProduct (decodeFq g) u)
  have hpoint (u : PauliRegister P) :
      (∑ a : PauliScalar P, ∑ b : PauliScalar P, if a = b then 0 else
        stateQForm χ (heteroKron (tildeM w .alice W u a) (tildeM w .bob W u b))) ≤
      ∑ g : Poly P, ∑ h : Poly P, if g = h then 0 else
        stateQForm χ (heteroKron (A.effect g) (B.effect h)) := by
    have hp := hpost u
    dsimp only [A, B] at hp
    have hA := tildeMeasurement_eq_pulledPoly_postprocess w .alice W u
    have hB := tildeMeasurement_eq_pulledPoly_postprocess w .bob W u
    rw [← hA, ← hB] at hp
    rw [SandwichProduct.consistencyDefect_placed_eq_avg_point,
      SandwichProduct.consistencyDefect_placed_eq_avg_point] at hp
    simp only [avgOver_uniform_const] at hp
    convert hp using 1
    rfl
  have havg := avgOver_mono (uniformDistribution (PauliRegister P)) _ _ hpoint
  rw [avgOver_uniform_const] at havg
  have hleft := SandwichProduct.consistencyDefect_placed_eq_avg_point
    (uniformDistribution (PauliRegister P))
    (tildeMeasurement w .alice W) (tildeMeasurement w .bob W) χ
  have hright := SandwichProduct.consistencyDefect_placed_eq_avg_point
    (uniformDistribution (Fin P.m → PauliScalar P))
    (fun u => A.postprocess (fun g => MvPolynomial.eval u g.1))
    (fun u => B.postprocess (fun g => MvPolynomial.eval u g.1)) χ
  exact hleft.le.trans (havg.trans (hcollision.trans_eq (congrArg
    (fun t => t + ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) hright.symm)))

end

end MIPStarRE.QPBT
