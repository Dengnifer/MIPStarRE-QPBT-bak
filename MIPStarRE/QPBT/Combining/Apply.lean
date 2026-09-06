import MIPStarRE.QPBT.Combining.Claims
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Applying the classical low-degree test

This module constructs the conditional extended-line POVM and proves its degree
support and completed-evaluation comparison. The quantitative application obligations
at the end of the Pauli-basis combining argument remain open.
Directly indexed combined-line measurements are recorded both
with the error form printed in the source and with the weaker estimate established by
its first proof route.  The final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials.  The existence assertions below
record the measurements and quantitative estimates required by the combining argument;
their derivations remain open.

## References

The combined-line declarations record directly indexed auxiliary forms of
`lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

/-- A positive atom gives a positive atom of every push-forward. -/
private theorem map_weight_pos_of_weight_pos {Source Target : Type*}
    [DecidableEq Target] (law : Distribution Source) (mapping : Source → Target)
    (sample : Source) (hpositive : 0 < law.weight sample) :
    0 < (law.map mapping).weight (mapping sample) := by
  classical
  have hmem : sample ∈ law.support := by
    by_contra hnot
    simp [law.outsideSupport sample hnot] at hpositive
  exact hpositive.trans_le (Finset.single_le_sum
    (fun other _ => law.nonnegative other) (Finset.mem_filter.mpr ⟨hmem, rfl⟩))

/-- Every canonical direct line has positive marginal mass. In particular, the
conditional distribution in the construction at paper lines 1118--1132 is defined
on every direct line, including zero-direction diagonal lines. -/
theorem directLinePointDist_line_weight_pos (params : DirectLdParams)
    (line : DirectLineDesc params) :
    0 < ((directLinePointDist params).map Prod.fst).weight line := by
  have huniform (sample : DirectLdSpace params) :
      0 < (uniformDistribution (DirectLdSpace params)).weight sample := by
    rw [uniformDistribution_weight_apply]
    positivity
  suffices hpoint : 0 < (directLinePointDist params).weight (line, line.base) by
    exact map_weight_pos_of_weight_pos _ Prod.fst _ hpoint
  cases line with
  | axis base index baseFixed =>
    let sample : DirectLdSpace params := ⟨base, index, 0⟩
    have haxis := map_weight_pos_of_weight_pos
      (uniformDistribution (DirectLdSpace params))
      (fun source => (directALineDescOf params source, source.point)) sample (huniform sample)
    have hdecode : directALineDescOf params sample = .axis base index baseFixed := by
      simp [directALineDescOf, sample, baseFixed]
    change 0 < (directALinePointDist params).weight _ at haxis
    rw [hdecode] at haxis
    have hother := (directDLinePointDist params).nonnegative
      (DirectLineDesc.axis base index baseFixed, base)
    change 0 < (1 / 2 : ℝ) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    change 0 < (directALinePointDist params).weight
      (DirectLineDesc.axis base index baseFixed, base) at haxis
    dsimp only [DirectLineDesc.base]
    linarith
  | diagonal base index direction baseFixed prefixZero =>
    let sample : DirectLdSpace params := ⟨base, index, direction⟩
    have hprefix : directPrefixProjection index direction = direction := by
      funext coordinate
      simp only [directPrefixProjection]
      split_ifs with hbefore
      · exact (prefixZero coordinate hbefore).symm
      · rfl
    have hdiagonal := map_weight_pos_of_weight_pos
      (uniformDistribution (DirectLdSpace params))
      (fun source => (directDLineDescOf params source, source.point)) sample (huniform sample)
    have hdecode : directDLineDescOf params sample =
        .diagonal base index direction baseFixed prefixZero := by
      simp [directDLineDescOf, sample, hprefix, baseFixed]
    change 0 < (directDLinePointDist params).weight _ at hdiagonal
    rw [hdecode] at hdiagonal
    have hother := (directALinePointDist params).nonnegative
      (DirectLineDesc.diagonal base index direction baseFixed prefixZero, base)
    change 0 < (1 / 2 : ℝ) * (directALinePointDist params).weight _ +
      (1 - 1 / 2) * (directDLinePointDist params).weight _
    change 0 < (directDLinePointDist params).weight
      (DirectLineDesc.diagonal base index direction baseFixed prefixZero, base) at hdiagonal
    dsimp only [DirectLineDesc.base]
    linarith

/-- The supported triples over a fixed extended line. Restricting the carrier
retains the affine compatibility proof without choosing any substitute lines. -/
abbrev SubLineWitness.Fiber {params : AdmissibleParams} (sublines : SubLineWitness params)
    (line : DirectLineDesc params.extendedDirectLd) :=
  ↥(sublines.D.support.filter (fun sample => sample.1 = line))

/-- The mass of a subline fiber is positive by the prescribed extended marginal. -/
theorem SubLineWitness.fiber_mass_pos {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    0 < (sublines.D.map Prod.fst).weight line := by
  rw [sublines.extended_marginal]
  exact directLinePointDist_line_weight_pos _ _

/-- The genuine conditional law of the supported subline triples given their
extended line, as in paper lines 1118--1132. There is no zero-mass branch. -/
def SubLineWitness.conditionalLaw {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    Distribution (sublines.Fiber line) where
  support := Finset.univ
  weight sample := sublines.D.weight sample.val / (sublines.D.map Prod.fst).weight line
  nonnegative sample := div_nonneg (sublines.D.nonnegative sample.val)
    (sublines.fiber_mass_pos line).le
  outsideSupport sample hnot := (hnot (Finset.mem_univ sample)).elim

/-- Conditioning on an extended line preserves total mass one. -/
theorem SubLineWitness.conditionalLaw_isProbability {params : AdmissibleParams}
    (sublines : SubLineWitness params) (line : DirectLineDesc params.extendedDirectLd) :
    (sublines.conditionalLaw line).IsProbability := by
  change (∑ sample : sublines.Fiber line,
    sublines.D.weight sample.val / (sublines.D.map Prod.fst).weight line) = 1
  rw [← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (sublines.fiber_mass_pos line).ne'

/-- Supported subline triples supply all eight affine coordinates in the
polynomial combination formula; the choice is only of proved compatible data. -/
private theorem SubLineWitness.exists_affineData {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) :
    ∃ data : Fin 8 → PauliScalar params,
      IsCombineLineCompatible (directPointToPauli params sample.1.base)
        (directPointToPauli params sample.1.direction)
        sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
        (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) := by
  obtain ⟨offsetX, slopeX, offsetZ, slopeZ, alpha, alphaSlope, beta, betaSlope, hcompat⟩ :=
    sublines.compatibility sample hsample
  exact ⟨![offsetX, slopeX, offsetZ, slopeZ, alpha, alphaSlope, beta, betaSlope], hcompat⟩

/-- Affine coordinates for the actual subline triple, not a replacement POVM. -/
def SubLineWitness.affineData {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) : Fin 8 → PauliScalar params :=
  Classical.choose (sublines.exists_affineData sample hsample)

/-- The selected coordinates satisfy the source's affine line identities. -/
theorem SubLineWitness.affineData_compatible {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) :
    let data := sublines.affineData sample hsample
    IsCombineLineCompatible (directPointToPauli params sample.1.base)
      (directPointToPauli params sample.1.direction)
      sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
      (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7) :=
  Classical.choose_spec (sublines.exists_affineData sample hsample)

/-- The source polynomial combination on a supported triple, transported only
along the canonical identification of the two scalar models. -/
def SubLineWitness.combinedPolynomial {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d)) :
    DirectDegPoly params.extendedDirectLd (params.m * params.d + 1) :=
  let data := sublines.affineData sample hsample
  fun index => (extendedDirectScalarEquiv params).symm
    (combineLinePoly (data 0) (data 1) (data 2) (data 3)
      (data 4) (data 5) (data 6) (data 7) polynomials.1 polynomials.2 index)

/-- The actual extended-line POVM of paper lines 1118--1132: condition the
subline law and average the postprocessed, supplied paired-line POVMs. -/
def SubLineWitness.extendedMeasurement {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (side : PlayerSide) (line : DirectLineDesc params.extendedDirectLd) :
    Quantum.Measurement (DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
      (setting.ExpandedLocalSpace side) := by
  let family (sample : sublines.Fiber line) :=
    (lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val (Finset.mem_filter.mp sample.property).1)
  have hsum : (∑ polynomial, averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => (family sample).effect polynomial)) = 1 := by
    rw [← averageOperatorOverDistribution_sum]
    simp only [Quantum.Measurement.sum_eq_one]
    exact averageOperatorOverDistribution_const_of_isProbability _
      (sublines.conditionalLaw_isProbability line) 1
  exact { effect := fun polynomial => averageOperatorOverDistribution
            (sublines.conditionalLaw line) (fun sample => (family sample).effect polynomial)
          pos := fun polynomial => averageOperatorOverDistribution_nonneg _ _
            (fun sample => (family sample).pos polynomial)
          sum_le_one := le_of_eq hsum
          sum_eq_one := hsum }

/-- Integrating the conditional law recovers the original subline law.
This is finite disintegration, not an independence assertion about projections. -/
theorem SubLineWitness.avgOver_conditionalLaw {params : AdmissibleParams}
    (sublines : SubLineWitness params) (quantity : SubLineTriple params → ℝ) :
    avgOver (sublines.D.map Prod.fst) (fun line =>
      avgOver (sublines.conditionalLaw line) (fun sample => quantity sample.val)) =
        avgOver sublines.D quantity := by
  classical
  simp only [avgOver, SubLineWitness.conditionalLaw]
  calc
    (∑ line ∈ (sublines.D.map Prod.fst).support,
        (sublines.D.map Prod.fst).weight line *
          ∑ sample : sublines.Fiber line,
            (sublines.D.weight sample.val / (sublines.D.map Prod.fst).weight line) *
              quantity sample.val) =
        ∑ line ∈ (sublines.D.map Prod.fst).support,
          ∑ sample ∈ sublines.D.support.filter (fun sample => sample.1 = line),
            sublines.D.weight sample * quantity sample := by
      apply Finset.sum_congr rfl
      intro line _
      rw [Finset.mul_sum]
      trans ∑ sample : sublines.Fiber line, sublines.D.weight sample.val * quantity sample.val
      · apply Finset.sum_congr rfl
        intro sample _
        field_simp [(sublines.fiber_mass_pos line).ne']
        exact (div_eq_iff (sublines.fiber_mass_pos line).ne').mpr (by ring)
      · exact Finset.sum_coe_sort
          (sublines.D.support.filter (fun sample => sample.1 = line))
          (fun sample => sublines.D.weight sample * quantity sample)
    _ = ∑ sample ∈ sublines.D.support, sublines.D.weight sample * quantity sample := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun sample hsample => Finset.mem_image.mpr ⟨sample, hsample, rfl⟩) _

/-- A determined direct evaluation gives precisely its completed answer. -/
private theorem directEvalOpt_eq_some_of_evaluatesTo {params : DirectLdParams} {bound : ℕ}
    (line : DirectLineDesc params) (polynomial : DirectDegPoly params bound)
    (point : Fin params.m → DirectScalarQ params) (value : DirectScalarQ params)
    (heval : DirectEvaluatesTo line polynomial point value) :
    directEvalOpt line point polynomial = some value := by
  classical
  have hexists : ∃ answer, DirectEvaluatesTo line polynomial point answer := ⟨value, heval⟩
  rw [directEvalOpt, dif_pos hexists]
  obtain ⟨parameter, hparameter⟩ := heval.1
  exact congrArg some (((Classical.choose_spec hexists).2 parameter hparameter).symm.trans
    (heval.2 parameter hparameter))

/-- Evaluation commutes with the canonical scalar identification. -/
private theorem evalCoefficient_extendedScalar {params : AdmissibleParams} {bound : ℕ}
    (polynomial : DirectDegPoly params.extendedDirectLd bound)
    (parameter : DirectScalarQ params.extendedDirectLd) :
    extendedDirectScalarEquiv params (evalCoefficient polynomial parameter) =
      evalCoefficient (fun index => extendedDirectScalarEquiv params (polynomial index))
        (extendedDirectScalarEquiv params parameter) := by
  simp [evalCoefficient]

/-- If both projected polynomials have determined values, their actual combined
polynomial has the required determined value at the extended point. This also
covers zero-direction lines: every parameter is checked, rather than selecting
one parameter or assigning a field-valued fallback. -/
theorem SubLineWitness.combinedPolynomial_evaluatesTo {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : PauliScalar params)
    (hevalX : EvaluatesTo sample.2.1 polynomials.1
      (projX (directPointToPauli params point)) valueX)
    (hevalZ : EvaluatesTo sample.2.2 polynomials.2
      (projZ (directPointToPauli params point)) valueZ) :
    DirectEvaluatesTo sample.1 (sublines.combinedPolynomial sample hsample polynomials) point
      ((extendedDirectScalarEquiv params).symm
        ((directPointToPauli params point) (alphaVar params.m) * valueX +
          (directPointToPauli params point) (betaVar params.m) * valueZ)) := by
  obtain ⟨initialParameter, hinitial⟩ := hpoint
  refine ⟨⟨initialParameter, hinitial⟩, ?_⟩
  intro parameter hparameter
  let data := sublines.affineData sample hsample
  have hcompat := sublines.affineData_compatible sample hsample
  have hformula := combineLinePoly_spec
    (directPointToPauli params sample.1.base) (directPointToPauli params sample.1.direction)
    sample.2.1.base sample.2.1.direction sample.2.2.base sample.2.2.direction
    (data 0) (data 1) (data 2) (data 3) (data 4) (data 5) (data 6) (data 7)
    polynomials.1 polynomials.2 hcompat (extendedDirectScalarEquiv params parameter)
  have hpointTransport : directPointToPauli params point =
      directPointToPauli params sample.1.base +
        extendedDirectScalarEquiv params parameter •
          directPointToPauli params sample.1.direction := by
    rw [hparameter, directPointToPauli_add, directPointToPauli_smul]
  have hvalueX := hevalX.2 _ (hpointTransport ▸ hformula.1)
  have hvalueZ := hevalZ.2 _ (hpointTransport ▸ hformula.2.1)
  apply (extendedDirectScalarEquiv params).injective
  rw [evalCoefficient_extendedScalar, RingEquiv.apply_symm_apply]
  simp only [SubLineWitness.combinedPolynomial, RingEquiv.apply_symm_apply]
  rw [hformula.2.2]
  erw [hvalueX, hvalueZ]
  rw [hpointTransport]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcompat.1, hcompat.2.1, hcompat.2.2.1, hcompat.2.2.2.1]

/-- Completed evaluation of the actual combination agrees with the source
linear combination whenever both source evaluations are defined. -/
theorem SubLineWitness.combinedPolynomial_evalOpt {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet) (valueX valueZ : PauliScalar params)
    (hevalX : evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1 =
      some valueX)
    (hevalZ : evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2 =
      some valueZ) :
    (directEvalOpt sample.1 point (sublines.combinedPolynomial sample hsample polynomials)).map
      (extendedDirectScalarEquiv params) =
        some ((directPointToPauli params point) (alphaVar params.m) * valueX +
          (directPointToPauli params point) (betaVar params.m) * valueZ) := by
  rw [directEvalOpt_eq_some_of_evaluatesTo _ _ _ _
    (sublines.combinedPolynomial_evaluatesTo sample hsample polynomials point hpoint valueX valueZ
      ((evalOpt_eq_some_iff _ _ _ _).mp hevalX) ((evalOpt_eq_some_iff _ _ _ _).mp hevalZ))]
  simp

/-- Coefficient support bounds the degree of the represented polynomial. -/
private theorem linePolynomial_natDegree_le_of_coefficients {Scalar : Type*}
    [Field Scalar] {bound degree : ℕ} (polynomial : Fin (bound + 1) → Scalar)
    (hdegree : ∀ index, degree < index.val → polynomial index = 0) :
    (linePolynomialOfCoefficients polynomial).natDegree ≤ degree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  by_cases hindex : index.val ≤ degree
  · refine Polynomial.natDegree_mul_le.trans ?_
    have hpower := Polynomial.natDegree_pow_le
      (p := (Polynomial.X : Polynomial Scalar)) (n := index.val)
    simp only [Polynomial.natDegree_X, Nat.mul_one] at hpower
    simpa using hpower.trans hindex
  · simp [hdegree index (Nat.lt_of_not_ge hindex)]

/-- Affine substitution preserves a degree bound. -/
private theorem affine_comp_natDegree_le {Scalar : Type*} [Field Scalar]
    (polynomial : Polynomial Scalar) (offset slope : Scalar) {degree : ℕ}
    (hdegree : polynomial.natDegree ≤ degree) :
    (polynomial.comp (Polynomial.C offset + Polynomial.C slope * Polynomial.X)).natDegree ≤
      degree := by
  have haffine : (Polynomial.C offset + Polynomial.C slope * Polynomial.X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  exact Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hdegree haffine)

/-- The source combination has degree at most `degree` on an axis line:
either the two scalar coordinates are constant, or both projected parameters
are constant. This is the algebraic assertion at paper lines 1127--1132. -/
theorem combineLinePoly_axis_degree {Scalar : Type*} [Field Scalar] {bound degree : ℕ}
    (hdegree : 1 ≤ degree) (data : Fin 8 → Scalar)
    (polynomialX polynomialZ : Fin (bound + 1) → Scalar)
    (hdegreeX : ∀ index, degree < index.val → polynomialX index = 0)
    (hdegreeZ : ∀ index, degree < index.val → polynomialZ index = 0)
    (haxis : (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0)) :
    ∀ index : Fin (bound + 1 + 1), degree < index.val →
      combineLinePoly (data 0) (data 1) (data 2) (data 3)
        (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ index = 0 := by
  have hpolyX := linePolynomial_natDegree_le_of_coefficients polynomialX hdegreeX
  have hpolyZ := linePolynomial_natDegree_le_of_coefficients polynomialZ hdegreeZ
  have htotal : (combineLinePolynomial (data 0) (data 1) (data 2) (data 3)
      (data 4) (data 5) (data 6) (data 7) polynomialX polynomialZ).natDegree ≤ degree := by
    unfold combineLinePolynomial
    rcases haxis with ⟨halpha, hbeta⟩ | ⟨hparamX, hparamZ⟩
    · simp only [halpha, hbeta, Polynomial.C_0, zero_mul, add_zero]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine Polynomial.natDegree_mul_le.trans ?_
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le _ (data 0) (data 1) hpolyX)
      · refine Polynomial.natDegree_mul_le.trans ?_
        simpa only [Polynomial.natDegree_C, Nat.zero_add] using
          (affine_comp_natDegree_le _ (data 2) (data 3) hpolyZ)
    · simp only [hparamX, hparamZ, Polynomial.C_0, zero_mul, add_zero, Polynomial.comp_C]
      have hterm (constant slope value : Scalar) :
          ((Polynomial.C constant + Polynomial.C slope * Polynomial.X) *
            Polynomial.C value).natDegree ≤ degree := by
        refine Polynomial.natDegree_mul_le.trans ?_
        simp only [Polynomial.natDegree_C, Nat.add_zero]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
          (Polynomial.natDegree_mul_le.trans (by simpa using hdegree)))
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (hterm _ _ _) (hterm _ _ _))
  intro index hindex
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (htotal.trans_lt hindex)

/-- Axis directions in the source line carrier are nonzero. -/
private theorem source_axis_direction_ne_zero {params : LdParams}
    (line : LineDesc params) (haxis : line.kind = .axis) : line.direction ≠ 0 := by
  cases line with
  | axis base seed baseFixed =>
    intro hzero
    have hcoordinate := congrFun hzero (chiIndex params seed)
    simp [LineDesc.direction, coordinateDirection] at hcoordinate
  | diagonal => cases haxis

/-- Two equal points on a nonzero affine direction force the parameter slope to vanish. -/
private theorem affine_slope_eq_zero {Scalar : Type*} [Field Scalar] {dimension : ℕ}
    {point base direction : Fin dimension → Scalar} {offset slope : Scalar}
    (hdirection : direction ≠ 0) (hzero : point = base + offset • direction)
    (hone : point = base + (offset + slope) • direction) : slope = 0 := by
  have hequal := add_left_cancel (hzero.symm.trans hone)
  have hvanish : slope • direction = 0 := by
    apply add_left_cancel (a := offset • direction)
    simpa only [add_smul, add_zero] using hequal.symm
  exact (smul_eq_zero.mp hvanish).resolve_right hdirection

/-- Axis subline coordinates satisfy the source's constant-coordinate alternative. -/
theorem SubLineWitness.affineData_axis {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) (haxis : sample.1.kind = .axis) :
    let data := sublines.affineData sample hsample
    (data 5 = 0 ∧ data 7 = 0) ∨ (data 1 = 0 ∧ data 3 = 0) := by
  let data := sublines.affineData sample hsample
  have hcompat := sublines.affineData_compatible sample hsample
  have hsource := sublines.axis_closure sample hsample haxis
  have hcoordinate : directPointToPauli params sample.1.direction =
      coordinateDirection sample.1.index := by
    rcases sample with ⟨line, pair⟩
    cases line with
    | axis => exact directPointToPauli_coordinateDirection params _
    | diagonal => cases haxis
  by_cases hspecial : sample.1.index = alphaVar params.m ∨ sample.1.index = betaVar params.m
  · right
    have hprojection : projX (directPointToPauli params sample.1.direction) = 0 ∧
        projZ (directPointToPauli params sample.1.direction) = 0 := by
      rw [hcoordinate]
      rcases hspecial with halpha | hbeta
      · rw [halpha]
        exact ⟨projX_coordinateDirection_alphaVar, projZ_coordinateDirection_alphaVar⟩
      · rw [hbeta]
        exact ⟨projX_coordinateDirection_betaVar, projZ_coordinateDirection_betaVar⟩
    have hzero := hcompat.2.2.2.2 (0 : PauliScalar params)
    have hone := hcompat.2.2.2.2 (1 : PauliScalar params)
    simp only [zero_smul, add_zero, mul_zero] at hzero
    simp only [one_smul, mul_one, projX_add, projZ_add, hprojection.1, hprojection.2,
      add_zero] at hone
    exact ⟨affine_slope_eq_zero (Scalar := PauliScalar params)
      (source_axis_direction_ne_zero _ hsource.1) hzero.1 hone.1,
      affine_slope_eq_zero (Scalar := PauliScalar params)
        (source_axis_direction_ne_zero _ hsource.2) hzero.2 hone.2⟩
  · left
    have halpha := Ne.symm (not_or.mp hspecial).1
    have hbeta := Ne.symm (not_or.mp hspecial).2
    rw [← hcompat.2.1, ← hcompat.2.2.2.1, hcoordinate]
    simp [coordinateDirection, halpha, hbeta]

/-- The actual polynomial combination preserves the source axis-degree support. -/
theorem SubLineWitness.combinedPolynomial_axis_degree {params : AdmissibleParams}
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) (haxis : sample.1.kind = .axis)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (hdegreeX : polynomials.1.FitsDegree params.d)
    (hdegreeZ : polynomials.2.FitsDegree params.d) :
    ∀ index, params.d < index.val →
      sublines.combinedPolynomial sample hsample polynomials index = 0 := by
  intro index hindex
  have hzero := combineLinePoly_axis_degree params.hd (sublines.affineData sample hsample)
    polynomials.1 polynomials.2 hdegreeX hdegreeZ
    (sublines.affineData_axis sample hsample haxis) index hindex
  change (extendedDirectScalarEquiv params).symm _ = 0
  erw [hzero]
  exact map_zero _

/-- The conditional average of the actual paired-line POVMs has no outcomes
above degree `d` on an extended axis line, as asserted at paper lines 1127--1132. -/
theorem SubLineWitness.extendedMeasurement_axis_degree {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (side : PlayerSide) (line : DirectLineDesc params.extendedDirectLd)
    (polynomial : DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (haxis : line.kind = .axis) (hdegree : ¬ ∀ index, params.d < index.val → polynomial index = 0) :
    (sublines.extendedMeasurement lines side line).effect polynomial = 0 := by
  classical
  change averageOperatorOverDistribution (sublines.conditionalLaw line) (fun sample =>
    ((lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val
        (Finset.mem_filter.mp sample.property).1)).effect polynomial) = 0
  unfold averageOperatorOverDistribution
  apply Finset.sum_eq_zero
  intro sample _
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hsampleAxis : sample.val.1.kind = .axis := by
    rw [(Finset.mem_filter.mp sample.property).2]
    exact haxis
  have hsource := sublines.axis_closure sample.val hsample hsampleAxis
  suffices hzero : ((lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val hsample)).effect polynomial = 0 by
    exact (congrArg (fun operator => (sublines.conditionalLaw line).weight sample • operator)
      hzero).trans (smul_zero _)
  rw [Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hdegreeX : pair.1.FitsDegree params.d
  · by_cases hdegreeZ : pair.2.FitsDegree params.d
    · have hfit := sublines.combinedPolynomial_axis_degree sample.val hsample hsampleAxis
        pair hdegreeX hdegreeZ
      rw [(Finset.mem_filter.mp hpair).2] at hfit
      exact (hdegree hfit).elim
    · exact lines.axis_degree_Z side _ _ _ _ hsource.2 hdegreeZ
  · exact lines.axis_degree_X side _ _ _ _ hsource.1 hdegreeX

/-- The completed point-pair effect is bounded by the effect of its linear
combination at the actual combined evaluation. Undefined source evaluations
contribute zero on the point side. The statement holds for either player's
measurement without any symmetry assumption on the strategy or local spaces. -/
theorem SubLineWitness.completedPoint_effect_le {params : AdmissibleParams}
    {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (sublines : SubLineWitness params) (sample : SubLineTriple params)
    (hsample : sample ∈ sublines.D.support)
    (polynomials : DegPoly params.toLdParams (params.m * params.d) ×
      DegPoly params.toLdParams (params.m * params.d))
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ sample.1.pointSet)
    (measurement : Quantum.Measurement (PauliScalar params × PauliScalar params) Carrier) :
    (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect
      (evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1,
        evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2) ≤
      (measurement.postprocess (fun pair => some
        ((directPointToPauli params point) (alphaVar params.m) * pair.1 +
          (directPointToPauli params point) (betaVar params.m) * pair.2))).effect
        ((directEvalOpt sample.1 point
          (sublines.combinedPolynomial sample hsample polynomials)).map
            (extendedDirectScalarEquiv params)) := by
  classical
  have hnoneX (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (none, value) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.fst (Finset.mem_filter.mp hpair).2
    simp at himpossible
  have hnoneZ (value : Option (PauliScalar params)) :
      (measurement.postprocess (fun pair => (some pair.1, some pair.2))).effect (value, none) =
        0 := by
    rw [Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro pair hpair
    have himpossible := congrArg Prod.snd (Finset.mem_filter.mp hpair).2
    simp at himpossible
  cases hevalX : evalOpt sample.2.1 (projX (directPointToPauli params point)) polynomials.1 with
  | none =>
    erw [hnoneX]
    exact Quantum.Submeasurement.pos _ _
  | some valueX =>
    cases hevalZ : evalOpt sample.2.2 (projZ (directPointToPauli params point)) polynomials.2 with
    | none =>
      erw [hnoneZ]
      exact Quantum.Submeasurement.pos _ _
    | some valueZ =>
      rw [sublines.combinedPolynomial_evalOpt sample hsample polynomials point hpoint
        valueX valueZ hevalX hevalZ]
      have hinjective : Function.Injective
          (fun pair : PauliScalar params × PauliScalar params => (some pair.1, some pair.2)) := by
        intro left right hequal
        exact Prod.ext (Option.some.inj (congrArg Prod.fst hequal))
          (Option.some.inj (congrArg Prod.snd hequal))
      erw [SandwichProduct.postprocess_effect_of_injective measurement _ hinjective
        (valueX, valueZ)]
      rw [Quantum.Measurement.postprocess_effect]
      exact Finset.single_le_sum (fun pair _ => measurement.pos pair)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- Uniform parameter resampling preserves the full direct line-point law,
including its canonical line, rather than merely its point marginal. -/
theorem avgOver_directLinePointDist_resample_parameter (params : DirectLdParams)
    (quantity : DirectLineDesc params × (Fin params.m → DirectScalarQ params) → ℝ) :
    avgOver (directLinePointDist params) quantity =
      avgOver ((directLinePointDist params).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ params)) (fun parameter =>
          quantity (line, line.base + parameter • line.direction))) := by
  classical
  rw [Distribution.avgOver_map, directLinePointDist, avgOver_mix, avgOver_mix]
  congr 1
  · congr 1
    unfold directALinePointDist
    simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_lineRepMap_resample_parameter (coordinateDirection index)
        (fun base point => quantity
          (.axis (lineRepMap (coordinateDirection index) base) index
            (lineRepMap_apply_self _ _), point))
  · congr 1
    unfold directDLinePointDist
    simp only [Distribution.avgOver_map]
    rw [← uniformDistribution_map_equiv (directLdSpaceIndexEquiv params).symm]
    simp only [Distribution.avgOver_map, uniformDistribution_prod, avgOver_prod]
    apply avgOver_congr
    intro index
    conv_lhs => rw [avgOver_comm]
    conv_rhs => rw [avgOver_comm]
    apply avgOver_congr
    intro direction
    simpa only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction, lineRepMap_apply_self] using
      avgOver_lineRepMap_resample_parameter (directPrefixProjection index direction)
        (fun base point => quantity
          (.diagonal (lineRepMap (directPrefixProjection index direction) base) index
            (directPrefixProjection index direction) (lineRepMap_apply_self _ _)
            (by intro coordinate hbefore; simp [directPrefixProjection, hbefore]), point))

/-- Real scalar multiplication commutes with placement. -/
private theorem place_real_smul {params : AdmissibleParams} {error : ℝ}
    (setting : ProjectiveSetting params error) (placement : Placement) (scalar : ℝ)
    (operator : Op (setting.ExpandedLocalSpace placement.side)) :
    setting.place placement (scalar • operator) = scalar • setting.place placement operator := by
  ext row column
  cases placement <;> simp only [ProjectiveSetting.place, Matrix.smul_apply, Complex.real_smul] <;>
    ring

/-- A placed overlap is linear in an averaged left operator. -/
private theorem placed_overlap_average {params : AdmissibleParams} {error : ℝ}
    {Sample : Type*} (setting : ProjectiveSetting params error) (first second : Placement)
    (law : Distribution Sample) (family : Sample → Op (setting.ExpandedLocalSpace first.side))
    (right : Op (setting.ExpandedLocalSpace second.side)) :
    stateQForm setting.psiHat
      (setting.place first (averageOperatorOverDistribution law family) *
        setting.place second right) =
      avgOver law (fun sample => stateQForm setting.psiHat
        (setting.place first (family sample) * setting.place second right)) := by
  unfold averageOperatorOverDistribution avgOver
  rw [setting.place_finsetSum, Finset.sum_mul, stateQForm_finset_sum]
  apply Finset.sum_congr rfl
  intro sample _
  rw [place_real_smul, smul_mul_assoc]
  have hscalar (operator : Op (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB)) :
      law.weight sample • operator = (law.weight sample : ℂ) • operator := by
    ext row column
    simp [Complex.real_smul]
  rw [hscalar]
  simp only [stateQForm, WinImplications.applyOperatorToState_smul_op, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Postprocessing the left measurement groups, but does not alter, its overlap
with a family indexed by the postprocessed answer. -/
private theorem placed_overlap_postprocess {params : AdmissibleParams} {error : ℝ}
    {Answer Output : Type*} [Fintype Answer] [DecidableEq Answer]
    [Fintype Output] [DecidableEq Output]
    (setting : ProjectiveSetting params error) (first second : Placement)
    (measurement : Quantum.Measurement Answer (setting.ExpandedLocalSpace first.side))
    (mapping : Answer → Output) (right : Output → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ output, stateQForm setting.psiHat
      (setting.place first ((measurement.postprocess mapping).effect output) *
        setting.place second (right output))) =
      ∑ answer, stateQForm setting.psiHat
        (setting.place first (measurement.effect answer) *
          setting.place second (right (mapping answer))) := by
  classical
  simp only [Quantum.Measurement.postprocess_effect, setting.place_finsetSum,
    Finset.sum_mul, stateQForm_finset_sum]
  calc
    (∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
        stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
          setting.place second (right output))) =
        ∑ output, ∑ answer ∈ Finset.univ.filter (fun answer => mapping answer = output),
          stateQForm setting.psiHat (setting.place first (measurement.effect answer) *
            setting.place second (right (mapping answer))) := by
      apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro answer hanswer
      rw [(Finset.mem_filter.mp hanswer).2]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- On opposite registers a positive left effect preserves order in the right
effect. This applies to both directed player placements without exchanging spaces. -/
private theorem placed_overlap_mono {params : AdmissibleParams} {error : ℝ}
    (setting : ProjectiveSetting params error) (first second : Placement)
    (hopposite : first.IsOpposite second)
    (left : Op (setting.ExpandedLocalSpace first.side))
    (lower upper : Op (setting.ExpandedLocalSpace second.side))
    (hleft : 0 ≤ left) (hright : lower ≤ upper) :
    stateQForm setting.psiHat (setting.place first left * setting.place second lower) ≤
      stateQForm setting.psiHat (setting.place first left * setting.place second upper) := by
  have hpositive := setting.place_mul_place_nonneg first second hopposite hleft
    (sub_nonneg.mpr hright)
  rw [setting.place_sub, mul_sub] at hpositive
  exact quadratic_form_mono (sub_nonneg.mp hpositive) setting.psiHat

/-- Expand the actual conditional extended-line POVM in a placed overlap.
This is exactly the averaging step at paper lines 1118--1134. -/
theorem SubLineWitness.extendedMeasurement_overlap {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (line : DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (right : Option (PauliScalar params) → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ answer, stateQForm setting.psiHat
      (setting.place first (((sublines.extendedMeasurement lines first.side line).postprocess
        (fun polynomial => (directEvalOpt line point polynomial).map
          (extendedDirectScalarEquiv params))).effect answer) *
            setting.place second (right answer))) =
      avgOver (sublines.conditionalLaw line) (fun sample =>
        ∑ pair, stateQForm setting.psiHat
          (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
            setting.place second (right ((directEvalOpt line point
              (sublines.combinedPolynomial sample.val
                (Finset.mem_filter.mp sample.property).1 pair)).map
                  (extendedDirectScalarEquiv params))))) := by
  rw [placed_overlap_postprocess]
  change (∑ polynomial, stateQForm setting.psiHat
    (setting.place first (averageOperatorOverDistribution (sublines.conditionalLaw line)
      (fun sample => ((lines.T first.side sample.val.2.1 sample.val.2.2).postprocess
        (sublines.combinedPolynomial sample.val
          (Finset.mem_filter.mp sample.property).1)).effect polynomial)) *
      setting.place second (right ((directEvalOpt line point polynomial).map
        (extendedDirectScalarEquiv params))))) = _
  simp_rw [placed_overlap_average]
  rw [← avgOver_sum]
  apply avgOver_congr
  intro sample
  exact placed_overlap_postprocess setting first second _ _ _

/-- The actual paired-line versus point-pair overlap on one subline triple,
with its uniform affine parameter. This is the integrand of the first route. -/
def pairedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
    let point := directPointToPauli params (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second (((points.Q second.side (projX point) (projZ point)).postprocess
          (fun values => (some values.1, some values.2))).effect
            (evalOpt sample.2.1 (projX point) pair.1,
              evalOpt sample.2.2 (projZ point) pair.2))))

/-- The actual extended-line versus extended-point overlap. Both families use
the supplied witnesses and the source polynomial combination. -/
def extendedPointOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params)
    (first second : Placement)
    (sample : DirectLineDesc params.extendedDirectLd ×
      (Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)) : ℝ :=
  ∑ answer, stateQForm setting.psiHat
    (setting.place first (((sublines.extendedMeasurement lines first.side sample.1).postprocess
      (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
        (extendedDirectScalarEquiv params))).effect answer) *
      setting.place second (((points.Q second.side
        (projX (directPointToPauli params sample.2))
        (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
          ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli params sample.2) (betaVar params.m) * values.2))).effect answer))

/-- The completed point-effect comparison survives conditional averaging and
placement on either directed opposite register pair. -/
theorem SubLineWitness.extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second)
    (line : DirectLineDesc params.extendedDirectLd)
    (point : Fin params.extendedDirectLd.m → DirectScalarQ params.extendedDirectLd)
    (hpoint : point ∈ line.pointSet) :
    avgOver (sublines.conditionalLaw line) (fun sample =>
      ∑ pair, stateQForm setting.psiHat
        (setting.place first ((lines.T first.side sample.val.2.1 sample.val.2.2).effect pair) *
          setting.place second (((points.Q second.side
            (projX (directPointToPauli params point))
            (projZ (directPointToPauli params point))).postprocess
              (fun values => (some values.1, some values.2))).effect
                (evalOpt sample.val.2.1 (projX (directPointToPauli params point)) pair.1,
                  evalOpt sample.val.2.2 (projZ (directPointToPauli params point)) pair.2)))) ≤
      extendedPointOverlap setting points lines sublines first second (line, point) := by
  rw [extendedPointOverlap, sublines.extendedMeasurement_overlap]
  apply avgOver_mono
  intro sample
  apply Finset.sum_le_sum
  intro pair _
  apply placed_overlap_mono setting first second hopposite _ _ _
    ((lines.T first.side sample.val.2.1 sample.val.2.2).pos pair)
  have hline := (Finset.mem_filter.mp sample.property).2
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hpointSample : point ∈ sample.val.1.pointSet := by rw [hline]; exact hpoint
  have hcomparison := sublines.completedPoint_effect_le sample.val hsample pair point hpointSample
    (points.Q second.side (projX (directPointToPauli params point))
      (projZ (directPointToPauli params point)))
  rw [hline] at hcomparison
  exact hcomparison

/-- The actual extended-line average dominates the first-route paired overlap.
This integrates the source conditional POVM without assuming any joint product
law for projected points. It holds for all directed opposite placements. -/
theorem SubLineWitness.avgOver_extendedPointOverlap_ge {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    avgOver sublines.D (pairedSublineOverlap setting points lines first second) ≤
      avgOver (directLinePointDist params.extendedDirectLd)
        (extendedPointOverlap setting points lines sublines first second) := by
  rw [avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal,
    ← sublines.avgOver_conditionalLaw]
  apply avgOver_mono
  intro line
  unfold pairedSublineOverlap
  rw [avgOver_comm]
  apply avgOver_mono
  intro parameter
  have hpoint : line.base + parameter • line.direction ∈ line.pointSet := ⟨parameter, rfl⟩
  refine le_trans ?_ (sublines.extendedPointOverlap_ge lines first second hopposite line _ hpoint)
  apply le_of_eq
  apply avgOver_congr
  intro sample
  rw [(Finset.mem_filter.mp sample.property).2]

/-- The completed consistency defect of the actual extended-line POVM is
bounded by the first-route deficit, for both player placements. -/
theorem SubLineWitness.extended_consistencyDefect_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    consistencyDefect (directLinePointDist params.extendedDirectLd)
      (fun sample answer => setting.place first
        (((sublines.extendedMeasurement lines first.side sample.1).postprocess
          (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
            (extendedDirectScalarEquiv params))).effect answer))
      (fun sample answer => setting.place second
        (((points.Q second.side (projX (directPointToPauli params sample.2))
          (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
            ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
              (directPointToPauli params sample.2) (betaVar params.m) * values.2))).effect answer))
      setting.psiHat ≤ 1 - avgOver sublines.D
        (pairedSublineOverlap setting points lines first second) := by
  erw [consistencyDefect_eq_one_sub_overlap (directLinePointDist params.extendedDirectLd)
    (fun sample => setting.placedMeasurement first
      ((sublines.extendedMeasurement lines first.side sample.1).postprocess
        (fun polynomial => (directEvalOpt sample.1 sample.2 polynomial).map
          (extendedDirectScalarEquiv params))))
    (fun sample => setting.placedMeasurement second
      ((points.Q second.side (projX (directPointToPauli params sample.2))
        (projZ (directPointToPauli params sample.2))).postprocess (fun values => some
          ((directPointToPauli params sample.2) (alphaVar params.m) * values.1 +
            (directPointToPauli params sample.2) (betaVar params.m) * values.2))))
    setting.psiHat (directLinePointDist_isProbability _) setting.psiHat_norm]
  exact sub_le_sub_left (sublines.avgOver_extendedPointOverlap_ge lines first second hopposite) 1

/-- The ordered Z-then-X point overlap on the actual subline law. -/
def orderedSublineOverlap {params : AdmissibleParams} {error pointError lineError : ℝ}
    (setting : ProjectiveSetting params error) (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (first second : Placement)
    (sample : SubLineTriple params) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
    let point := directPointToPauli params (sample.1.base + parameter • sample.1.direction)
    ∑ pair, stateQForm setting.psiHat
      (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
        setting.place second
          ((setting.pointMeasExpOption second.side .Z (projZ point)).effect
              (evalOpt sample.2.2 (projZ point) pair.2) *
            (setting.pointMeasExpOption second.side .X (projX point)).effect
              (evalOpt sample.2.1 (projX point) pair.1))))

/-- The first-route replacement by the ordered point product holds for any
placement, in particular for the missing second-player orientation. Its only
distributional input is the uniform joint point marginal, not a product law
conditional on the projected lines. -/
theorem SubLineWitness.paired_ordered_overlap_gap_le {params : AdmissibleParams}
    {error pointError lineError : ℝ} {setting : ProjectiveSetting params error}
    {points : CombinedPointsWitness setting pointError}
    (sublines : SubLineWitness params) (lines : CombinedLinesWitness setting points lineError)
    (first second : Placement) :
    |avgOver sublines.D (pairedSublineOverlap setting points lines first second) -
      avgOver sublines.D (orderedSublineOverlap setting points lines first second)| ≤
        Real.sqrt (4 * pointError) := by
  let law := Distribution.prod sublines.D
    (uniformDistribution (DirectScalarQ params.extendedDirectLd))
  let point (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd) :=
    directPointToPauli params (sample.1.1.base + sample.2 • sample.1.1.direction)
  let lineMeasurement (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd) :=
    setting.placedMeasurement first
      ((lines.T first.side sample.1.2.1 sample.1.2.2).postprocess (fun pair =>
        (evalOpt sample.1.2.1 (projX (point sample)) pair.1,
          evalOpt sample.1.2.2 (projZ (point sample)) pair.2)))
  let joint (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd)
      (answer : Option (PauliScalar params) × Option (PauliScalar params)) :=
    setting.place second (((points.Q second.side (projX (point sample))
      (projZ (point sample))).postprocess (fun values => (some values.1, some values.2))).effect
        answer)
  let ordered (sample : SubLineTriple params × DirectScalarQ params.extendedDirectLd)
      (answer : Option (PauliScalar params) × Option (PauliScalar params)) :=
    setting.place second
      ((setting.pointMeasExpOption second.side .Z (projZ (point sample))).effect answer.2 *
        (setting.pointMeasExpOption second.side .X (projX (point sample))).effect answer.1)
  have hprob : law.IsProbability := Distribution.prod_isProbability _ _ sublines.isProbability
    (uniformDistribution_isProbability _)
  have hdist : opFamilyDistSq law joint ordered setting.psiHat ≤ 4 * pointError := by
    unfold opFamilyDistSq
    change avgOver law (fun sample => ∑ answer,
      ‖applyOperatorToState (joint sample answer - ordered sample answer) setting.psiHat‖ ^ 2) ≤ _
    have hcompleted := avgOver_congr law _ _ (fun sample =>
      setting.completedPair_norm_sq_sum_ZX points second
        (projX (point sample)) (projZ (point sample)))
    dsimp only [joint, ordered] at *
    rw [hcompleted]
    change avgOver law (fun sample => ∑ answer : PauliScalar params × PauliScalar params,
      ‖applyOperatorToState
        (setting.place second ((points.Q second.side (projX (point sample))
          (projZ (point sample))).effect answer) -
          setting.place second
            ((setting.pointMeasExp second.side .Z (projZ (point sample))).effect answer.2 *
              (setting.pointMeasExp second.side .X (projX (point sample))).effect answer.1))
        setting.psiHat‖ ^ 2) ≤ _
    rw [show law = Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ params.extendedDirectLd)) from rfl, avgOver_prod]
    dsimp only [point]
    rw [SubLineWitness.avgOver_projX_projZ params sublines
      (fun coordinates => ∑ answer : PauliScalar params × PauliScalar params,
        ‖applyOperatorToState
          (setting.place second ((points.Q second.side coordinates.1 coordinates.2).effect answer) -
            setting.place second
              ((setting.pointMeasExp second.side .Z coordinates.2).effect answer.2 *
                (setting.pointMeasExp second.side .X coordinates.1).effect answer.1))
          setting.psiHat‖ ^ 2)]
    exact points.orderedZX_dist_le second
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq law lineMeasurement joint ordered
    setting.psiHat hprob setting.psiHat_norm (4 * pointError) hdist
  have hregroup (right : (SubLineTriple params × DirectScalarQ params.extendedDirectLd) →
      Option (PauliScalar params) × Option (PauliScalar params) →
        Op (setting.ExpandedLocalSpace second.side)) :
      avgOver law (fun sample => ∑ answer, stateQForm setting.psiHat
        ((lineMeasurement sample).effect answer * setting.place second (right sample answer))) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
          ∑ pair, stateQForm setting.psiHat
            (setting.place first ((lines.T first.side sample.2.1 sample.2.2).effect pair) *
              setting.place second (right (sample, parameter)
                (evalOpt sample.2.1 (projX (point (sample, parameter))) pair.1,
                  evalOpt sample.2.2 (projZ (point (sample, parameter))) pair.2))))) := by
    change avgOver (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ params.extendedDirectLd))) _ = _
    rw [avgOver_prod]
    apply avgOver_congr
    intro sample
    apply avgOver_congr
    intro parameter
    exact placed_overlap_postprocess setting first second _ _ _
  dsimp only [joint, ordered] at hgap
  rw [hregroup, hregroup] at hgap
  exact hgap

/-- Chaining Claims 17-1, 17-2, and 17-3 bounds the joint overlap on the
actual subline law. This is the first route to `eq:qld-combined-lines-consistency`,
paper `14_analysis_of_the_pauli_basis_test.tex:1134-1241`, with the corrected
claim errors documented in `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.
It uses no assertion about the joint conditional law of the two projected points.
`SubLineWitness.extended_consistencyDefect_le` now integrates this overlap into
the actual extended-line comparison. -/
theorem subline_joint_overlap_near_one :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : AdmissibleParams) (error pointError lineError : ℝ)
        (setting : ProjectiveSetting params error)
        (points : CombinedPointsWitness setting pointError)
        (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
              let point := directPointToPauli params
                (sample.1.base + parameter • sample.1.direction)
              ∑ polyX, ∑ polyZ,
                (inner ℂ setting.psiHat ((EuclideanSpace.equiv
                  (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB) ℂ).symm
                    ((setting.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (polyX, polyZ)) *
                      setting.place .BA''
                        (((points.Q .bob (projX point) (projZ point)).postprocess
                          (fun pair => (some pair.1, some pair.2))).effect
                            (evalOpt sample.2.1 (projX point) polyX,
                              evalOpt sample.2.2 (projZ point) polyZ))).mulVec
                                setting.psiHat))).re)) - 1| ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := by
  obtain ⟨firstConstant, hfirstConstant, hfirst⟩ := subline_replace_by_ordered_product
  obtain ⟨secondConstant, hsecondConstant, hsecond⟩ := subline_remove_X_factor
  obtain ⟨thirdConstant, hthirdConstant, hthird⟩ := subline_Z_term_near_one
  refine ⟨firstConstant + secondConstant + thirdConstant, by linarith, ?_⟩
  intro params error pointError lineError setting points lines sublines
  have hchain := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add (hfirst params error pointError lineError setting points lines sublines)
      ((abs_sub_le _ _ (1 : ℝ)).trans
        (add_le_add (hsecond params error pointError lineError setting points lines sublines)
          (hthird params error pointError lineError setting points lines sublines))))
  have hpointHalf : 0 ≤ pointError ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hsum : 0 ≤ lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) :=
    add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have herrorQuarter := rpow_quarter_nonneg error
  simp only [Real.rpow_eq_pow] at herrorQuarter
  have hdimension := Real.sqrt_nonneg (params.m : ℝ)
  have hbound : firstConstant * pointError ^ (1 / 2 : ℝ) +
      secondConstant * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ)) +
      thirdConstant * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ)) ≤
      (firstConstant + secondConstant + thirdConstant) *
        (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
          (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ))) := by
    nlinarith [mul_nonneg hsecondConstant.le hpointHalf,
      mul_nonneg hthirdConstant.le hpointHalf,
      mul_nonneg (mul_nonneg hfirstConstant.le hdimension) hsum,
      mul_nonneg (mul_nonneg hfirstConstant.le hdimension) herrorQuarter,
      mul_nonneg (mul_nonneg hsecondConstant.le hdimension) herrorQuarter]
  exact hchain.trans (by simpa only [Real.rpow_eq_pow, add_assoc] using hbound)

/-- The actual first-player extended-line deficit obeys the first-route
quantitative estimate at paper lines 1134--1241. This is not the two-player
witness assertion; see `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem extended_first_player_deficit_le :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : AdmissibleParams) (error pointError lineError : ℝ)
        (setting : ProjectiveSetting params error)
        (points : CombinedPointsWitness setting pointError)
        (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params),
        1 - avgOver (directLinePointDist params.extendedDirectLd)
          (extendedPointOverlap setting points lines sublines .AA' .BA'') ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := by
  obtain ⟨constant, hconstant, hnear⟩ := subline_joint_overlap_near_one
  refine ⟨constant, hconstant, ?_⟩
  intro params error pointError lineError setting points lines sublines
  have hnear' : |avgOver sublines.D
      (pairedSublineOverlap setting points lines .AA' .BA'') - 1| ≤
      constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ))) := by
    unfold pairedSublineOverlap
    simp only [Fintype.sum_prod_type]
    exact hnear params error pointError lineError setting points lines sublines
  refine (sub_le_sub_left
    (sublines.avgOver_extendedPointOverlap_ge lines .AA' .BA'' trivial) 1).trans ?_
  exact (le_abs_self (1 - avgOver sublines.D
    (pairedSublineOverlap setting points lines .AA' .BA''))).trans
      (by simpa only [abs_sub_comm] using hnear')

/-- Polynomial absorption for the first combining route, including large errors.
The independent unit bound on consistency accounts for the minimum. The factor
`dimension` is retained, as required by the correction to `lem:qld-4-13` in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, paper lines 1134--1246. -/
theorem exists_combining_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hline
  let finalPower := min (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
  let coefficient := pointConstant ^ (1 / 2 : ℝ) + lineConstant ^ (1 / 4 : ℝ) +
    pointConstant ^ (1 / 4 : ℝ) + 1
  let finalConstant := 1 + constant * coefficient
  have hfinalPower : 0 < finalPower := by dsimp [finalPower]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    linarith [mul_nonneg hconstant hcoefficient]
  refine ⟨fun error ratio => finalConstant *
    (error ^ finalPower + ratio ^ (ratioPower / 4)),
    ⟨finalConstant, finalPower, ratioPower / 4, hfinalConstant, hfinalPower,
      by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have herrorTerm : 0 ≤ error ^ finalPower := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ ratio ^ (ratioPower / 4) := Real.rpow_nonneg hratio _
  by_cases herrorOne : error ≤ 1
  · have hpointValue := hpointBound error herror
    have hlineValue := hlineBound error ratio herror hratio
    have hpointRoot (power : ℝ) (hpower : 0 ≤ power)
        (hsmall : finalPower ≤ pointPower * power) :
        (pointError error) ^ power ≤ pointConstant ^ power * error ^ finalPower := by
      calc
        _ ≤ (pointConstant * error ^ pointPower) ^ power :=
          Real.rpow_le_rpow hpointValue.1 hpointValue.2 hpower
        _ = pointConstant ^ power * error ^ (pointPower * power) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hsmall)
          (Real.rpow_nonneg (by linarith) _)
    have hpointQuarter := hpointRoot (1 / 4) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hpointHalf := hpointRoot (1 / 2) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hlineQuarter : (lineError error ratio) ^ (1 / 4 : ℝ) ≤
        lineConstant ^ (1 / 4 : ℝ) * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlineValue.1 hlineValue.2 (by norm_num)
        _ = lineConstant ^ (1 / 4 : ℝ) *
            (error ^ errorPower + ratio ^ ratioPower) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ (1 / 4 : ℝ) *
            ((error ^ errorPower) ^ (1 / 4 : ℝ) +
              (ratio ^ ratioPower) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror _)
              (Real.rpow_nonneg hratio _) (by norm_num) (by norm_num))
            (Real.rpow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← Real.rpow_mul herror, ← Real.rpow_mul hratio]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          apply add_le_add _ (by simp [div_eq_mul_inv])
          apply Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
          have hsmall : finalPower ≤ errorPower / 4 :=
            (min_le_right _ _).trans (min_le_left _ _)
          linarith
    have herrorQuarter : error ^ (1 / 4 : ℝ) ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
        ((min_le_right _ _).trans (min_le_right _ _))
    have hsqrt : Real.sqrt dimension ≤ dimension := by
      nlinarith [Real.sq_sqrt hdimensionNonneg, Real.sqrt_nonneg dimension]
    have hsum : (pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
        ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ)) ≤
        dimension * (coefficient * (error ^ finalPower + ratio ^ (ratioPower / 4))) := by
      have hrootNonneg : 0 ≤ (lineError error ratio) ^ (1 / 4 : ℝ) +
          (pointError error) ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ) :=
        add_nonneg (add_nonneg (Real.rpow_nonneg hlineValue.1 _)
          (Real.rpow_nonneg hpointValue.1 _)) (Real.rpow_nonneg herror _)
      have hrootSum := add_le_add (add_le_add hlineQuarter hpointQuarter) herrorQuarter
      have hscaled := mul_le_mul hsqrt hrootSum hrootNonneg hdimensionNonneg
      have hpointScaled := mul_le_mul_of_nonneg_right hdimension
        (Real.rpow_nonneg hpointValue.1 (1 / 2 : ℝ))
      dsimp [coefficient]
      nlinarith [mul_nonneg hdimensionNonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 2 : ℝ))
          hratioTerm),
        mul_nonneg hdimensionNonneg
          (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 4 : ℝ))
            hratioTerm),
        mul_le_mul_of_nonneg_left hpointHalf hdimensionNonneg,
        mul_nonneg hdimensionNonneg hratioTerm]
    refine (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hsum hconstant).trans ?_)
    dsimp [finalConstant]
    nlinarith [mul_nonneg hdimensionNonneg (add_nonneg herrorTerm hratioTerm)]
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge herrorOne) hfinalPower.le
    have hsumOne : 1 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
        (add_nonneg herrorTerm hratioTerm)]
    nlinarith [mul_nonneg (show 0 ≤ dimension - 1 by linarith)
      (show 0 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) by linarith)]

/-- Conditional directly indexed construction of the extended-line measurements with
the error expression `poly(m^2 * epsilon, md / q)` printed in `lem:qld-4-13`, paper
lines 1020--1034. This is an auxiliary obligation, not the source-facing statement.

The printed proof does not establish this error form: its first route gives
`m * poly(epsilon, md / q)`, while its second route gives a different bound and
uses a joint-law decomposition absent from the subline lemma.  The discrepancy is
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`rem:qld-4-13-source-defects` in the blueprint. `ExtendedLinesWitness` uses the
directly indexed question carrier and line-point law documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, and the completed answer
alphabet documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Their conversion to the source's verifier game remains open. This declaration takes
an already constructed point witness; the companion obligation below supplies that
witness existentially. Its polynomial point-error function is fixed before the
output error is chosen, as in `exists_combinedLinesWitness_ofPointsWitness`.
This removes the unrestricted supplied-error omission tracked by issue #118;
it does not discharge the separate printed-error obligation.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_ofPointsWitness (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε)),
        Nonempty (ExtendedLinesWitness S points
          (deltaCombine ((P.m : ℝ) ^ 2 * ε)
            ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-! The following directly indexed obligation supplies the point witness from
`lem:qld-4-10` rather than taking it as an external hypothesis. -/

/-- Directly indexed extended-line obligation with the numerical error expression
printed in `lem:qld-4-13`, paper lines 1020--1034.

The `_ofPointsWitness` companion assumes a point witness, while this declaration
supplies one existentially. Both declarations use the directly indexed questions,
law, and completed answer alphabet, so neither is the source-facing paper statement.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (ExtendedLinesWitness S points
              (deltaCombine ((P.m : ℝ) ^ 2 * ε)
                ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaCombine, hdeltaCombine, hlines⟩ :=
    exists_extendedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, deltaCombine, hdeltaCombine, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩

/-- Construction of the extended-line measurements with the estimate actually
delivered by the first proof route, `C * m * poly(epsilon, md / q)`.

This is an established auxiliary form of the argument, not the source-labelled
`lem:qld-4-13`; it must not be advertised as that theorem. The source discrepancy
is analyzed in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. As in the
companion directly indexed declaration, the extended questions use the directly
indexed line-space construction. This conditional declaration takes an already
constructed point witness with its polynomial error function fixed before the
line error is chosen; the obligation below supplies it existentially. The first
route's joint-overlap estimate is proved by `subline_joint_overlap_near_one`.
The actual conditional POVM and its axis-degree support are constructed by
`SubLineWitness.extendedMeasurement` and `SubLineWitness.extendedMeasurement_axis_degree`.
`SubLineWitness.completedPoint_effect_le` gives the point-effect comparison for either player.
`SubLineWitness.extended_consistencyDefect_le` integrates the placed overlaps on
both player orientations, and `extended_first_player_deficit_le` proves the actual
first-player estimate. The second-player ordered-product replacement is proved by
`SubLineWitness.paired_ordered_overlap_gap_le`; its X-removal and Z-deficit estimates
remain. The ten-session ordinary budget is exhausted; the self-contained escalation
packet is in `audits/2026-09-06-issue118-point-error-dependency.md`. Relating
its game to the source's seed-bearing game requires the transport and soundness
obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_established_ofPointsWitness (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
          (points : CombinedPointsWitness S (deltaQ ε)),
          Nonempty (ExtendedLinesWitness S points
            (C * (P.m : ℝ) *
              deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-- Directly indexed construction for the auxiliary estimate
`C * m * poly(epsilon, md / q)`. This has the same directly indexed estimate as
`exists_extendedLinesWitness_established_ofPointsWitness`, with the point witness
existentially supplied rather than assumed.

Its question carrier and line-point law are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; its `Option`-completed answer
alphabet is documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Transport to `lem:qld-4-13` must convert this completed comparison to the source's
sum over field answers, including degenerate zero-direction singleton lines.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness_established :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
          ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
            ∃ points : CombinedPointsWitness S (deltaQ ε),
              Nonempty (ExtendedLinesWitness S points
                (C * (P.m : ℝ) *
                  deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨C, hC, deltaCombine, hdeltaCombine, hlines⟩ :=
    exists_extendedLinesWitness_established_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, C, hC, deltaCombine, hdeltaCombine,
    fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩

/-- Construction of the projective global polynomial-pair measurements from
`lem:qld-4-7`, paper lines 1267--1274.  The statement has the source's universal
constants and contains no divisibility hypothesis or residual construction input.

The argument uses low-degree soundness at dimension `2 * m + 2`.  The current
direct carrier realizes the required dimension without assuming
`2 * m + 2 ∣ q`, but it does not itself prove the game-correspondence and
auxiliary-parameter estimates required by the soundness import; those obligations
are exposed by `exists_direct_ld_soundness` and documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.  Absorption of the established
combined-lines prefactor into the final universal constants is to use
`deltaQld_mono` on its stated source parameter domain.
-/
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 < ε →
        ∀ S : ProjectiveSetting P ε,
          Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  sorry

end

end MIPStarRE.QPBT
