module

public import MIPStarRE.QPBT.Observables.WinImplications.LowDegree
public import MIPStarRE.QPBT.Observables.WinImplications.Interchange
public import MIPStarRE.QPBT.Observables.Defs
public import MIPStarRE.QPBT.Combining.ActualErrorBounds
public import MIPStarRE.QPBT.Test.Soundness.NaimarkAssembly
public import MIPStarRE.QPBT.Test.Soundness.EpsReduction

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Completing the Pauli-answer measurement changes only outcome zero, where
it adds the total effect of malformed answers. -/
theorem completedPauliEffect_eq_raw_add_wrongForm {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) (u : PauliRegister P) :
    (M.postprocess pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) +
        if u = 0 then ProjectiveSetting.wrongFormEffect (.pauli W) M else 0 := by
  classical
  rw [Measurement.postprocess_effect, ProjectiveSetting.wrongFormEffect,
    Finset.sum_filter]
  by_cases hu : u = 0
  · subst u
    simp only [ite_true]
    calc
      (∑ answer, if pauliAnswerOrZero answer = 0 then M.effect answer else 0) =
          ∑ answer, ((if answer = .pauliOutcome 0 then M.effect answer else 0) +
            (if validPauliAnswer (.pauli W) answer = false then M.effect answer else 0)) := by
        apply Finset.sum_congr rfl
        intro answer _
        cases answer <;> simp [pauliAnswerOrZero, validPauliAnswer] <;> rfl
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
  · simp only [hu, ite_false, add_zero]
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [pauliAnswerOrZero]
    · intro answer _ hanswer
      have hzero : (0 : PauliRegister P) ≠ u := by
        simpa [eq_comm] using hu
      cases answer <;> simp_all [pauliAnswerOrZero]
    · simp

namespace WinImplications

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
    rw [← rejectionEventAverage_eq_one_sub_value S]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  rw [havg]
  linarith

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
        (Fintype.card PauliEdge : ℝ) *
          avgOver (uniformDistribution (PauliEdge × PauliSpace P))
            (fun ez => pauliRejectionAt S ez.1 ez.2) := by
      exact avgOver_uniform_fixed_le_card_mul_prod _
        (fun edge z => pauliRejectionAt_nonneg S edge z) e
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error_of_win S hwin)
        (Nat.cast_nonneg _)

end WinImplications

open DistanceCalculus

/-- Alice's malformed Pauli-answer mass is bounded by rejection on the
Pauli-to-point edge. -/
theorem wrongFormPauliMass_alice_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1) =
          aliceEventWeight S (pauliQuestion P W)
            (fun a => validPauliAnswer (.pauli W) a = false) := by
      unfold ProjectiveSetting.wrongFormEffect aliceEventWeight
      rw [heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : validPauliAnswer (.pauli W) a = false
      · simp [ha, stateQForm, aliceOutcomeWeight]
      · simp [ha]
    rw [hmass]
    rw [← outcome_event_weight_left_eq S (pauliQuestion P W)
      ((.point W), pauliCL P (.point W) z)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pauliPointEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b ha
    simp [pauliWinPredicate, ha]
  calc
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1)) := by
      symm
      exact avgOver_uniform_const _
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W)) := by
      exact avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

/-- Bob's malformed Pauli-answer mass is bounded by rejection on the
point-to-Pauli edge. -/
theorem wrongFormPauliMass_bob_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron 1
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W)))) =
          bobEventWeight S (pauliQuestion P W)
            (fun b => validPauliAnswer (.pauli W) b = false) := by
      unfold ProjectiveSetting.wrongFormEffect bobEventWeight
      rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : validPauliAnswer (.pauli W) b = false
      · simp [hb, stateQForm, bobOutcomeWeight]
      · simp [hb]
    rw [hmass]
    rw [← outcome_event_weight_right_eq S
      ((.point W), pauliCL P (.point W) z) (pauliQuestion P W)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pointPauliEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b hb
    simp [pauliWinPredicate, hb]
  calc
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W))))) := by
      symm
      exact avgOver_uniform_const _
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W)) := by
      exact avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

private theorem raw_transfer_liftedAEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA M =
      heteroKron (conjIsometry φA M) (1 : Op (ιB' × PauliRegister P)) := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_transfer_liftedBEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB M =
      heteroKron (1 : Op (ιA' × PauliRegister P)) (conjIsometry φB M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_transfer_liftedAEffect_add {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (A B : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA (A + B) =
      liftedAEffect S φA A + liftedAEffect S φA B := by
  rw [raw_transfer_liftedAEffect_eq_tensor, raw_transfer_liftedAEffect_eq_tensor,
    raw_transfer_liftedAEffect_eq_tensor, ← heteroKron_add_left]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

private theorem raw_transfer_liftedBEffect_add {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (A B : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB (A + B) =
      liftedBEffect S φB A + liftedBEffect S φB B := by
  rw [raw_transfer_liftedBEffect_eq_tensor, raw_transfer_liftedBEffect_eq_tensor,
    raw_transfer_liftedBEffect_eq_tensor, ← heteroKron_add_right]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

/-- The prescribed raw Pauli-answer effects form a square-summable subfamily
of the full answer POVM. This is the family hypothesis needed for the universal
raw-distance cap in paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`. -/
theorem raw_pauli_effects_sum_adjoint_mul_le_one {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι) :
    ∑ u : PauliRegister P,
        (M.effect (.pauliOutcome u))ᴴ * M.effect (.pauliOutcome u) ≤ 1 := by
  classical
  let f : PauliRegister P → PauliAnswer P := fun u => .pauliOutcome u
  have hf : Set.InjOn f (Finset.univ : Finset (PauliRegister P)) := by
    intro u _ v _ huv
    exact PauliAnswer.pauliOutcome.inj huv
  calc
    ∑ u : PauliRegister P,
        (M.effect (.pauliOutcome u))ᴴ * M.effect (.pauliOutcome u) =
        ∑ a ∈ Finset.image f (Finset.univ : Finset (PauliRegister P)),
          (M.effect a)ᴴ * M.effect a := by
            symm
            rw [Finset.sum_image hf]
    _ ≤ ∑ a : PauliAnswer P, (M.effect a)ᴴ * M.effect a := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun a _ _ => star_mul_self_nonneg (M.effect a))
    _ ≤ 1 := measurement_sum_adjoint_mul_le_one M

private theorem raw_sum_conj_isometry_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) ≤ 1 := by
  have heq (a : α) : (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) =
      MagicSquareRigidity.isometryMatrix φ * ((N a)ᴴ * N a) *
        (MagicSquareRigidity.isometryMatrix φ)ᴴ := by
    simp only [MagicSquareRigidity.conjIsometry_eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (MagicSquareRigidity.isometryMatrix φ)ᴴ
      (MagicSquareRigidity.isometryMatrix φ),
      MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  simp_rw [heq]
  have hsum : (∑ a, MagicSquareRigidity.isometryMatrix φ * ((N a)ᴴ * N a) *
      (MagicSquareRigidity.isometryMatrix φ)ᴴ) =
      MagicSquareRigidity.isometryMatrix φ * (∑ a, (N a)ᴴ * N a) *
        (MagicSquareRigidity.isometryMatrix φ)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [hsum]
  calc
    _ ≤ MagicSquareRigidity.isometryMatrix φ * (1 : Op ι) *
        (MagicSquareRigidity.isometryMatrix φ)ᴴ := by
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hN).mul_mul_conjTranspose_same
        (MagicSquareRigidity.isometryMatrix φ) using 1
      all_goals simp [Matrix.mul_sub, Matrix.sub_mul]
    _ ≤ 1 := by
      rw [Matrix.mul_one]
      exact MagicSquareRigidity.isometryMatrix_mul_conjTranspose_le_one φ

private theorem raw_left_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (N a) (1 : Op κ))ᴴ * heteroKron (N a) 1 ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.leftTensor (ι₂ := κ) (N a))ᴴ *
    MIPStarRE.LDT.leftTensor (N a) ≤ 1
  have h := MIPStarRE.LDT.leftTensor_mono (ι₂ := κ) hN
  simpa only [← MIPStarRE.LDT.leftTensor_finset_sum,
    MIPStarRE.LDT.leftTensor_one, MIPStarRE.LDT.leftTensor_conjTranspose,
    MIPStarRE.LDT.leftTensor_mul_leftTensor] using h

private theorem raw_right_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op κ) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (1 : Op ι) (N a))ᴴ * heteroKron 1 (N a) ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.rightTensor (ι₁ := ι) (N a))ᴴ *
    MIPStarRE.LDT.rightTensor (N a) ≤ 1
  have h := MIPStarRE.LDT.rightTensor_mono (ι₁ := ι) hN
  simpa only [← MIPStarRE.LDT.rightTensor_finset_sum,
    MIPStarRE.LDT.rightTensor_one, MIPStarRE.LDT.rightTensor_conjTranspose,
    MIPStarRE.LDT.rightTensor_mul_rightTensor] using h

/-- The canonical Pauli projectors packaged as a complete measurement for the
universal raw-distance estimate. -/
private def rawIdealPauliMeasurement (P : AdmissibleParams) (W : PauliKind) :
    Measurement (PauliRegister P) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliProj W) (fun h => (posSemidef_pauliProj W h).nonneg)
    (sum_pauliProj_eq_one W)

private theorem raw_pauli_proj_on_a_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron (heteroKron 1 (pauliProj W h)) 1 := by
  ext i j
  simp [pauliProjOnA'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem raw_pauli_proj_on_b_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron 1 (heteroKron 1 (pauliProj W h)) := by
  ext i j
  simp [pauliProjOnB'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem raw_pauli_proj_on_a_sum_adjoint_mul_le_one (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) :
    ∑ h, (pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnA'' P W h ≤ 1 := by
  simp only [raw_pauli_proj_on_a_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (leftPlacedMeasurement (rightPlacedMeasurement (rawIdealPauliMeasurement P W)))

private theorem raw_pauli_proj_on_b_sum_adjoint_mul_le_one (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) :
    ∑ h, (pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnB'' P W h ≤ 1 := by
  simp only [raw_pauli_proj_on_b_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (rightPlacedMeasurement (rightPlacedMeasurement (rawIdealPauliMeasurement P W)))

private theorem ideal_state_norm_one {P : AdmissibleParams}
    {S : Strategy (pauliBasisTest P)} (w : PauliSoundnessWitness P S) :
    ‖idealState P w.aux‖ = 1 := by
  change ‖reindexState prodShuffle (vecTensor w.aux (eprState (PauliRegister P)))‖ = 1
  rw [reindexState_norm_eq, vecTensor_norm_eq, w.aux_norm, eprState_norm, mul_one]

/-- Any Pauli soundness witness compares two unit vectors, so its state distance
is at most two. This is the assumption-free saturation bound used for the large
error branch of paper `thm:pauli`. -/
theorem pauli_soundness_state_distance_le_two (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S) :
    ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ 2 := by
  calc
    ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
        ‖isometryTensor w.φA w.φB S.ψ‖ + ‖idealState P w.aux‖ := norm_sub_le _ _
    _ = 1 + 1 := by
      rw [MagicSquareRigidity.norm_isometryTensor, S.ψ_norm, ideal_state_norm_one]
    _ = 2 := by norm_num

/-- Alice's raw prescribed-answer family has squared distance at most four from
the ideal Pauli family for every strategy and every soundness witness. No
winning or projectivity assumption is used. -/
theorem raw_pauli_operator_distance_a_le_four (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) : rawPauliOperatorDistanceA P S w W ≤ 4 := by
  have hraw := raw_pauli_effects_sum_adjoint_mul_le_one (S.A (pauliQuestion P W))
  have hA : ∑ u : PauliRegister P,
      (liftedAEffect S (ιB' := w.ιB') w.φA
        ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)))ᴴ *
      liftedAEffect S w.φA
        ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) ≤ 1 := by
    simp only [raw_transfer_liftedAEffect_eq_tensor]
    exact raw_left_sum_adjoint_mul_le_one _
      (raw_sum_conj_isometry_adjoint_mul_le_one w.φA _ hraw)
  unfold rawPauliOperatorDistanceA
  exact sum_norm_sub_apply_sq_le_four _ _ _ (ideal_state_norm_one w) hA
    (raw_pauli_proj_on_a_sum_adjoint_mul_le_one P W)

/-- Bob's raw prescribed-answer family satisfies the same universal squared
distance cap as Alice's, on the same normalized ideal state. -/
theorem raw_pauli_operator_distance_b_le_four (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) : rawPauliOperatorDistanceB P S w W ≤ 4 := by
  have hraw := raw_pauli_effects_sum_adjoint_mul_le_one (S.B (pauliQuestion P W))
  have hB : ∑ u : PauliRegister P,
      (liftedBEffect S (ιA' := w.ιA') w.φB
        ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)))ᴴ *
      liftedBEffect S w.φB
        ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) ≤ 1 := by
    simp only [raw_transfer_liftedBEffect_eq_tensor]
    exact raw_right_sum_adjoint_mul_le_one _
      (raw_sum_conj_isometry_adjoint_mul_le_one w.φB _ hraw)
  unfold rawPauliOperatorDistanceB
  exact sum_norm_sub_apply_sq_le_four _ _ _ (ideal_state_norm_one w) hB
    (raw_pauli_proj_on_b_sum_adjoint_mul_le_one P W)

private theorem wrongFormEffect_eq_validity_effect {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) :
    ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (validPauliAnswer (.pauli W))).effect false := by
  rw [ProjectiveSetting.wrongFormEffect, Measurement.postprocess_effect]

private theorem wrongFormEffect_ideal_norm_alice_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤ r) :
    ‖applyOperatorToState
        (liftedAEffect S w.φA
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let M : Measurement (PauliAnswer P) S.ιA := S.A (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := liftedAEffect S (ιB' := w.ιB') w.φA E
  let theta := isometryTensor w.φA w.φB S.ψ
  let Delta := idealState P w.aux
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : E = N.effect false := by
    exact wrongFormEffect_eq_validity_effect M W
  have hEcontr : Eᴴ * E ≤ 1 := by
    rw [hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]
    rw [raw_transfer_liftedAEffect_eq_tensor]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φA hEcontr)
  have htheta : ‖applyOperatorToState Q theta‖ ^ 2 ≤ r := by
    dsimp only [Q, theta]
    rw [raw_transfer_liftedAEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor]
    have hEpos : 0 ≤ E := by rw [hE]; exact N.pos false
    have hEle : E ≤ 1 := by rw [hE]; exact measurement_effect_le_one N false
    have hKpos : 0 ≤ heteroKron E (1 : Op S.ιB) :=
      kronecker_nonneg hEpos (by simp)
    have hKle : heteroKron E (1 : Op S.ιB) ≤ 1 := by
      rw [← Matrix.one_kronecker_one]
      exact kronecker_mono_left hEle (by simp)
    rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKH : (heteroKron E (1 : Op S.ιB))ᴴ = heteroKron E 1 :=
      (Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq
    rw [hKH]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      hmass
  have hdecomp : applyOperatorToState Q Delta =
      applyOperatorToState Q (Delta - theta) + applyOperatorToState Q theta := by
    simp [applyOperatorToState]
  rw [hdecomp]
  have hfirst : ‖applyOperatorToState Q (Delta - theta)‖ ≤ δ := by
    exact (MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans (by
      rw [norm_sub_rev]
      exact hstate)
  have htri := norm_add_le (applyOperatorToState Q (Delta - theta))
    (applyOperatorToState Q theta)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hfirstsq := pow_le_pow_left₀
    (norm_nonneg (applyOperatorToState Q (Delta - theta))) hfirst 2
  nlinarith [sq_nonneg (‖applyOperatorToState Q (Delta - theta)‖ -
    ‖applyOperatorToState Q theta‖)]

private theorem wrongFormEffect_ideal_norm_bob_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤ r) :
    ‖applyOperatorToState
        (liftedBEffect S w.φB
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let M := S.B (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := liftedBEffect S (ιA' := w.ιA') w.φB E
  let theta := isometryTensor w.φA w.φB S.ψ
  let Delta := idealState P w.aux
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : E = N.effect false := by
    exact wrongFormEffect_eq_validity_effect M W
  have hEcontr : Eᴴ * E ≤ 1 := by
    rw [hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]
    rw [raw_transfer_liftedBEffect_eq_tensor]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φB hEcontr)
  have htheta : ‖applyOperatorToState Q theta‖ ^ 2 ≤ r := by
    dsimp only [Q, theta]
    rw [raw_transfer_liftedBEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor]
    have hEpos : 0 ≤ E := by rw [hE]; exact N.pos false
    have hEle : E ≤ 1 := by rw [hE]; exact measurement_effect_le_one N false
    have hKpos : 0 ≤ heteroKron (1 : Op S.ιA) E :=
      kronecker_nonneg (by simp) hEpos
    have hKle : heteroKron (1 : Op S.ιA) E ≤ 1 := by
      rw [← Matrix.one_kronecker_one]
      exact kronecker_le_kronecker_right_one (by simp) hEle
    rw [MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKH : (heteroKron (1 : Op S.ιA) E)ᴴ = heteroKron 1 E :=
      (Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq
    rw [hKH]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      hmass
  have hdecomp : applyOperatorToState Q Delta =
      applyOperatorToState Q (Delta - theta) + applyOperatorToState Q theta := by
    simp [applyOperatorToState]
  rw [hdecomp]
  have hfirst : ‖applyOperatorToState Q (Delta - theta)‖ ≤ δ := by
    exact (MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans (by
      rw [norm_sub_rev]
      exact hstate)
  have htri := norm_add_le (applyOperatorToState Q (Delta - theta))
    (applyOperatorToState Q theta)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hfirstsq := pow_le_pow_left₀
    (norm_nonneg (applyOperatorToState Q (Delta - theta))) hfirst 2
  nlinarith [sq_nonneg (‖applyOperatorToState Q (Delta - theta)‖ -
    ‖applyOperatorToState Q theta‖)]

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M : Measurement (PauliAnswer P) S.ιA := S.A (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖applyOperatorToState (liftedAEffect S w.φA E)
    (idealState P w.aux)‖ ^ 2
  have hmass := wrongFormPauliMass_alice_le_error S hwin W
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε := by
    simpa only [bad, E, M, mul_assoc] using
      wrongFormEffect_ideal_norm_alice_le S w W δ _ hstate hmass
  have hpoint (u : PauliRegister P) :
      ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 ≤
        2 * ‖applyOperatorToState
          (liftedAEffect S w.φA
              ((M.postprocess pauliAnswerOrZero).effect u) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl, completedPauliEffect_eq_raw_add_wrongForm M W 0]
      simp only [ite_true]
      have hvec :
          applyOperatorToState
              (liftedAEffect S w.φA
                  (M.effect (.pauliOutcome 0)) -
                pauliProjOnA'' P W 0) (idealState P w.aux) =
            applyOperatorToState
                (liftedAEffect S w.φA
                    (M.effect (.pauliOutcome 0) + E) -
                  pauliProjOnA'' P W 0) (idealState P w.aux) -
              applyOperatorToState (liftedAEffect S w.φA E)
                (idealState P w.aux) := by
        rw [raw_transfer_liftedAEffect_add]
        simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := norm_sub_le
        (applyOperatorToState
          (liftedAEffect S w.φA
              (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnA'' P W 0) (idealState P w.aux))
        (applyOperatorToState (liftedAEffect S w.φA E) (idealState P w.aux))
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖applyOperatorToState
          (liftedAEffect S w.φA
              (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnA'' P W 0) (idealState P w.aux)‖ -
          ‖applyOperatorToState (liftedAEffect S w.φA E) (idealState P w.aux)‖)]
    · rw [if_neg hu, completedPauliEffect_eq_raw_add_wrongForm M W u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg
        ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖]
  unfold rawPauliOperatorDistanceA pauliOperatorDistanceA
  change (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) - pauliProjOnA'' P W u)
        (idealState P w.aux)‖ ^ 2) ≤
    2 * (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedAEffect S w.φA ((M.postprocess pauliAnswerOrZero).effect u) -
          pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) +
      4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε
  calc
    (∑ u : PauliRegister P,
        ‖applyOperatorToState
          (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
            pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) ≤
        ∑ u : PauliRegister P,
          (2 * ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) + 2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedAEffect S w.φA
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2) +
          2 * (2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε) := by
      linarith
    _ = _ := by
      ring

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M : Measurement (PauliAnswer P) S.ιB := S.B (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖applyOperatorToState (liftedBEffect S w.φB E)
    (idealState P w.aux)‖ ^ 2
  have hmass := wrongFormPauliMass_bob_le_error S hwin W
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε := by
    simpa only [bad, E, M, mul_assoc] using
      wrongFormEffect_ideal_norm_bob_le S w W δ _ hstate hmass
  have hpoint (u : PauliRegister P) :
      ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 ≤
        2 * ‖applyOperatorToState
          (liftedBEffect S w.φB
              ((M.postprocess pauliAnswerOrZero).effect u) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl, completedPauliEffect_eq_raw_add_wrongForm M W 0]
      simp only [ite_true]
      have hvec :
          applyOperatorToState
              (liftedBEffect S w.φB (M.effect (.pauliOutcome 0)) -
                pauliProjOnB'' P W 0) (idealState P w.aux) =
            applyOperatorToState
                (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
                  pauliProjOnB'' P W 0) (idealState P w.aux) -
              applyOperatorToState (liftedBEffect S w.φB E)
                (idealState P w.aux) := by
        rw [raw_transfer_liftedBEffect_add]
        simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := norm_sub_le
        (applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnB'' P W 0) (idealState P w.aux))
        (applyOperatorToState (liftedBEffect S w.φB E) (idealState P w.aux))
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            pauliProjOnB'' P W 0) (idealState P w.aux)‖ -
          ‖applyOperatorToState (liftedBEffect S w.φB E) (idealState P w.aux)‖)]
    · rw [if_neg hu, completedPauliEffect_eq_raw_add_wrongForm M W u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg
        ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖]
  unfold rawPauliOperatorDistanceB pauliOperatorDistanceB
  change (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) - pauliProjOnB'' P W u)
        (idealState P w.aux)‖ ^ 2) ≤
    2 * (∑ u : PauliRegister P,
      ‖applyOperatorToState
        (liftedBEffect S w.φB ((M.postprocess pauliAnswerOrZero).effect u) -
          pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) +
      4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε
  calc
    (∑ u : PauliRegister P,
        ‖applyOperatorToState
          (liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) ≤
        ∑ u : PauliRegister P,
          (2 * ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) + 2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (liftedBEffect S w.φB
                ((M.postprocess pauliAnswerOrZero).effect u) -
              pauliProjOnB'' P W u) (idealState P w.aux)‖ ^ 2) +
          2 * (2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε) := by
      linarith
    _ = _ := by
      ring

end

end MIPStarRE.QPBT
