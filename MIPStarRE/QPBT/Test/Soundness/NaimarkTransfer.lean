import MIPStarRE.QPBT.Games.MeasurementCompression
import MIPStarRE.QPBT.Test.Soundness.IdealPauli
import MIPStarRE.QPBT.Observables.Defs

/-!
# Compression in Pauli soundness

The genuine Naimark dilation preserves the prepared state and compresses to
the original effects, including the answer postprocessing of the Pauli test.
Composing local witness isometries therefore inserts two range projections.

## References

Formalization support for paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and the final transfer at `14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The distinction from ancilla intertwining is recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex` and issue #529.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

variable {P : AdmissibleParams}

/-- The two local Naimark dilations of the supplied strategy. -/
def pauliNaimarkStrategy (S : Strategy (pauliBasisTest P)) :
    Strategy (pauliBasisTest P) :=
  paddedStrategy S none none
    (fun x => dilatedMeasurement (default : PauliAnswer P) (S.A x))
    (fun y => dilatedMeasurement (default : PauliAnswer P) (S.B y))

/-- The constructed dilation is projective on both local spaces. -/
theorem pauliNaimarkStrategy_projective (S : Strategy (pauliBasisTest P)) :
    (pauliNaimarkStrategy S).IsProjective :=
  paddedStrategy_isProjective S none none _ _
    (fun x => dilatedMeasurement_isProjective (default : PauliAnswer P) (S.A x))
    (fun y => dilatedMeasurement_isProjective (default : PauliAnswer P) (S.B y))

/-- The supplied strategy and its dilation have exactly the same game value. -/
theorem pauliNaimarkStrategy_value (S : Strategy (pauliBasisTest P)) :
    (pauliNaimarkStrategy S).value = S.value :=
  paddedStrategy_value S none none _ _
    (fun x a => dilatedMeasurement_compression (default : PauliAnswer P) a (S.A x))
    (fun y b => dilatedMeasurement_compression (default : PauliAnswer P) b (S.B y))

/-- The concrete projective setting produced from a supplied successful strategy.
Both projectivity and its winning premise follow from the proved dilation. -/
def pauliNaimarkSetting (S : Strategy (pauliBasisTest P)) {epsilon : ℝ}
    (hwin : 1 - epsilon ≤ S.value) : ProjectiveSetting P epsilon where
  toStrategy := pauliNaimarkStrategy S
  isProjective := pauliNaimarkStrategy_projective S
  win := hwin.trans_eq (pauliNaimarkStrategy_value S).symm

/-- Both ground embeddings prepare the actual dilated state exactly. -/
theorem pauliNaimarkStrategy_state (S : Strategy (pauliBasisTest P)) :
    isometryTensor (naimarkEmbedding S.ιA (pauliBasisTest P).AnswerA)
      (naimarkEmbedding S.ιB (pauliBasisTest P).AnswerB) S.ψ =
        (pauliNaimarkStrategy S).ψ := by
  ext p
  change naimarkDilatedState (pauliBasisTest P).AnswerA S.ψ p = _
  rw [naimarkDilatedState_apply]
  simp only [pauliNaimarkStrategy, paddedStrategy, padState, ite_and]
  rfl

/-- Alice's actual Pauli readout compresses to the original postprocessed POVM. -/
theorem pauliNaimarkStrategy_compression_alice
    (S : Strategy (pauliBasisTest P)) (W : PauliKind) (h : PauliRegister P) :
    naimarkCompression
      ((((pauliNaimarkStrategy S).A (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h) =
      (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) := by
  have hc := congrArg (fun M : Measurement (PauliRegister P) S.ιA => M.effect h)
    ((dilatedMeasurement (default : PauliAnswer P)
      (S.A (pauliQuestion P W))).compressAt_postprocess
      none pauliAnswerOrZero)
  rw [Measurement.compressAt_dilatedMeasurement] at hc
  exact hc

/-- Bob's actual Pauli readout compresses to the original postprocessed POVM. -/
theorem pauliNaimarkStrategy_compression_bob
    (S : Strategy (pauliBasisTest P)) (W : PauliKind) (h : PauliRegister P) :
    naimarkCompression
      ((((pauliNaimarkStrategy S).B (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h) =
      (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) := by
  have hc := congrArg (fun M : Measurement (PauliRegister P) S.ιB => M.effect h)
    ((dilatedMeasurement (default : PauliAnswer P)
      (S.B (pauliQuestion P W))).compressAt_postprocess
      none pauliAnswerOrZero)
  rw [Measurement.compressAt_dilatedMeasurement] at hc
  exact hc

/-- Pull back the supplied witness isometries along the actual ground embeddings.
The auxiliary state and both auxiliary spaces are preserved. -/
def PauliSoundnessWitness.ofNaimark {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) :
    PauliSoundnessWitness P S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA.comp (naimarkEmbedding S.ιA (pauliBasisTest P).AnswerA)
  φB := w.φB.comp (naimarkEmbedding S.ιB (pauliBasisTest P).AnswerB)
  aux := w.aux
  aux_norm := w.aux_norm

/-- Pullback preserves the complete, unsquared state error exactly. -/
theorem PauliSoundnessWitness.ofNaimark_state_error
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) :
    ‖isometryTensor w.ofNaimark.φA w.ofNaimark.φB S.ψ -
      idealState P w.ofNaimark.aux‖ =
    ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ - idealState P w.aux‖ := by
  dsimp only [PauliSoundnessWitness.ofNaimark]
  erw [isometryTensor_comp, pauliNaimarkStrategy_state]
  rfl

/-- Coordinate compression is precisely multiplication by the adjoint of the
actual ground embedding on the left and by that embedding on the right. -/
theorem naimarkCompression_eq_adjoint {ι α : Type}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (N : Op (ι × Option α)) :
    naimarkCompression N =
      (isometryMatrix (naimarkEmbedding ι α))ᴴ * N *
        isometryMatrix (naimarkEmbedding ι α) := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    isometryMatrix_apply, naimarkCompression_apply, eq_comm]

/-- Compression followed by isometry conjugation inserts the ground projection
on both sides; Naimark dilation supplies no intertwining identity. -/
theorem conjIsometry_compressed {ι α κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : Op (ι × Option α)) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) (naimarkCompression N) =
      conjIsometry φ (groundProjection ι α) * conjIsometry φ N *
        conjIsometry φ (groundProjection ι α) := by
  rw [conjIsometry_comp_naimarkEmbedding, naimarkInflation_naimarkCompression,
    conjIsometry_mul, conjIsometry_mul]

private theorem liftedAEffect_eq_tensor {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φ M = heteroKron (conjIsometry φ M) 1 := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem liftedBEffect_eq_tensor {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φ M = heteroKron 1 (conjIsometry φ M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

/-- The original Alice readout is exactly `Q N Q` in the witness space. -/
theorem PauliSoundnessWitness.ofNaimark_compression_alice
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S))
    (W : PauliKind) (h : PauliRegister P) :
    liftedAEffect S (ιB' := w.ιB') w.ofNaimark.φA
        (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) =
      liftedAEffect (pauliNaimarkStrategy S) w.φA
          (groundProjection S.ιA (PauliAnswer P)) *
        liftedAEffect (pauliNaimarkStrategy S) w.φA
          ((((pauliNaimarkStrategy S).A (pauliQuestion P W)).postprocess
            pauliAnswerOrZero).effect h) *
        liftedAEffect (pauliNaimarkStrategy S) w.φA
          (groundProjection S.ιA (PauliAnswer P)) := by
  have hc := conjIsometry_compressed w.φA
    ((((pauliNaimarkStrategy S).A (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).effect h)
  rw [pauliNaimarkStrategy_compression_alice] at hc
  dsimp +instances only [PauliSoundnessWitness.ofNaimark, pauliNaimarkStrategy,
    paddedStrategy] at hc ⊢
  have hh := congrArg (fun M => heteroKron M (1 : Op (w.ιB' × PauliRegister P))) hc
  simp only [liftedAEffect_eq_tensor, heteroKron_mul, Matrix.one_mul] at hh ⊢
  exact hh

/-- The original Bob readout is exactly `Q N Q` in the witness space. -/
theorem PauliSoundnessWitness.ofNaimark_compression_bob
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S))
    (W : PauliKind) (h : PauliRegister P) :
    liftedBEffect S (ιA' := w.ιA') w.ofNaimark.φB
        (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) =
      liftedBEffect (pauliNaimarkStrategy S) w.φB
          (groundProjection S.ιB (PauliAnswer P)) *
        liftedBEffect (pauliNaimarkStrategy S) w.φB
          ((((pauliNaimarkStrategy S).B (pauliQuestion P W)).postprocess
            pauliAnswerOrZero).effect h) *
        liftedBEffect (pauliNaimarkStrategy S) w.φB
          (groundProjection S.ιB (PauliAnswer P)) := by
  have hc := conjIsometry_compressed w.φB
    ((((pauliNaimarkStrategy S).B (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).effect h)
  rw [pauliNaimarkStrategy_compression_bob] at hc
  dsimp +instances only [PauliSoundnessWitness.ofNaimark, pauliNaimarkStrategy,
    paddedStrategy] at hc ⊢
  have hh := congrArg (fun M => heteroKron (1 : Op (w.ιA' × PauliRegister P)) M) hc
  simp only [liftedBEffect_eq_tensor, heteroKron_mul, Matrix.one_mul] at hh ⊢
  exact hh

private theorem liftedA_sum_le {G : Game} (S : Strategy G)
    {α ιA' ιB' : Type} [Fintype α] [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Measurement α S.ιA) :
    ∑ a, (liftedAEffect S (ιB' := ιB') φ (M.effect a))ᴴ *
      liftedAEffect S φ (M.effect a) ≤ 1 := by
  simp only [liftedAEffect_eq_tensor]
  exact left_sum_adjoint_mul_le_one _
    (sum_conjIsometry_adjoint_mul_le_one φ M.effect (measurement_sum_adjoint_mul_le_one M))

private theorem liftedB_sum_le {G : Game} (S : Strategy G)
    {α ιA' ιB' : Type} [Fintype α] [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Measurement α S.ιB) :
    ∑ a, (liftedBEffect S (ιA' := ιA') φ (M.effect a))ᴴ *
      liftedBEffect S φ (M.effect a) ≤ 1 := by
  simp only [liftedBEffect_eq_tensor]
  exact right_sum_adjoint_mul_le_one _
    (sum_conjIsometry_adjoint_mul_le_one φ M.effect (measurement_sum_adjoint_mul_le_one M))

private theorem left_isProj {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Q : Op ι} (hQ : IsProj Q) :
    IsProj (heteroKron Q (1 : Op κ)) := by
  constructor
  · change heteroKron Q 1 * heteroKron Q 1 = heteroKron Q 1
    rw [heteroKron_mul, hQ.isIdempotentElem.eq, Matrix.one_mul]
  · change star (heteroKron Q (1 : Op κ)) = heteroKron Q 1
    simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      hQ.isSelfAdjoint.isHermitian.eq]

private theorem right_isProj {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Q : Op κ} (hQ : IsProj Q) :
    IsProj (heteroKron (1 : Op ι) Q) := by
  constructor
  · change heteroKron 1 Q * heteroKron 1 Q = heteroKron 1 Q
    rw [heteroKron_mul, hQ.isIdempotentElem.eq, Matrix.one_mul]
  · change star (heteroKron (1 : Op ι) Q) = heteroKron 1 Q
    simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      hQ.isSelfAdjoint.isHermitian.eq]

set_option maxHeartbeats 800000 in
/-- Alice's compressed distance is bounded by three times the dilated distance
plus six times the squared state error. This holds for every original strategy. -/
theorem PauliSoundnessWitness.ofNaimark_distance_alice
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) (W : PauliKind) :
    pauliOperatorDistanceA P S w.ofNaimark W ≤
      3 * pauliOperatorDistanceA P (pauliNaimarkStrategy S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedAEffect (pauliNaimarkStrategy S) (ιB' := w.ιB') w.φA
    (groundProjection S.ιA (PauliAnswer P))
  have hQ : IsProj Q := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor]
    exact left_isProj (isProj_conjIsometry w.φA (isProj_groundProjection _ _))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, applyOperatorToState_leftTensor_conjIsometry]
    have hp : (pauliNaimarkStrategy S).ψ = naimarkDilatedState (PauliAnswer P) S.ψ :=
      (pauliNaimarkStrategy_state S).symm
    rw [hp]
    erw [applyOperatorToState_leftTensor_groundProjection (PauliAnswer P) S.ψ]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnB'' P W h =
      pauliProjOnB'' P W h * Q := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, pauliProjOnB_eq_tensor]
    simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedAEffect (pauliNaimarkStrategy S) w.φA
      ((((pauliNaimarkStrategy S).A (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    (pauliProjOnA'' P W) (pauliProjOnB'' P W) Q hQ
    (liftedA_sum_le _ w.φA _) (pauliProjOnB_sum_adjoint_mul_le_one P W)
    (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) (idealState P w.aux)
    hfix (idealState_pauli_mirror P w.aux W) hcomm
  unfold pauliOperatorDistanceA
  have hc := w.ofNaimark_compression_alice W
  dsimp +instances only [PauliSoundnessWitness.ofNaimark] at hc ⊢
  simp_rw [hc]
  simpa only [norm_sub_rev] using hb

set_option maxHeartbeats 800000 in
/-- Bob's compressed distance has the same dimension-independent bound. -/
theorem PauliSoundnessWitness.ofNaimark_distance_bob
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) (W : PauliKind) :
    pauliOperatorDistanceB P S w.ofNaimark W ≤
      3 * pauliOperatorDistanceB P (pauliNaimarkStrategy S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedBEffect (pauliNaimarkStrategy S) (ιA' := w.ιA') w.φB
    (groundProjection S.ιB (PauliAnswer P))
  have hQ : IsProj Q := by
    dsimp only [Q]
    rw [liftedBEffect_eq_tensor]
    exact right_isProj (isProj_conjIsometry w.φB (isProj_groundProjection _ _))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ := by
    dsimp only [Q]
    rw [liftedBEffect_eq_tensor, applyOperatorToState_rightTensor_conjIsometry]
    have hp : (pauliNaimarkStrategy S).ψ = naimarkDilatedState (PauliAnswer P) S.ψ :=
      (pauliNaimarkStrategy_state S).symm
    rw [hp]
    erw [applyOperatorToState_rightTensor_groundProjection (PauliAnswer P) S.ψ]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnA'' P W h =
      pauliProjOnA'' P W h * Q := by
    dsimp only [Q]
    rw [liftedBEffect_eq_tensor, pauliProjOnA_eq_tensor]
    simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedBEffect (pauliNaimarkStrategy S) w.φB
      ((((pauliNaimarkStrategy S).B (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    (pauliProjOnB'' P W) (pauliProjOnA'' P W) Q hQ
    (liftedB_sum_le _ w.φB _) (pauliProjOnA_sum_adjoint_mul_le_one P W)
    (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) (idealState P w.aux)
    hfix (fun h => (idealState_pauli_mirror P w.aux W h).symm) hcomm
  unfold pauliOperatorDistanceB
  have hc := w.ofNaimark_compression_bob W
  dsimp +instances only [PauliSoundnessWitness.ofNaimark] at hc ⊢
  simp_rw [hc]
  simpa only [norm_sub_rev] using hb

/-- Alice's distance is at most four for every witness and every strategy. -/
theorem pauliOperatorDistanceA_le_four (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    pauliOperatorDistanceA P S w W ≤ 4 :=
  sum_norm_sub_sq_le_four _ _ (liftedA_sum_le S w.φA _)
    (pauliProjOnA_sum_adjoint_mul_le_one P W) (idealState P w.aux)
    ((idealState_norm P w.aux).trans w.aux_norm)

/-- Bob's distance is at most four for every witness and every strategy. -/
theorem pauliOperatorDistanceB_le_four (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : PauliKind) :
    pauliOperatorDistanceB P S w W ≤ 4 :=
  sum_norm_sub_sq_le_four _ _ (liftedB_sum_le S w.φB _)
    (pauliProjOnB_sum_adjoint_mul_le_one P W) (idealState P w.aux)
    ((idealState_norm P w.aux).trans w.aux_norm)

/-- A supplied soundness witness for the genuine projective dilation pulls
back to an arbitrary original strategy. State error remains at most `delta`;
both operator errors are at most `9 * delta`. This is blueprint
`ex:pauli-naimark-support`. The converter does not construct the upstream
witness or certify the source theorem; its discharge requires the global-pair
and extraction constructions documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #529. -/
theorem pauli_soundness_ofNaimarkWitness (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) {delta : ℝ}
    (hs : ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
      idealState P w.aux‖ ≤ delta)
    (ha : ∀ W, pauliOperatorDistanceA P (pauliNaimarkStrategy S) w W ≤ delta)
    (hb : ∀ W, pauliOperatorDistanceB P (pauliNaimarkStrategy S) w W ≤ delta) :
    ‖isometryTensor w.ofNaimark.φA w.ofNaimark.φB S.ψ -
      idealState P w.ofNaimark.aux‖ ≤ delta ∧
    (∀ W, pauliOperatorDistanceA P S w.ofNaimark W ≤ 9 * delta) ∧
    (∀ W, pauliOperatorDistanceB P S w.ofNaimark W ≤ 9 * delta) := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans hs
  refine ⟨w.ofNaimark_state_error.trans_le hs, ?_, ?_⟩
  · intro W
    by_cases hsmall : delta ≤ 1
    · have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
      have h := w.ofNaimark_distance_alice W
      have := ha W
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
    · have := pauliOperatorDistanceA_le_four S w.ofNaimark W
      linarith
  · intro W
    by_cases hsmall : delta ≤ 1
    · have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
      have h := w.ofNaimark_distance_bob W
      have := hb W
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
    · have := pauliOperatorDistanceB_le_four S w.ofNaimark W
      linarith

private theorem nine_mul_deltaQld_le {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    9 * deltaQld a b epsilon P.m P.d P.q ≤
      deltaQld (9 * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpow := Real.rpow_le_rpow_of_exponent_le hmd (show a ≤ 9 * a by linarith)
  unfold deltaQld
  calc
    9 * (a * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))))) =
      (9 * a) * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by linarith))
      (add_nonneg (add_nonneg (Real.rpow_nonneg hepsilon _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))

/-- Conditional Naimark pullback preserves the source robustness form by
replacing `a` with `9 * a` and leaving `b` unchanged. This uses only nonnegative
`epsilon`; the converter imposes no upper bound on the success error.
It supports blueprint `ex:pauli-naimark-error-support`. Supplying the witness
from the global-pair and extraction constructions remains the upstream
obligation in `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #529. -/
theorem pauli_soundness_deltaQld_ofNaimarkWitness
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy S))
    {a b epsilon : ℝ} (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon)
    (hs : ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
      idealState P w.aux‖ ≤ deltaQld a b epsilon P.m P.d P.q)
    (hA : ∀ W, pauliOperatorDistanceA P (pauliNaimarkStrategy S) w W ≤
      deltaQld a b epsilon P.m P.d P.q)
    (hB : ∀ W, pauliOperatorDistanceB P (pauliNaimarkStrategy S) w W ≤
      deltaQld a b epsilon P.m P.d P.q) :
    ‖isometryTensor w.ofNaimark.φA w.ofNaimark.φB S.ψ -
      idealState P w.ofNaimark.aux‖ ≤ deltaQld (9 * a) b epsilon P.m P.d P.q ∧
    (∀ W, pauliOperatorDistanceA P S w.ofNaimark W ≤
      deltaQld (9 * a) b epsilon P.m P.d P.q) ∧
    (∀ W, pauliOperatorDistanceB P S w.ofNaimark W ≤
      deltaQld (9 * a) b epsilon P.m P.d P.q) := by
  obtain ⟨ht, htA, htB⟩ := pauli_soundness_ofNaimarkWitness S w hs hA hB
  have hd := (norm_nonneg _).trans hs
  have hscale := nine_mul_deltaQld_le (P := P) (b := b) ha hepsilon
  have hstate : deltaQld a b epsilon P.m P.d P.q ≤
      9 * deltaQld a b epsilon P.m P.d P.q := by linarith
  exact ⟨ht.trans (hstate.trans hscale), fun W => (htA W).trans hscale,
    fun W => (htB W).trans hscale⟩

end

end MIPStarRE.QPBT
