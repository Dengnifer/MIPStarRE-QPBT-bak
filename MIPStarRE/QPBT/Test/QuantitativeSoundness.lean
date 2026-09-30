import MIPStarRE.QPBT.Combining.Quantitative
import MIPStarRE.QPBT.Test.Soundness
import MIPStarRE.QPBT.Test.Soundness.ComponentBounds
import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars

/-!
# Quantitative Pauli basis test soundness

This module combines the quantitative global polynomial-pair construction with
the componentwise extraction and raw-effect transfer. The result retains one
common witness for the state estimate and both source-facing Pauli operator
families, first at a degree-four structured error and then at the canonical
`deltaQld 100` error.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Full-domain quantitative Pauli soundness retaining the squared state
component and the two raw operator components separately. With
`e = min epsilon 1` and `X` the extraction scale at the concrete native
global-pair error, one witness satisfies the capped bounds `min 4 (16*X)` and
`min 4 (472*X + 24*(m*d)/q + 192*sqrt X + 344*e)`.

This is a Lean-only component headline. It constructs the global polynomial
pair internally when the field ratio is at most one and uses the universal
caps otherwise. -/
theorem pauli_soundness_quantitative_mixed_components
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    let e := min epsilon 1
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤
          min 4 (16 * pauliSoundnessQuantitativeMixedScale P e) ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        min 4 (pauliSoundnessQuantitativeMixedOperatorError P e) := by
  let e := min epsilon 1
  change ∃ t : PauliSoundnessWitness P R,
    ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤
        min 4 (16 * pauliSoundnessQuantitativeMixedScale P e) ∧
    (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
      min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)) ∧
    ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
      min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)
  have he : 0 ≤ e := by
    dsimp only [e]
    exact le_min hepsilon zero_le_one
  have he1 : e ≤ 1 := by
    dsimp only [e]
    exact min_le_right _ _
  have hwinE : 1 - e ≤ R.value := by
    by_cases hepsilon1 : epsilon ≤ 1
    · have heq : e = epsilon := by simp only [e, min_eq_left hepsilon1]
      rw [heq]
      exact hwin
    · have heq : e = 1 := by
        simp only [e, min_eq_right (le_of_lt (lt_of_not_ge hepsilon1))]
      rw [heq]
      simpa only [sub_self] using R.value_nonneg
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError e + (P.m : ℝ) *
      pauliBaselineExtendedLineError e r) r
  let lambda := directNativeError P.extendedDirectLd passing
  let G := nativeGlobalPairError P lambda (pauliBaselinePointError e)
  let X := pauliSoundnessQuantitativeMixedScale P e
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpassing0 : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    exact mul_nonneg (by norm_num) (add_nonneg (Real.sqrt_nonneg _) hr0)
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    exact direct_native_error_nonneg _ hpassing0
  have hpoint0 : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact native_global_pair_error_nonneg P hlambda0 hpoint0
  have hXEq : X = 2800 * (G + Real.sqrt e + r) := by
    rfl
  have hX0 : 0 ≤ X := by
    rw [hXEq]
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg hG0 (Real.sqrt_nonneg e)) hr0)
  by_cases hr1 : r ≤ 1
  · let S := pauliNaimarkSetting P e R hwinE
    obtain ⟨w⟩ := exists_quantitative_global_pair_witness_native P e he S
    have w' : GlobalPairWitness (pauliNaimarkSetting P e R hwinE) G := by
      simpa only [S, G, lambda, passing, r] using w
    let x : ℝ := 2800 * (G + Real.sqrt e + r)
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      exact mul_nonneg (by norm_num)
        (add_nonneg (add_nonneg hG0 (Real.sqrt_nonneg e)) hr0)
    have hxX : x = X := by
      dsimp only [x]
      exact hXEq.symm
    obtain ⟨t, hstateSq, hA, hB⟩ :=
      exists_pauli_soundness_witness_with_component_bounds
        P e he he1 R hwinE G hG0 w'
    have hstateFour :
        ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 4 := by
      have htwo := pauli_soundness_state_distance_le_two P R t
      nlinarith [norm_nonneg
        (isometryTensor t.φA t.φB R.ψ - idealState P t.aux)]
    have hstateX :
        ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 16 * X :=
      (show ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 16 * x by
        simpa only [x, r] using hstateSq).trans_eq
          (congrArg (fun y : ℝ => 16 * y) hxX)
    have hcomponent :
        472 * x + 24 * r + 192 * Real.sqrt x + 344 * e =
          pauliSoundnessQuantitativeMixedOperatorError P e := by
      unfold pauliSoundnessQuantitativeMixedOperatorError
      change 472 * x + 24 * r + 192 * Real.sqrt x + 344 * e =
        472 * X + 24 * r + 192 * Real.sqrt X + 344 * e
      rw [hxX]
    refine ⟨t, le_min hstateFour hstateX, ?_, ?_⟩
    · intro W
      exact le_min (raw_pauli_operator_distance_a_le_four P R t W)
        ((show rawPauliOperatorDistanceA P R t W ≤
            472 * x + 24 * r + 192 * Real.sqrt x + 344 * e by
          simpa only [x, r] using hA W).trans_eq hcomponent)
    · intro W
      exact le_min (raw_pauli_operator_distance_b_le_four P R t W)
        ((show rawPauliOperatorDistanceB P R t W ≤
            472 * x + 24 * r + 192 * Real.sqrt x + 344 * e by
          simpa only [x, r] using hB W).trans_eq hcomponent)
  · have hrLarge : 1 < r := lt_of_not_ge hr1
    obtain ⟨_, _, _, hbaseline⟩ := pauli_soundness_explicit_baseline
    obtain ⟨t, _, _, _⟩ := hbaseline P epsilon hepsilon R hwin
    have hXRatio : 2800 * r ≤ X := by
      rw [hXEq]
      nlinarith [Real.sqrt_nonneg e]
    have hstateScale : 4 ≤ 16 * X := by nlinarith
    have hoperatorScale : 4 ≤ pauliSoundnessQuantitativeMixedOperatorError P e := by
      unfold pauliSoundnessQuantitativeMixedOperatorError
      change 4 ≤ 472 * X + 24 * r + 192 * Real.sqrt X + 344 * e
      nlinarith [Real.sqrt_nonneg X]
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [min_eq_left hstateScale]
      have htwo := pauli_soundness_state_distance_le_two P R t
      nlinarith [norm_nonneg
        (isometryTensor t.φA t.φB R.ψ - idealState P t.aux)]
    · intro W
      rw [min_eq_left hoperatorScale]
      exact raw_pauli_operator_distance_a_le_four P R t W
    · intro W
      rw [min_eq_left hoperatorScale]
      exact raw_pauli_operator_distance_b_le_four P R t W

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
-- Expanding the nested native mixed-scale lets exceeds the project default depth.
/-- Explicit quantitative Pauli soundness with the terminal common error
`min 4 (10769120 * m^(20481/262144) * d^(1/64) * E_b)`. The same auxiliary
state witnesses the unsquared state norm and both raw summed-squared operator
errors. -/
theorem pauli_soundness_quantitative_fractional
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          pauliSoundnessQuantitativeFractionalError P epsilon ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeFractionalError P epsilon) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeFractionalError P epsilon := by
  let e := min epsilon 1
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let m : ℝ := P.m
  let d : ℝ := P.d
  let q : ℝ := P.q
  let b : ℝ := pauliSoundnessQuantitativePower
  let M : ℝ := pauliSoundnessQuantitativeFractionalDimension P
  let F : ℝ := pauliSoundnessQuantitativeEnvelope P e
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  have he1 : e ≤ 1 := by dsimp [e]; exact min_le_right _ _
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast P.one_le_m
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast P.hd
  have hq : 1 ≤ q := by
    dsimp [q]
    obtain ⟨power, _, hqpow⟩ := P.hq
    rw [hqpow]
    exact_mod_cast Nat.one_le_pow power 2 (by norm_num)
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hM0 : 0 ≤ M := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  by_cases hsaturated : 4 ≤ pauliSoundnessQuantitativeFractionalRawError P e
  · obtain ⟨_, _, _, hbaseline⟩ := pauli_soundness_explicit_baseline
    obtain ⟨t, _, _, _⟩ := hbaseline P epsilon hepsilon R hwin
    have herror : pauliSoundnessQuantitativeFractionalError P epsilon = 4 := by
      unfold pauliSoundnessQuantitativeFractionalError
      change min 4 (pauliSoundnessQuantitativeFractionalRawError P e) = 4
      exact min_eq_left hsaturated
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [herror]
      exact (pauli_soundness_state_distance_le_two P R t).trans (by norm_num)
    · intro W
      rw [herror]
      exact raw_pauli_operator_distance_a_le_four P R t W
    · intro W
      rw [herror]
      exact raw_pauli_operator_distance_b_le_four P R t W
  · have hsmall : pauliSoundnessQuantitativeFractionalRawError P e < 4 :=
      lt_of_not_ge hsaturated
    have hrEq : r = m * d / q := by
      dsimp [r, m, d, q]
      push_cast
      rfl
    have hdimension : Real.rpow m b * Real.rpow d b ≤ M := by
      dsimp [M, m, d, pauliSoundnessQuantitativeFractionalDimension]
      exact mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le hm
          (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num))
        (Real.rpow_le_rpow_of_exponent_le hd
          (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num))
        (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hm0 _)
    have hrb : Real.rpow r b =
        Real.rpow m b * Real.rpow d b * Real.rpow q (-b) := by
      calc
        r ^ b = (m * d / q) ^ b := by rw [hrEq]
        _ = (m * d) ^ b / q ^ b := Real.div_rpow (mul_nonneg hm0 hd0) hq0 b
        _ = m ^ b * d ^ b * q ^ (-b) := by
          rw [Real.mul_rpow hm0 hd0, div_eq_mul_inv, Real.rpow_neg hq0]
    have hqF : Real.rpow q (-b) ≤ F := by
      dsimp [F, b, q, pauliSoundnessQuantitativeEnvelope]
      exact (le_add_of_nonneg_left (Real.rpow_nonneg he _)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
    have hrPowerMF : Real.rpow r b ≤ M * F := by
      rw [hrb]
      calc
        Real.rpow m b * Real.rpow d b * Real.rpow q (-b) ≤
            M * Real.rpow q (-b) :=
          mul_le_mul_of_nonneg_right hdimension (Real.rpow_nonneg hq0 _)
        _ ≤ M * F := mul_le_mul_of_nonneg_left hqF hM0
    have hr1 : r < 1 := by
      by_contra hratio
      have hone : 1 ≤ r := le_of_not_gt hratio
      have honePower : 1 ≤ Real.rpow r b :=
        Real.one_le_rpow hone
          (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      have hMF : 1 ≤ M * F := honePower.trans hrPowerMF
      unfold pauliSoundnessQuantitativeFractionalRawError at hsmall
      change 10769120 * M * F < 4 at hsmall
      nlinarith
    have hrLe : r ≤ 1 := hr1.le
    obtain ⟨t, hstateSq, hA, hB⟩ :=
      pauli_soundness_quantitative_mixed_components P epsilon hepsilon R hwin
    let X := pauliSoundnessQuantitativeMixedScale P e
    have hX0 : 0 ≤ X := by
      let passing := directPassingErrorEnvelope
        (pauliBaselinePointError e + (P.m : ℝ) *
          pauliBaselineExtendedLineError e r) r
      let lambda := directNativeError P.extendedDirectLd passing
      have hpassing : 0 ≤ passing := by
        dsimp [passing, directPassingErrorEnvelope]
        positivity
      have hlambda : 0 ≤ lambda := by
        dsimp only [lambda]
        exact direct_native_error_nonneg _ hpassing
      have hpoint : 0 ≤ pauliBaselinePointError e := by
        unfold pauliBaselinePointError
        exact mul_nonneg (zero_le_one.trans one_le_pauli_baseline_point_constant)
          (Real.rpow_nonneg he _)
      dsimp [X, pauliSoundnessQuantitativeMixedScale]
      exact mul_nonneg (by norm_num)
        (add_nonneg
          (add_nonneg (native_global_pair_error_nonneg P hlambda hpoint)
            (Real.sqrt_nonneg e)) hr0)
    have hXroot := quantitative_native_extraction_sqrt_le_fractional_base
      P e he he1 (by simpa only [r] using hrLe)
    have hXroot' : Real.sqrt X ≤ 16218 * M * F := by
      simpa only [X, M, F] using hXroot
    have hrawSmall : 10769120 * M * F < 4 := by
      simpa only [pauliSoundnessQuantitativeFractionalRawError, M, F] using hsmall
    have hrootLt : Real.sqrt X < 1 := by nlinarith
    have hXleRoot : X ≤ Real.sqrt X := by
      nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]
    have hePower : e ≤ Real.rpow e b := by
      calc
        e = Real.rpow e 1 := (Real.rpow_one e).symm
        _ ≤ Real.rpow e b :=
          Real.rpow_le_rpow_of_exponent_ge' he he1
            (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
            (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    have heF : Real.rpow e b ≤ F := by
      dsimp [F, b, pauliSoundnessQuantitativeEnvelope]
      exact (le_add_of_nonneg_right (Real.rpow_nonneg hq0 _)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
    have hM1 : 1 ≤ M := by
      dsimp [M, pauliSoundnessQuantitativeFractionalDimension, m, d] at hm hd ⊢
      exact one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hm (by norm_num)) (Real.one_le_rpow hd (by norm_num))
    have heMF : e ≤ M * F :=
      hePower.trans (heF.trans (le_mul_of_one_le_left hF0 hM1))
    have hrPower : r ≤ Real.rpow r b := by
      calc
        r = Real.rpow r 1 := (Real.rpow_one r).symm
        _ ≤ Real.rpow r b :=
          Real.rpow_le_rpow_of_exponent_ge' hr0 hrLe
            (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
            (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    have hrMF : r ≤ M * F := hrPower.trans hrPowerMF
    have hstateBound : 4 * Real.sqrt X ≤ 10769120 * M * F := by
      nlinarith
    have hopBound : pauliSoundnessQuantitativeMixedOperatorError P e ≤
        10769120 * M * F := by
      unfold pauliSoundnessQuantitativeMixedOperatorError
      change 472 * X + 24 * r + 192 * Real.sqrt X + 344 * e ≤ _
      nlinarith
    have herror : pauliSoundnessQuantitativeFractionalError P epsilon =
        10769120 * M * F := by
      unfold pauliSoundnessQuantitativeFractionalError
      change min 4 (10769120 * M * F) = _
      exact min_eq_right hrawSmall.le
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [herror]
      have hsq : ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤
          16 * X := hstateSq.trans (min_le_right _ _)
      have hnorm := norm_nonneg
        (isometryTensor t.φA t.φB R.ψ - idealState P t.aux)
      exact (show ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          4 * Real.sqrt X by
        nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg X]).trans hstateBound
    · intro W
      rw [herror]
      exact (hA W).trans (min_le_right _ _) |>.trans hopBound
    · intro W
      rw [herror]
      exact (hB W).trans (min_le_right _ _) |>.trans hopBound

/-- Weakening: `pauli_soundness_quantitative_fractional` implies this
degree-two common bound because the fractional dimension factor is at most
`(m*d)^2` and `10769120 ≤ 10^9`. The statement is retained for compatibility
with the issue #729 quantitative interface.

Bound: deferred #727. -/
theorem pauli_soundness_quantitative_degree_two
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          pauliSoundnessQuantitativeDegreeTwoError P epsilon ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeDegreeTwoError P epsilon) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeDegreeTwoError P epsilon := by
  obtain ⟨t, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_fractional P epsilon hepsilon R hwin
  have herror :=
    pauli_soundness_quantitative_fractional_error_le_degree_two P epsilon hepsilon
  exact ⟨t, hstate.trans herror, fun W => (hA W).trans herror,
    fun W => (hB W).trans herror⟩

/-- Weakening: `pauli_soundness_quantitative_degree_two` implies this
historical degree-four common bound. The statement is retained for existing
downstream uses.

Bound: deferred #727. -/
theorem pauli_soundness_quantitative
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          pauliSoundnessQuantitativeError P epsilon ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeError P epsilon) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeError P epsilon := by
  obtain ⟨t, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_degree_two P epsilon hepsilon R hwin
  have herror :=
    pauli_soundness_quantitative_degree_two_error_le_quantitative_error
      P epsilon hepsilon
  exact ⟨t, hstate.trans herror, fun W => (hA W).trans herror,
    fun W => (hB W).trans herror⟩

/-- Weakening: `pauli_soundness_quantitative_degree_two` implies the canonical
`deltaQld` form because paper `thm:pauli` states one common polynomial error
for the state and both operator families. The coefficient is `100` and the
exponent is `1 / 67108864`. -/
theorem pauli_soundness_quantitative_canonical :
    1 ≤ (100 : ℝ) ∧
    0 < pauliSoundnessQuantitativePower ∧
    pauliSoundnessQuantitativePower < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ R : Strategy (pauliBasisTest P), 1 - epsilon ≤ R.value →
          ∃ t : PauliSoundnessWitness P R,
            ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
                deltaQld 100 pauliSoundnessQuantitativePower
                  epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q := by
  refine ⟨by norm_num, pauli_soundness_quantitative_power_pos,
    pauli_soundness_quantitative_power_lt_one, ?_⟩
  intro P epsilon hepsilon R hwin
  obtain ⟨t, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_degree_two P epsilon hepsilon R hwin
  have hcanonical :=
    pauli_soundness_quantitative_degree_two_error_le_deltaQld P epsilon hepsilon
  exact ⟨t, hstate.trans hcanonical, fun W => (hA W).trans hcanonical,
    fun W => (hB W).trans hcanonical⟩

end

end MIPStarRE.QPBT
