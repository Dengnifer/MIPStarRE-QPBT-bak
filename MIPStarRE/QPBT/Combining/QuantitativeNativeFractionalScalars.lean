module

public import MIPStarRE.QPBT.Combining.QuantitativeNativeScalars.Core

/-!
# Fractional native scalar bounds for QPBT

This module retains the fractional dimension powers in the exact native
global-pair calculation and proves the sharp scalar comparisons used in the
global-pair and extraction estimates.

## References

* Paper `lem:qld-4-7`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* Blueprint `thm:qld-native-small-regime-global-pair`
* Blueprint `thm:pauli-final-fractional-scalar-support`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The final quantitative Pauli-soundness exponent. -/
def pauliSoundnessQuantitativePower : ℝ := 1 / 67108864

/-- The three-term error envelope at the final Pauli-soundness exponent. -/
def pauliSoundnessQuantitativeEnvelope (P : AdmissibleParams) (e : ℝ) : ℝ :=
  Real.rpow e pauliSoundnessQuantitativePower +
    Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) +
    Real.rpow 2
      (-(pauliSoundnessQuantitativePower * ((P.m * P.d : ℕ) : ℝ)))

/-- The final three-term envelope is nonnegative. -/
theorem pauli_soundness_quantitative_envelope_nonneg
    (P : AdmissibleParams) {e : ℝ} (he : 0 ≤ e) :
    0 ≤ pauliSoundnessQuantitativeEnvelope P e := by
  unfold pauliSoundnessQuantitativeEnvelope
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg he _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (by norm_num) _)

/-- The fractional dimension factor retained by the native scalar
calculation. -/
def pauliSoundnessQuantitativeFractionalDimension
    (P : AdmissibleParams) : ℝ :=
  Real.rpow (P.m : ℝ) (20481 / 262144 : ℝ) *
    Real.rpow (P.d : ℝ) (1 / 64 : ℝ)


private theorem min_one_add_le_add_min_one
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min 1 (x + y) ≤ min 1 x + min 1 y := by
  by_cases hx1 : 1 ≤ x
  · rw [min_eq_left hx1]
    exact (min_le_left _ _).trans
      (by linarith [le_min zero_le_one hy])
  · have hxlt : x < 1 := lt_of_not_ge hx1
    by_cases hy1 : 1 ≤ y
    · rw [min_eq_left hy1]
      exact (min_le_left _ _).trans
        (by linarith [le_min zero_le_one hx])
    · have hylt : y < 1 := lt_of_not_ge hy1
      rw [min_eq_right hxlt.le, min_eq_right hylt.le]
      exact min_le_right 1 (x + y)

private theorem min_one_sum_six_le
    {x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃)
    (h₄ : 0 ≤ x₄) (h₅ : 0 ≤ x₅) (h₆ : 0 ≤ x₆) :
    min 1 (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) ≤
      min 1 x₁ + min 1 x₂ + min 1 x₃ + min 1 x₄ + min 1 x₅ + min 1 x₆ := by
  calc
    min 1 (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) ≤
        min 1 (x₁ + x₂ + x₃ + x₄ + x₅) + min 1 x₆ :=
      min_one_add_le_add_min_one
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) h₄) h₅) h₆
    _ ≤ (min 1 (x₁ + x₂ + x₃ + x₄) + min 1 x₅) + min 1 x₆ := by
      gcongr
      exact min_one_add_le_add_min_one
        (add_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) h₄) h₅
    _ ≤ ((min 1 (x₁ + x₂ + x₃) + min 1 x₄) + min 1 x₅) + min 1 x₆ := by
      gcongr
      exact min_one_add_le_add_min_one (add_nonneg (add_nonneg h₁ h₂) h₃) h₄
    _ ≤ (((min 1 (x₁ + x₂) + min 1 x₃) + min 1 x₄) + min 1 x₅) +
        min 1 x₆ := by
      gcongr
      exact min_one_add_le_add_min_one (add_nonneg h₁ h₂) h₃
    _ ≤ ((((min 1 x₁ + min 1 x₂) + min 1 x₃) + min 1 x₄) + min 1 x₅) +
        min 1 x₆ := by
      gcongr
      exact min_one_add_le_add_min_one h₁ h₂
    _ = _ := by ring

private theorem min_one_le_rpow
    {x theta : ℝ} (hx : 0 ≤ x) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    min 1 x ≤ Real.rpow x theta := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' hx hx1 htheta htheta1
  · rw [min_eq_left (le_of_not_ge hx1)]
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (le_of_not_ge hx1) htheta

private theorem sqrt_min_one_le_rpow
    {x theta : ℝ} (hx : 0 ≤ x) (htheta : 0 ≤ theta) (hthetaHalf : theta ≤ 1 / 2) :
    Real.sqrt (min 1 x) ≤ Real.rpow x theta := by
  have hmin0 : 0 ≤ min 1 x := le_min zero_le_one hx
  have hmin1 : min 1 x ≤ 1 := min_le_left _ _
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (min 1 x) (1 / 2 : ℝ) ≤ Real.rpow (min 1 x) theta :=
      Real.rpow_le_rpow_of_exponent_ge' hmin0 hmin1 htheta hthetaHalf
    _ ≤ Real.rpow x theta :=
      Real.rpow_le_rpow hmin0 (min_le_right _ _) htheta

private theorem rpow_six_one_sixteenth_le_two :
    Real.rpow 6 (1 / 16 : ℝ) ≤ 2 := by
  simp only [Real.rpow_eq_pow]
  rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem rpow_six_one_five_hundred_twelfth_le_two :
    Real.rpow 6 (1 / 512 : ℝ) ≤ 2 := by
  simp only [Real.rpow_eq_pow]
  rw [show (1 / 512 : ℝ) = (512 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  calc
    (6 : ℝ) ≤ 2 ^ (16 : ℕ) := by norm_num
    _ ≤ 2 ^ (16 : ℕ) * 2 ^ (496 : ℕ) := by
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    _ = 2 ^ (512 : ℕ) := by rw [← pow_add]
    _ = Real.rpow 2 (512 : ℝ) := (Real.rpow_natCast 2 512).symm

private theorem rpow_eight_hundred_thousand_one_sixteenth_le_three :
    Real.rpow 800000 (1 / 16 : ℝ) ≤ 3 := by
  simp only [Real.rpow_eq_pow]
  rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem rpow_four_hundred_thousand_one_sixteenth_le_three :
    Real.rpow 400000 (1 / 16 : ℝ) ≤ 3 := by
  simp only [Real.rpow_eq_pow]
  rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem rpow_four_five_sixty_fourths_le_two :
    Real.rpow 4 (5 / 64 : ℝ) ≤ 2 := by
  calc
    Real.rpow 4 (5 / 64 : ℝ) ≤ Real.rpow 4 (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = Real.sqrt 4 := (Real.sqrt_eq_rpow 4).symm
    _ = 2 := by norm_num

set_option maxHeartbeats 800000 in
-- The six independent rational-power normalizations exceed the project default.
/-- The six native contributions at power `1/16`, with the unit cap used only
at this terminal conversion, are bounded by `12 M E_b`. -/
theorem quantitative_native_error_one_sixteenth_le_fractional_base
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    let lambda := directNativeError P.extendedDirectLd passing
    Real.rpow lambda (1 / 16 : ℝ) ≤
      12 * pauliSoundnessQuantitativeFractionalDimension P *
        pauliSoundnessQuantitativeEnvelope P e := by
  intro r passing lambda
  let m : ℝ := P.m
  let d : ℝ := P.d
  let q : ℝ := P.q
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let h : ℝ := 2 * m + 2
  let b : ℝ := pauliSoundnessQuantitativePower
  let D : ℝ := Real.rpow m (5 / 64 : ℝ) * Real.rpow d (1 / 64 : ℝ)
  let M : ℝ := pauliSoundnessQuantitativeFractionalDimension P
  let F : ℝ := pauliSoundnessQuantitativeEnvelope P e
  let u₁ : ℝ := Real.rpow e (1 / 2097152 : ℝ)
  let u₂ : ℝ := Real.rpow m (1 / 262144 : ℝ) * Real.rpow e b
  let u₃ : ℝ := Real.rpow m (1 / 262144 : ℝ) *
    Real.rpow r (1 / 4194304 : ℝ)
  let u₄ : ℝ := Real.rpow r (1 / 131072 : ℝ)
  let u₅ : ℝ := Real.rpow (d / q) (1 / 131072 : ℝ)
  let u₆ : ℝ := Real.exp (-(4 * h * d * (1 / 16 : ℝ)))
  let z₁ : ℝ := 6 * D * u₁
  let z₂ : ℝ := 6 * D * u₂
  let z₃ : ℝ := 6 * D * u₃
  let z₄ : ℝ := 6 * D * u₄
  let z₅ : ℝ := 6 * D * u₅
  let z₆ : ℝ := 6 * D * u₆
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
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M, pauliSoundnessQuantitativeFractionalDimension]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hu₁ : 0 ≤ u₁ := by dsimp [u₁]; positivity
  have hu₂ : 0 ≤ u₂ := by dsimp [u₂]; positivity
  have hu₃ : 0 ≤ u₃ := by dsimp [u₃]; positivity
  have hu₄ : 0 ≤ u₄ := by dsimp [u₄]; positivity
  have hu₅ : 0 ≤ u₅ := by dsimp [u₅]; positivity
  have hu₆ : 0 ≤ u₆ := by dsimp [u₆]; positivity
  have hz₁ : 0 ≤ z₁ := by dsimp [z₁]; positivity
  have hz₂ : 0 ≤ z₂ := by dsimp [z₂]; positivity
  have hz₃ : 0 ≤ z₃ := by dsimp [z₃]; positivity
  have hz₄ : 0 ≤ z₄ := by dsimp [z₄]; positivity
  have hz₅ : 0 ≤ z₅ := by dsimp [z₅]; positivity
  have hz₆ : 0 ≤ z₆ := by dsimp [z₆]; positivity
  have hh4m : h ≤ 4 * m := by
    dsimp [h]
    nlinarith
  have hrEq : r = m * d / q := by
    dsimp [r, m, d, q]
    push_cast
    rfl
  have hhrpow : Real.rpow h (5 / 64 : ℝ) ≤
      2 * Real.rpow m (5 / 64 : ℝ) := by
    calc
      Real.rpow h (5 / 64 : ℝ) ≤ Real.rpow (4 * m) (5 / 64 : ℝ) :=
        Real.rpow_le_rpow hh hh4m (by norm_num)
      _ = Real.rpow 4 (5 / 64 : ℝ) * Real.rpow m (5 / 64 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow (by norm_num) hm0]
      _ ≤ 2 * Real.rpow m (5 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_right rpow_four_five_sixty_fourths_le_two
          (Real.rpow_nonneg hm0 _)
  have hU : quantitativeNativeSeparatedRaw P e (1 / 16 : ℝ) ≤
      z₁ + z₂ + z₃ + z₄ + z₅ + z₆ := by
    unfold quantitativeNativeSeparatedRaw
    dsimp only
    norm_num [quantitativeLowDegreePower]
    rw [← hrEq]
    change Real.rpow h (5 / 64 : ℝ) * Real.rpow d (1 / 64 : ℝ) *
        (Real.rpow 800000 (1 / 16 : ℝ) * (u₁ + u₂ + u₃ + u₄) +
          Real.rpow 400000 (1 / 16 : ℝ) * (u₅ + u₆)) ≤
      z₁ + z₂ + z₃ + z₄ + z₅ + z₆
    have hsum₁ : 0 ≤ u₁ + u₂ + u₃ + u₄ :=
      add_nonneg (add_nonneg (add_nonneg hu₁ hu₂) hu₃) hu₄
    have hsum₂ : 0 ≤ u₅ + u₆ := add_nonneg hu₅ hu₆
    have hdim : Real.rpow h (5 / 64 : ℝ) * Real.rpow d (1 / 64 : ℝ) ≤
        2 * D := by
      calc
        Real.rpow h (5 / 64 : ℝ) * Real.rpow d (1 / 64 : ℝ) ≤
            (2 * Real.rpow m (5 / 64 : ℝ)) * Real.rpow d (1 / 64 : ℝ) :=
          mul_le_mul_of_nonneg_right hhrpow (Real.rpow_nonneg hd0 _)
        _ = 2 * D := by dsimp [D]; ring
    have hbracket :
        Real.rpow 800000 (1 / 16 : ℝ) * (u₁ + u₂ + u₃ + u₄) +
            Real.rpow 400000 (1 / 16 : ℝ) * (u₅ + u₆) ≤
          3 * (u₁ + u₂ + u₃ + u₄) + 3 * (u₅ + u₆) :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          rpow_eight_hundred_thousand_one_sixteenth_le_three hsum₁)
        (mul_le_mul_of_nonneg_right
          rpow_four_hundred_thousand_one_sixteenth_le_three hsum₂)
    have hbracket0 : 0 ≤
        Real.rpow 800000 (1 / 16 : ℝ) * (u₁ + u₂ + u₃ + u₄) +
          Real.rpow 400000 (1 / 16 : ℝ) * (u₅ + u₆) :=
      add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hsum₁)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hsum₂)
    calc
      _ ≤ (2 * D) *
          (Real.rpow 800000 (1 / 16 : ℝ) * (u₁ + u₂ + u₃ + u₄) +
            Real.rpow 400000 (1 / 16 : ℝ) * (u₅ + u₆)) :=
        mul_le_mul_of_nonneg_right hdim hbracket0
      _ ≤ (2 * D) * (3 * (u₁ + u₂ + u₃ + u₄) + 3 * (u₅ + u₆)) :=
        mul_le_mul_of_nonneg_left hbracket (mul_nonneg (by norm_num) hD)
      _ = z₁ + z₂ + z₃ + z₄ + z₅ + z₆ := by
        dsimp [z₁, z₂, z₃, z₄, z₅, z₆]
        ring
  have hlambda := quantitative_native_error_rpow_le_separated
    P e (1 / 16 : ℝ) he (by norm_num) (by norm_num)
  have hlambda' : Real.rpow lambda (1 / 16 : ℝ) ≤
      min 1 (z₁ + z₂ + z₃ + z₄ + z₅ + z₆) := by
    calc
      Real.rpow lambda (1 / 16 : ℝ) ≤
          quantitativeNativeSeparatedError P e (1 / 16 : ℝ) := by
        simpa only [r, passing, lambda] using hlambda
      _ ≤ min 1 (z₁ + z₂ + z₃ + z₄ + z₅ + z₆) := by
        unfold quantitativeNativeSeparatedError
        exact min_le_min_left 1 hU
  have hsplit : Real.rpow lambda (1 / 16 : ℝ) ≤
      min 1 z₁ + min 1 z₂ + min 1 z₃ + min 1 z₄ + min 1 z₅ + min 1 z₆ :=
    hlambda'.trans (min_one_sum_six_le hz₁ hz₂ hz₃ hz₄ hz₅ hz₆)
  have hDM : D ≤ M := by
    dsimp [D, M, m, d, pauliSoundnessQuantitativeFractionalDimension]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast P.one_le_m) (by norm_num))
      le_rfl (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hePower : Real.rpow e (1 / 2097152 : ℝ) ≤ Real.rpow e b := by
    have hpower := Real.rpow_le_rpow_of_exponent_ge' he he1
      (show 0 ≤ (1 / 67108864 : ℝ) by norm_num)
      (show (1 / 67108864 : ℝ) ≤ 1 / 2097152 by norm_num)
    simpa only [b, pauliSoundnessQuantitativePower, Real.rpow_eq_pow] using hpower
  have hterm₁ : min 1 z₁ ≤ 6 * M * Real.rpow e b := by
    calc
      min 1 z₁ ≤ z₁ := min_le_right _ _
      _ ≤ 6 * M * Real.rpow e b := by
        dsimp [z₁, u₁]
        calc
          6 * D * Real.rpow e (1 / 2097152 : ℝ) ≤
              6 * M * Real.rpow e (1 / 2097152 : ℝ) := by gcongr
          _ ≤ 6 * M * Real.rpow e b := by gcongr
  have hDext : D * Real.rpow m (1 / 262144 : ℝ) = M := by
    dsimp [D, M, m, d, pauliSoundnessQuantitativeFractionalDimension]
    calc
      Real.rpow (P.m : ℝ) (5 / 64 : ℝ) * Real.rpow (P.d : ℝ) (1 / 64 : ℝ) *
          Real.rpow (P.m : ℝ) (1 / 262144 : ℝ) =
          (Real.rpow (P.m : ℝ) (5 / 64 : ℝ) *
            Real.rpow (P.m : ℝ) (1 / 262144 : ℝ)) *
            Real.rpow (P.d : ℝ) (1 / 64 : ℝ) := by ring
      _ = Real.rpow (P.m : ℝ) ((5 / 64 : ℝ) + 1 / 262144) *
          Real.rpow (P.d : ℝ) (1 / 64 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (P.m : ℝ))]
      _ = _ := by norm_num
  have hdimensionBound : ∀ {am ad : ℝ},
      am ≤ (20481 / 262144 : ℝ) → ad ≤ (1 / 64 : ℝ) →
        Real.rpow m am * Real.rpow d ad ≤ M := by
    intro am ad ham had
    dsimp [M, m, d, pauliSoundnessQuantitativeFractionalDimension]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hm ham)
      (Real.rpow_le_rpow_of_exponent_le hd had)
      (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hm0 _)
  have hterm₂ : min 1 z₂ ≤ 6 * M * Real.rpow e b := by
    calc
      min 1 z₂ ≤ z₂ := min_le_right _ _
      _ = 6 * (D * Real.rpow m (1 / 262144 : ℝ)) * Real.rpow e b := by
        dsimp [z₂, u₂]
        ring
      _ = 6 * M * Real.rpow e b := by rw [hDext]
  have hfield₃ : min 1 z₃ ≤ 2 * M * Real.rpow q (-b) := by
    have hDroot : D ^ (1 / 16 : ℝ) =
        m ^ (5 / 1024 : ℝ) * d ^ (1 / 1024 : ℝ) := by
      dsimp [D]
      rw [Real.mul_rpow (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)]
      rw [← Real.rpow_mul hm0, ← Real.rpow_mul hd0]
      congr 1 <;> norm_num
    have hrb : r ^ b = m ^ b * d ^ b * q ^ (-b) := by
      calc
        r ^ b = (m * d / q) ^ b := by rw [hrEq]
        _ = (m * d) ^ b / q ^ b :=
          Real.div_rpow (mul_nonneg hm0 hd0) hq0 b
        _ = m ^ b * d ^ b * q ^ (-b) := by
          rw [Real.mul_rpow hm0 hd0, div_eq_mul_inv, Real.rpow_neg hq0]
    have huRoot : u₃ ^ (1 / 16 : ℝ) =
        m ^ (1 / 4194304 : ℝ) * (m ^ b * d ^ b * q ^ (-b)) := by
      dsimp [u₃]
      rw [Real.mul_rpow (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hr _)]
      rw [← Real.rpow_mul hm0, ← Real.rpow_mul hr]
      rw [show (1 / 262144 : ℝ) * (1 / 16 : ℝ) = 1 / 4194304 by norm_num]
      rw [show (1 / 4194304 : ℝ) * (1 / 16 : ℝ) = b by
        dsimp [b, pauliSoundnessQuantitativePower]
        norm_num]
      rw [hrb]
    have hzRoot : z₃ ^ (1 / 16 : ℝ) =
        (6 : ℝ) ^ (1 / 16 : ℝ) *
          ((m ^ ((5 / 1024 : ℝ) + 1 / 4194304 + b) *
            d ^ ((1 / 1024 : ℝ) + b)) * q ^ (-b)) := by
      dsimp [z₃]
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hD) hu₃,
        Real.mul_rpow (by norm_num) hD]
      rw [hDroot, huRoot]
      calc
        _ = (6 : ℝ) ^ (1 / 16 : ℝ) *
            (((m ^ (5 / 1024 : ℝ) * m ^ (1 / 4194304 : ℝ)) * m ^ b) *
              (d ^ (1 / 1024 : ℝ) * d ^ b) * q ^ (-b)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (zero_lt_one.trans_le hm),
            ← Real.rpow_add (zero_lt_one.trans_le hm),
            ← Real.rpow_add (zero_lt_one.trans_le hd)]
    have hdim :
        Real.rpow m ((5 / 1024 : ℝ) + 1 / 4194304 + b) *
            Real.rpow d ((1 / 1024 : ℝ) + b) ≤ M :=
      hdimensionBound (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
        (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    have hqpow0 : 0 ≤ Real.rpow q (-b) := Real.rpow_nonneg hq0 _
    calc
      min 1 z₃ ≤ Real.rpow z₃ (1 / 16 : ℝ) :=
        min_one_le_rpow hz₃ (by norm_num) (by norm_num)
      _ = Real.rpow 6 (1 / 16 : ℝ) *
          ((Real.rpow m ((5 / 1024 : ℝ) + 1 / 4194304 + b) *
            Real.rpow d ((1 / 1024 : ℝ) + b)) * Real.rpow q (-b)) := hzRoot
      _ ≤ 2 *
          ((Real.rpow m ((5 / 1024 : ℝ) + 1 / 4194304 + b) *
            Real.rpow d ((1 / 1024 : ℝ) + b)) * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_right rpow_six_one_sixteenth_le_two
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)) hqpow0)
      _ ≤ 2 * (M * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdim hqpow0) (by norm_num)
      _ = 2 * M * Real.rpow q (-b) := by ring
  have hfield₄ : min 1 z₄ ≤ 2 * M * Real.rpow q (-b) := by
    have hDroot : D ^ (1 / 512 : ℝ) =
        m ^ (5 / 32768 : ℝ) * d ^ (1 / 32768 : ℝ) := by
      dsimp [D]
      rw [Real.mul_rpow (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)]
      rw [← Real.rpow_mul hm0, ← Real.rpow_mul hd0]
      congr 1 <;> norm_num
    have hrb : r ^ b = m ^ b * d ^ b * q ^ (-b) := by
      calc
        r ^ b = (m * d / q) ^ b := by rw [hrEq]
        _ = (m * d) ^ b / q ^ b :=
          Real.div_rpow (mul_nonneg hm0 hd0) hq0 b
        _ = m ^ b * d ^ b * q ^ (-b) := by
          rw [Real.mul_rpow hm0 hd0, div_eq_mul_inv, Real.rpow_neg hq0]
    have huRoot : u₄ ^ (1 / 512 : ℝ) =
        m ^ b * d ^ b * q ^ (-b) := by
      dsimp [u₄]
      rw [← Real.rpow_mul hr]
      rw [show (1 / 131072 : ℝ) * (1 / 512 : ℝ) = b by
        dsimp [b, pauliSoundnessQuantitativePower]
        norm_num]
      exact hrb
    have hzRoot : z₄ ^ (1 / 512 : ℝ) =
        (6 : ℝ) ^ (1 / 512 : ℝ) *
          ((m ^ ((5 / 32768 : ℝ) + b) * d ^ ((1 / 32768 : ℝ) + b)) *
            q ^ (-b)) := by
      dsimp [z₄]
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hD) hu₄,
        Real.mul_rpow (by norm_num) hD, hDroot, huRoot]
      calc
        _ = (6 : ℝ) ^ (1 / 512 : ℝ) *
            ((m ^ (5 / 32768 : ℝ) * m ^ b) *
              (d ^ (1 / 32768 : ℝ) * d ^ b) * q ^ (-b)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (zero_lt_one.trans_le hm),
            ← Real.rpow_add (zero_lt_one.trans_le hd)]
    have hdim :
        Real.rpow m ((5 / 32768 : ℝ) + b) *
            Real.rpow d ((1 / 32768 : ℝ) + b) ≤ M :=
      hdimensionBound (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
        (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    have hqpow0 : 0 ≤ Real.rpow q (-b) := Real.rpow_nonneg hq0 _
    calc
      min 1 z₄ ≤ Real.rpow z₄ (1 / 512 : ℝ) :=
        min_one_le_rpow hz₄ (by norm_num) (by norm_num)
      _ = Real.rpow 6 (1 / 512 : ℝ) *
          ((Real.rpow m ((5 / 32768 : ℝ) + b) *
            Real.rpow d ((1 / 32768 : ℝ) + b)) * Real.rpow q (-b)) := hzRoot
      _ ≤ 2 *
          ((Real.rpow m ((5 / 32768 : ℝ) + b) *
            Real.rpow d ((1 / 32768 : ℝ) + b)) * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_right rpow_six_one_five_hundred_twelfth_le_two
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)) hqpow0)
      _ ≤ 2 * (M * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdim hqpow0) (by norm_num)
      _ = 2 * M * Real.rpow q (-b) := by ring
  have hfield₅ : min 1 z₅ ≤ 2 * M * Real.rpow q (-b) := by
    have hDroot : D ^ (1 / 512 : ℝ) =
        m ^ (5 / 32768 : ℝ) * d ^ (1 / 32768 : ℝ) := by
      dsimp [D]
      rw [Real.mul_rpow (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)]
      rw [← Real.rpow_mul hm0, ← Real.rpow_mul hd0]
      congr 1 <;> norm_num
    have hdqb : (d / q) ^ b = d ^ b * q ^ (-b) := by
      calc
        (d / q) ^ b = d ^ b / q ^ b := Real.div_rpow hd0 hq0 b
        _ = d ^ b * q ^ (-b) := by
          rw [div_eq_mul_inv, Real.rpow_neg hq0]
    have huRoot : u₅ ^ (1 / 512 : ℝ) = d ^ b * q ^ (-b) := by
      dsimp [u₅]
      rw [← Real.rpow_mul (div_nonneg hd0 hq0)]
      rw [show (1 / 131072 : ℝ) * (1 / 512 : ℝ) = b by
        dsimp [b, pauliSoundnessQuantitativePower]
        norm_num]
      exact hdqb
    have hzRoot : z₅ ^ (1 / 512 : ℝ) =
        (6 : ℝ) ^ (1 / 512 : ℝ) *
          ((m ^ (5 / 32768 : ℝ) * d ^ ((1 / 32768 : ℝ) + b)) * q ^ (-b)) := by
      dsimp [z₅]
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hD) hu₅,
        Real.mul_rpow (by norm_num) hD, hDroot, huRoot]
      calc
        _ = (6 : ℝ) ^ (1 / 512 : ℝ) *
            (m ^ (5 / 32768 : ℝ) *
              (d ^ (1 / 32768 : ℝ) * d ^ b) * q ^ (-b)) := by ring
        _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hd)]
    have hdim :
        Real.rpow m (5 / 32768 : ℝ) * Real.rpow d ((1 / 32768 : ℝ) + b) ≤ M :=
      hdimensionBound (by norm_num)
        (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    have hqpow0 : 0 ≤ Real.rpow q (-b) := Real.rpow_nonneg hq0 _
    calc
      min 1 z₅ ≤ Real.rpow z₅ (1 / 512 : ℝ) :=
        min_one_le_rpow hz₅ (by norm_num) (by norm_num)
      _ = Real.rpow 6 (1 / 512 : ℝ) *
          ((Real.rpow m (5 / 32768 : ℝ) *
            Real.rpow d ((1 / 32768 : ℝ) + b)) * Real.rpow q (-b)) := hzRoot
      _ ≤ 2 *
          ((Real.rpow m (5 / 32768 : ℝ) *
            Real.rpow d ((1 / 32768 : ℝ) + b)) * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_right rpow_six_one_five_hundred_twelfth_le_two
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _)) hqpow0)
      _ ≤ 2 * (M * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdim hqpow0) (by norm_num)
      _ = 2 * M * Real.rpow q (-b) := by ring
  have htail : min 1 z₆ ≤ 6 * M *
      Real.rpow 2 (-(b * n)) := by
    have hnEq : n = m * d := by
      dsimp [n, m, d]
      push_cast
      rfl
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmd0 : 0 ≤ m * d := mul_nonneg hm0 hd0
    have htailBase : u₆ ≤ Real.rpow 2 (-(b * n)) := by
      dsimp [u₆]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      rw [hnEq]
      dsimp [h, b, pauliSoundnessQuantitativePower]
      nlinarith [mul_le_mul_of_nonneg_right hlog hmd0]
    calc
      min 1 z₆ ≤ z₆ := min_le_right _ _
      _ = 6 * D * u₆ := rfl
      _ ≤ 6 * M * u₆ := by gcongr
      _ ≤ 6 * M * Real.rpow 2 (-(b * n)) := by gcongr
  have heF : Real.rpow e b ≤ F := by
    dsimp [F, b, pauliSoundnessQuantitativeEnvelope]
    exact (le_add_of_nonneg_right (Real.rpow_nonneg hq0 _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have hqF : Real.rpow q (-b) ≤ F := by
    dsimp [F, b, q, pauliSoundnessQuantitativeEnvelope]
    exact (le_add_of_nonneg_left (Real.rpow_nonneg he _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have htailF : Real.rpow 2 (-(b * n)) ≤ F := by
    dsimp [F, b, n, pauliSoundnessQuantitativeEnvelope]
    exact le_add_of_nonneg_left
      (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hq0 _))
  calc
    Real.rpow lambda (1 / 16 : ℝ) ≤
        min 1 z₁ + min 1 z₂ + min 1 z₃ + min 1 z₄ + min 1 z₅ + min 1 z₆ := hsplit
    _ ≤ 12 * M * Real.rpow e b + 6 * M * Real.rpow q (-b) +
        6 * M * Real.rpow 2 (-(b * n)) := by linarith
    _ ≤ 12 * M * F := by
      have hM12 : 0 ≤ 12 * M := by positivity
      have hM6 : 0 ≤ 6 * M := by positivity
      calc
        _ ≤ 12 * M * Real.rpow e b + 6 * M * Real.rpow q (-b) +
            6 * M * Real.rpow 2 (-(b * n)) := le_rfl
        _ ≤ 12 * M * Real.rpow e b + 12 * M * Real.rpow q (-b) +
            12 * M * Real.rpow 2 (-(b * n)) := by
          have hqpow : 0 ≤ M * Real.rpow q (-b) :=
            mul_nonneg hM (Real.rpow_nonneg hq0 _)
          have htpow : 0 ≤ M * Real.rpow 2 (-(b * n)) :=
            mul_nonneg hM (Real.rpow_nonneg (by norm_num) _)
          nlinarith
        _ = 12 * M *
            (Real.rpow e b + Real.rpow q (-b) + Real.rpow 2 (-(b * n))) := by ring
        _ = 12 * M * F := by rfl
    _ = 12 * pauliSoundnessQuantitativeFractionalDimension P *
        pauliSoundnessQuantitativeEnvelope P e := by rfl

set_option maxHeartbeats 800000 in
-- The proof keeps the rounding, point, and collision caps as separate groups.
/-- The square root of the exact native global-pair error is bounded by
`304 M E_b` on the clipped source-error domain. -/
theorem quantitative_native_global_pair_sqrt_le_fractional_base
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    let lambda := directNativeError P.extendedDirectLd passing
    Real.sqrt (nativeGlobalPairError P lambda (pauliBaselinePointError e)) ≤
      304 * pauliSoundnessQuantitativeFractionalDimension P *
        pauliSoundnessQuantitativeEnvelope P e := by
  intro r passing lambda
  let m : ℝ := P.m
  let d : ℝ := P.d
  let q : ℝ := P.q
  let b : ℝ := pauliSoundnessQuantitativePower
  let M : ℝ := pauliSoundnessQuantitativeFractionalDimension P
  let F : ℝ := pauliSoundnessQuantitativeEnvelope P e
  let rounding : ℝ := 32 * nativeRoundingError lambda
  let point : ℝ := 64 * pauliBaselinePointError e
  let collision : ℝ :=
    (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)
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
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrEq : r = m * d / q := by
    dsimp [r, m, d, q]
    push_cast
    rfl
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    exact direct_native_error_nonneg _ hpassing
  have hlambda1 : lambda ≤ 1 := by
    dsimp only [lambda]
    unfold directNativeError
    exact min_le_left _ _
  have hpoint0 : 0 ≤ point := by
    dsimp [point, pauliBaselinePointError]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (zero_le_one.trans one_le_pauli_baseline_point_constant)
        (Real.rpow_nonneg he _))
  have hcollision0 : 0 ≤ collision := by dsimp [collision]; positivity
  have hrounding0 : 0 ≤ rounding := by
    dsimp [rounding]
    exact mul_nonneg (by norm_num) (native_rounding_error_nonneg hlambda0)
  have hM0 : 0 ≤ M := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension]
    positivity
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hM1 : 1 ≤ M := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension, m, d] at hm hd ⊢
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hm (by norm_num)) (Real.one_le_rpow hd (by norm_num))
  have hlambdaLeEighth : lambda ≤ Real.rpow lambda (1 / 8 : ℝ) := by
    calc
      lambda = Real.rpow lambda 1 := (Real.rpow_one lambda).symm
      _ ≤ Real.rpow lambda (1 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hlambda0 hlambda1
          (by norm_num) (by norm_num)
  have hlambdaHalfLeEighth : Real.rpow lambda (1 / 2 : ℝ) ≤
      Real.rpow lambda (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hlambda0 hlambda1
      (by norm_num) (by norm_num)
  have hsqrt220 : Real.sqrt 220 ≤ 15 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsqrt2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hlambdaEighth0 : 0 ≤ Real.rpow lambda (1 / 8 : ℝ) :=
    Real.rpow_nonneg hlambda0 _
  have hlambdaHalf0 : 0 ≤ Real.rpow lambda (1 / 2 : ℝ) :=
    Real.rpow_nonneg hlambda0 _
  have hlambdaSixteenth0 : 0 ≤ Real.rpow lambda (1 / 16 : ℝ) :=
    Real.rpow_nonneg hlambda0 _
  have hrounding : rounding ≤ 608 * Real.rpow lambda (1 / 8 : ℝ) := by
    dsimp [rounding, nativeRoundingError]
    calc
      32 * (lambda + Real.sqrt 220 * Real.rpow lambda (1 / 8 : ℝ) +
          2 * Real.sqrt 2 * Real.rpow lambda (1 / 2 : ℝ)) ≤
          32 * (Real.rpow lambda (1 / 8 : ℝ) +
            15 * Real.rpow lambda (1 / 8 : ℝ) +
            2 * (3 / 2 : ℝ) * Real.rpow lambda (1 / 8 : ℝ)) := by
        gcongr
      _ = 608 * Real.rpow lambda (1 / 8 : ℝ) := by ring
  have hsplit : Real.sqrt
      (nativeGlobalPairError P lambda (pauliBaselinePointError e)) ≤
        Real.sqrt (min 1 rounding) + Real.sqrt (min 1 point) +
          Real.sqrt (min 1 collision) := by
    have hmin : min 1 (rounding + point + collision) ≤
        min 1 rounding + min 1 point + min 1 collision := by
      calc
        min 1 (rounding + point + collision) ≤
            min 1 (rounding + point) + min 1 collision :=
          min_one_add_le_add_min_one (add_nonneg hrounding0 hpoint0) hcollision0
        _ ≤ (min 1 rounding + min 1 point) + min 1 collision := by
          gcongr
          exact min_one_add_le_add_min_one hrounding0 hpoint0
    unfold nativeGlobalPairError nativeGlobalPairRawError
    change Real.sqrt (min 1 (rounding + point + collision)) ≤ _
    calc
      Real.sqrt (min 1 (rounding + point + collision)) ≤
          Real.sqrt (min 1 rounding + min 1 point + min 1 collision) :=
        Real.sqrt_le_sqrt hmin
      _ ≤ Real.sqrt (min 1 rounding + min 1 point) +
          Real.sqrt (min 1 collision) := by
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow
            (add_nonneg (by positivity) (by positivity)) (by positivity)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ ≤ (Real.sqrt (min 1 rounding) + Real.sqrt (min 1 point)) +
          Real.sqrt (min 1 collision) := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow (by positivity) (by positivity)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hlambdaBase := quantitative_native_error_one_sixteenth_le_fractional_base
    P e he he1
  have hlambdaBase' : Real.rpow lambda (1 / 16 : ℝ) ≤ 12 * M * F := by
    simpa only [r, passing, lambda, M, F] using hlambdaBase
  have hsqrt608 : Real.sqrt 608 ≤ 25 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hroundingRoot : Real.sqrt (min 1 rounding) ≤ 300 * M * F := by
    calc
      Real.sqrt (min 1 rounding) ≤
          Real.sqrt (608 * Real.rpow lambda (1 / 8 : ℝ)) :=
        Real.sqrt_le_sqrt ((min_le_right 1 rounding).trans hrounding)
      _ = Real.sqrt 608 * Real.rpow lambda (1 / 16 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), sqrt_rpow_eq hlambda0]
        congr 2
        ring
      _ ≤ 25 * Real.rpow lambda (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt608 hlambdaSixteenth0
      _ ≤ 25 * (12 * M * F) :=
        mul_le_mul_of_nonneg_left hlambdaBase' (by norm_num)
      _ = 300 * M * F := by ring
  have hpointCoefficient0 : 0 ≤ 64 * pauliBaselinePointConstant := by
    exact mul_nonneg (by norm_num)
      (zero_le_one.trans one_le_pauli_baseline_point_constant)
  have hpointCoefficient :
      Real.rpow (64 * pauliBaselinePointConstant) (1 / 56 : ℝ) ≤ 2 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 56 : ℝ) = (56 : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_le_iff_of_pos hpointCoefficient0 (by norm_num) (by norm_num)]
    calc
      64 * pauliBaselinePointConstant ≤ 64 * (1000000000000000 : ℝ) := by
        gcongr
        exact pauli_baseline_point_constant_le
      _ ≤ (2 : ℝ) ^ (56 : ℕ) := by norm_num
      _ = Real.rpow 2 (56 : ℝ) := (Real.rpow_natCast 2 56).symm
  have hePoint : Real.rpow e (1 / 448 : ℝ) ≤ Real.rpow e b := by
    exact Real.rpow_le_rpow_of_exponent_ge' he he1
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
  have heF : Real.rpow e b ≤ F := by
    dsimp [F, b, pauliSoundnessQuantitativeEnvelope]
    exact (le_add_of_nonneg_right (Real.rpow_nonneg hq0 _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have hePointRoot : (Real.rpow e (1 / 8 : ℝ)) ^ (1 / 56 : ℝ) =
      Real.rpow e (1 / 448 : ℝ) := by
    calc
      (Real.rpow e (1 / 8 : ℝ)) ^ (1 / 56 : ℝ) =
          Real.rpow e ((1 / 8 : ℝ) * (1 / 56 : ℝ)) :=
        (Real.rpow_mul he _ _).symm
      _ = Real.rpow e (1 / 448 : ℝ) := by congr 1; ring
  have hpointRoot : Real.sqrt (min 1 point) ≤ 2 * M * F := by
    have hcap := sqrt_min_one_le_rpow hpoint0
      (show (0 : ℝ) ≤ 1 / 56 by norm_num) (show (1 / 56 : ℝ) ≤ 1 / 2 by norm_num)
    calc
      Real.sqrt (min 1 point) ≤ Real.rpow point (1 / 56 : ℝ) := hcap
      _ = Real.rpow ((64 * pauliBaselinePointConstant) *
          Real.rpow e (1 / 8 : ℝ)) (1 / 56 : ℝ) := by
        dsimp [point, pauliBaselinePointError]
        congr 1
        ring
      _ = Real.rpow (64 * pauliBaselinePointConstant) (1 / 56 : ℝ) *
          Real.rpow e (1 / 448 : ℝ) := by
        calc
          _ = (64 * pauliBaselinePointConstant) ^ (1 / 56 : ℝ) *
              (Real.rpow e (1 / 8 : ℝ)) ^ (1 / 56 : ℝ) :=
            Real.mul_rpow hpointCoefficient0 (Real.rpow_nonneg he _)
          _ = _ := by
            simpa only [Real.rpow_eq_pow] using congrArg
              (fun x : ℝ => (64 * pauliBaselinePointConstant) ^ (1 / 56 : ℝ) * x)
              hePointRoot
      _ ≤ 2 * Real.rpow e (1 / 448 : ℝ) :=
        mul_le_mul_of_nonneg_right hpointCoefficient (Real.rpow_nonneg he _)
      _ ≤ 2 * Real.rpow e b :=
        mul_le_mul_of_nonneg_left hePoint (by norm_num)
      _ ≤ 2 * (M * F) := by
        gcongr
        exact heF.trans (le_mul_of_one_le_left hF0 hM1)
      _ = 2 * M * F := by ring
  have hcollisionCoefficient : collision ≤ 30 * r := by
    dsimp [collision, r]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have hthirty : Real.rpow 30 b ≤ 2 := by
    calc
      Real.rpow 30 b ≤ Real.rpow 30 (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      _ ≤ 2 := by
        simp only [Real.rpow_eq_pow]
        rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num,
          Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
        norm_num
  have hrb : Real.rpow r b =
      Real.rpow m b * Real.rpow d b * Real.rpow q (-b) := by
    calc
      r ^ b = (m * d / q) ^ b := by rw [hrEq]
      _ = (m * d) ^ b / q ^ b := Real.div_rpow (mul_nonneg hm0 hd0) hq0 b
      _ = m ^ b * d ^ b * q ^ (-b) := by
        rw [Real.mul_rpow hm0 hd0, div_eq_mul_inv, Real.rpow_neg hq0]
  have hdimension : Real.rpow m b * Real.rpow d b ≤ M := by
    dsimp [M, m, d, pauliSoundnessQuantitativeFractionalDimension]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hm
        (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num))
      (Real.rpow_le_rpow_of_exponent_le hd
        (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num))
      (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hm0 _)
  have hqF : Real.rpow q (-b) ≤ F := by
    dsimp [F, b, q, pauliSoundnessQuantitativeEnvelope]
    exact (le_add_of_nonneg_left (Real.rpow_nonneg he _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have hcollisionRoot : Real.sqrt (min 1 collision) ≤ 2 * M * F := by
    have hcap := sqrt_min_one_le_rpow hcollision0
      (show 0 ≤ b by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      (show b ≤ 1 / 2 by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
    calc
      Real.sqrt (min 1 collision) ≤ Real.rpow collision b := hcap
      _ ≤ Real.rpow (30 * r) b :=
        Real.rpow_le_rpow hcollision0 hcollisionCoefficient
          (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      _ = Real.rpow 30 b * Real.rpow r b := by
        exact Real.mul_rpow (by norm_num) hr
      _ = Real.rpow 30 b *
          ((Real.rpow m b * Real.rpow d b) * Real.rpow q (-b)) := by
        rw [hrb]
      _ ≤ 2 *
          ((Real.rpow m b * Real.rpow d b) * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_right hthirty
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hd0 _))
            (Real.rpow_nonneg hq0 _))
      _ ≤ 2 * (M * Real.rpow q (-b)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdimension (Real.rpow_nonneg hq0 _))
          (by norm_num)
      _ ≤ 2 * (M * F) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqF hM0) (by norm_num)
      _ = 2 * M * F := by ring
  calc
    Real.sqrt (nativeGlobalPairError P lambda (pauliBaselinePointError e)) ≤
        Real.sqrt (min 1 rounding) + Real.sqrt (min 1 point) +
          Real.sqrt (min 1 collision) := hsplit
    _ ≤ 300 * M * F + 2 * M * F + 2 * M * F := by gcongr
    _ = 304 * M * F := by ring
    _ = 304 * pauliSoundnessQuantitativeFractionalDimension P *
        pauliSoundnessQuantitativeEnvelope P e := by rfl

/-- Squaring the exact native global-pair root estimate gives a bound with the
fractional dimension factor squared and the error-envelope exponent doubled on
all three terms. -/
theorem quantitative_native_global_pair_error_le_fractional
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    let lambda := directNativeError P.extendedDirectLd passing
    nativeGlobalPairError P lambda (pauliBaselinePointError e) ≤
      277248 * Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
        Real.rpow (P.d : ℝ) (1 / 32 : ℝ) *
          quantitativeGlobalPairEnvelope P e := by
  intro r passing lambda
  let G := nativeGlobalPairError P lambda (pauliBaselinePointError e)
  let M := pauliSoundnessQuantitativeFractionalDimension P
  let F := pauliSoundnessQuantitativeEnvelope P e
  let E := quantitativeGlobalPairEnvelope P e
  let x := Real.rpow e pauliSoundnessQuantitativePower
  let y := Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower)
  let z := Real.rpow 2
    (-(pauliSoundnessQuantitativePower * ((P.m * P.d : ℕ) : ℝ)))
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
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact native_global_pair_error_nonneg P hlambda hpoint
  have hM0 : 0 ≤ M := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension]
    positivity
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hroot := quantitative_native_global_pair_sqrt_le_fractional_base P e he he1
  have hroot' : Real.sqrt G ≤ 304 * M * F := by
    simpa only [r, passing, lambda, G, M, F] using hroot
  have hGsquare : G ≤ (304 * M * F) ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt hG0, Real.sqrt_nonneg G]
  have hMsquare : M ^ (2 : ℕ) =
      Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
        Real.rpow (P.d : ℝ) (1 / 32 : ℝ) := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension]
    rw [mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (P.m : ℝ))]
      congr 1
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (P.d : ℝ))]
      congr 1
      norm_num
  have hxSquare : x ^ (2 : ℕ) = Real.rpow e quantitativeGlobalPairPower := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul he]
    congr 1
    unfold pauliSoundnessQuantitativePower quantitativeGlobalPairPower
    norm_num
  have hySquare : y ^ (2 : ℕ) =
      Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (P.q : ℝ))]
    congr 1
    unfold pauliSoundnessQuantitativePower quantitativeGlobalPairPower
    norm_num
  have hzSquare : z ^ (2 : ℕ) = Real.rpow 2
      (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ))) := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    unfold pauliSoundnessQuantitativePower quantitativeGlobalPairPower
    ring
  have hthree : (x + y + z) ^ (2 : ℕ) ≤
      3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  have hFsquare : F ^ (2 : ℕ) ≤ 3 * E := by
    change (x + y + z) ^ (2 : ℕ) ≤ 3 * E
    calc
      (x + y + z) ^ (2 : ℕ) ≤
          3 * (x ^ (2 : ℕ) + y ^ (2 : ℕ) + z ^ (2 : ℕ)) := hthree
      _ = 3 * E := by
        rw [hxSquare, hySquare, hzSquare]
        rfl
  have hK0 : 0 ≤ Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
      Real.rpow (P.d : ℝ) (1 / 32 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hE0 : 0 ≤ E := by dsimp [E, quantitativeGlobalPairEnvelope]; positivity
  calc
    G ≤ (304 * M * F) ^ (2 : ℕ) := hGsquare
    _ = 92416 * M ^ (2 : ℕ) * F ^ (2 : ℕ) := by ring
    _ = 92416 *
        (Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
          Real.rpow (P.d : ℝ) (1 / 32 : ℝ)) * F ^ (2 : ℕ) := by rw [hMsquare]
    _ ≤ 92416 *
        (Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
          Real.rpow (P.d : ℝ) (1 / 32 : ℝ)) * (3 * E) := by
      gcongr
    _ = 277248 * Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
        Real.rpow (P.d : ℝ) (1 / 32 : ℝ) * E := by ring
    _ = 277248 * Real.rpow (P.m : ℝ) (20481 / 131072 : ℝ) *
        Real.rpow (P.d : ℝ) (1 / 32 : ℝ) *
          quantitativeGlobalPairEnvelope P e := by rfl

end

end MIPStarRE.QPBT
