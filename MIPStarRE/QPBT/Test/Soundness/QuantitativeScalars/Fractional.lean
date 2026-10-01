module

public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.NativeSeparated

/-!
# Fractional-dimensional quantitative Pauli soundness scalars

This module collapses the separated native error terms only at the terminal
common-error corollary.  It retains the exponent `1 / 67108864` and the
fractional dimension factor `m^(20481/262144) d^(1/64)`.

## References

* Paper `thm:pauli`,
  `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1491`
* Paper `lem:qld-unitary`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
* Blueprint `def:pauli-final-fractional-error`
* Blueprint `thm:pauli-final-fractional-scalar-support`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The uncapped terminal common error obtained from the native scalar
calculation. -/
def pauliSoundnessQuantitativeFractionalRawError
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  10769120 * pauliSoundnessQuantitativeFractionalDimension P *
    pauliSoundnessQuantitativeEnvelope P e

/-- The terminal fractional-dimensional common error, with source clipping
and the universal cap applied. -/
def pauliSoundnessQuantitativeFractionalError
    (P : AdmissibleParams) (epsilon : ℝ) : ℝ :=
  min 4 (pauliSoundnessQuantitativeFractionalRawError P (min epsilon 1))


/-- On the small field-ratio branch, the square root of the exact extraction
scale is bounded by `16218 M E_b`. -/
theorem quantitative_native_extraction_sqrt_le_fractional_base
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr1 : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1) :
    Real.sqrt (pauliSoundnessQuantitativeMixedScale P e) ≤
      16218 * pauliSoundnessQuantitativeFractionalDimension P *
        pauliSoundnessQuantitativeEnvelope P e := by
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError e + (P.m : ℝ) * pauliBaselineExtendedLineError e r) r
  let lambda := directNativeError P.extendedDirectLd passing
  let G := nativeGlobalPairError P lambda (pauliBaselinePointError e)
  let b : ℝ := pauliSoundnessQuantitativePower
  let M : ℝ := pauliSoundnessQuantitativeFractionalDimension P
  let F : ℝ := pauliSoundnessQuantitativeEnvelope P e
  let m : ℝ := P.m
  let d : ℝ := P.d
  let q : ℝ := P.q
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
  have hr1' : r ≤ 1 := by simpa only [r] using hr1
  have hrEq : r = m * d / q := by
    dsimp [r, m, d, q]
    push_cast
    rfl
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
  have hM1 : 1 ≤ M := by
    dsimp [M, pauliSoundnessQuantitativeFractionalDimension, m, d] at hm hd ⊢
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hm (by norm_num)) (Real.one_le_rpow hd (by norm_num))
  have hGroot := quantitative_native_global_pair_sqrt_le_fractional_base P e he he1
  have hGroot' : Real.sqrt G ≤ 304 * M * F := by
    simpa only [r, passing, lambda, G, M, F] using hGroot
  have hsqrt2800 : Real.sqrt 2800 ≤ 53 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsqrtSqrt : Real.sqrt (Real.sqrt e) = Real.rpow e (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact (Real.rpow_mul he (1 / 2 : ℝ) (1 / 2 : ℝ)).symm.trans
      (by congr 1; ring)
  have heQuarter : Real.rpow e (1 / 4 : ℝ) ≤ Real.rpow e b :=
    Real.rpow_le_rpow_of_exponent_ge' he he1
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
  have heF : Real.rpow e b ≤ F := by
    dsimp [F, b, pauliSoundnessQuantitativeEnvelope]
    exact (le_add_of_nonneg_right (Real.rpow_nonneg hq0 _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have heTerm : Real.rpow e (1 / 4 : ℝ) ≤ M * F :=
    heQuarter.trans (heF.trans (le_mul_of_one_le_left hF0 hM1))
  have hrRoot : Real.sqrt r ≤ Real.rpow r b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hr hr1'
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
      (by dsimp [b, pauliSoundnessQuantitativePower]; norm_num)
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
  have hrTerm : Real.sqrt r ≤ M * F := by
    calc
      Real.sqrt r ≤ Real.rpow r b := hrRoot
      _ = (Real.rpow m b * Real.rpow d b) * Real.rpow q (-b) := by
        rw [hrb]
      _ ≤ M * Real.rpow q (-b) :=
        mul_le_mul_of_nonneg_right hdimension (Real.rpow_nonneg hq0 _)
      _ ≤ M * F := mul_le_mul_of_nonneg_left hqF hM0
  unfold pauliSoundnessQuantitativeMixedScale
  change Real.sqrt (2800 * (G + Real.sqrt e + r)) ≤ 16218 * M * F
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2800)]
  calc
    Real.sqrt 2800 * Real.sqrt (G + Real.sqrt e + r) ≤
        53 * Real.sqrt (G + Real.sqrt e + r) :=
      mul_le_mul_of_nonneg_right hsqrt2800 (Real.sqrt_nonneg _)
    _ ≤ 53 * (Real.sqrt G + Real.rpow e (1 / 4 : ℝ) + Real.sqrt r) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        Real.sqrt (G + Real.sqrt e + r) ≤
            Real.sqrt (G + Real.sqrt e) + Real.sqrt r := by
            simpa only [Real.sqrt_eq_rpow] using
              Real.rpow_add_le_add_rpow (add_nonneg hG0 (Real.sqrt_nonneg e)) hr
                (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        _ ≤ (Real.sqrt G + Real.sqrt (Real.sqrt e)) + Real.sqrt r := by
          gcongr
          simpa only [Real.sqrt_eq_rpow] using
            Real.rpow_add_le_add_rpow hG0 (Real.sqrt_nonneg e)
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        _ = Real.sqrt G + Real.rpow e (1 / 4 : ℝ) + Real.sqrt r := by rw [hsqrtSqrt]
    _ ≤ 53 * (304 * M * F + M * F + M * F) := by gcongr
    _ = 16218 * M * F := by ring

end

end MIPStarRE.QPBT
