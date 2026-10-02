module

public import MIPStarRE.QPBT.Combining.QuantitativeNativeGlobalPairScalars
public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.Bounds

/-!
# Separated native extraction bounds for Pauli soundness

This module propagates the separated native global-pair estimate to the
extraction scale and its square root.  The resulting bounds keep the direct
low-degree powers, point error, collision term, clipped source error, and
field ratio as distinct summands.

## References

* Paper `lem:qld-unitary`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
* Blueprint `def:pauli-final-fractional-error`
* Blueprint `thm:pauli-final-fractional-scalar-support`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The separated upper bound for the native extraction scale. -/
def pauliSoundnessQuantitativeSeparatedScale
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  2800 * (quantitativeNativeGlobalPairSeparatedError P e + Real.sqrt e + r)

/-- The separated upper bound for the square root of the native extraction
scale. -/
def pauliSoundnessQuantitativeSeparatedRoot
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let collision : ℝ :=
    (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)
  Real.sqrt 2800 *
    (Real.sqrt 32 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
      Real.sqrt (32 * Real.sqrt 220) *
        quantitativeNativeSeparatedError P e (1 / 16 : ℝ) +
      Real.sqrt (64 * Real.sqrt 2) *
        quantitativeNativeSeparatedError P e (1 / 4 : ℝ) +
      8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision +
      Real.rpow e (1 / 4 : ℝ) + Real.sqrt r)

/-- The exact native extraction scale and its square root are bounded by the
separated certificates `Y` and `Z`. -/
theorem quantitative_native_extraction_scale_bounds
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    pauliSoundnessQuantitativeMixedScale P e ≤
        pauliSoundnessQuantitativeSeparatedScale P e ∧
      Real.sqrt (pauliSoundnessQuantitativeMixedScale P e) ≤
        pauliSoundnessQuantitativeSeparatedRoot P e := by
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError e + (P.m : ℝ) *
      pauliBaselineExtendedLineError e r) r
  let lambda := directNativeError P.extendedDirectLd passing
  let G := nativeGlobalPairError P lambda (pauliBaselinePointError e)
  let collision : ℝ :=
    (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact direct_native_error_nonneg _ hpassing
  have hpoint : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  have hcollision : 0 ≤ collision := by dsimp [collision]; positivity
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact native_global_pair_error_nonneg P hlambda hpoint
  have hGsep := quantitative_native_global_pair_error_le_separated P e he
  have hGsep' : G ≤ quantitativeNativeGlobalPairSeparatedError P e := by
    simpa only [r, passing, lambda, G] using hGsep
  have h12 := quantitative_native_error_rpow_le_separated P e (1 / 2 : ℝ) he
    (by norm_num) (by norm_num)
  have h116 := quantitative_native_error_rpow_le_separated P e (1 / 16 : ℝ) he
    (by norm_num) (by norm_num)
  have h14 := quantitative_native_error_rpow_le_separated P e (1 / 4 : ℝ) he
    (by norm_num) (by norm_num)
  have h12' : Real.rpow lambda (1 / 2 : ℝ) ≤
      quantitativeNativeSeparatedError P e (1 / 2 : ℝ) := by
    simpa only [r, passing, lambda] using h12
  have h116' : Real.rpow lambda (1 / 16 : ℝ) ≤
      quantitativeNativeSeparatedError P e (1 / 16 : ℝ) := by
    simpa only [r, passing, lambda] using h116
  have h14' : Real.rpow lambda (1 / 4 : ℝ) ≤
      quantitativeNativeSeparatedError P e (1 / 4 : ℝ) := by
    simpa only [r, passing, lambda] using h14
  let a := 32 * lambda
  let b := 32 * Real.sqrt 220 * Real.rpow lambda (1 / 8 : ℝ)
  let c := 64 * Real.sqrt 2 * Real.rpow lambda (1 / 2 : ℝ)
  let d := 64 * pauliBaselinePointError e
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hrawEq : nativeGlobalPairRawError P lambda (pauliBaselinePointError e) =
      a + b + c + d + collision := by
    dsimp [a, b, c, d, collision]
    unfold nativeGlobalPairRawError nativeRoundingError
    simp only [Real.rpow_eq_pow]
    ring
  have hsqrtA : Real.sqrt a =
      Real.sqrt 32 * Real.rpow lambda (1 / 2 : ℝ) := by
    dsimp [a]
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    exact Real.sqrt_eq_rpow lambda
  have hsqrtB : Real.sqrt b =
      Real.sqrt (32 * Real.sqrt 220) * Real.rpow lambda (1 / 16 : ℝ) := by
    dsimp [b]
    rw [Real.sqrt_mul (by positivity)]
    have hroot := sqrt_rpow_eq (x := lambda) (a := (1 / 8 : ℝ)) hlambda
    simp only [Real.rpow_eq_pow] at hroot ⊢
    rw [hroot]
    congr 1
    ring
  have hsqrtC : Real.sqrt c =
      Real.sqrt (64 * Real.sqrt 2) * Real.rpow lambda (1 / 4 : ℝ) := by
    dsimp [c]
    rw [Real.sqrt_mul (by positivity)]
    have hroot := sqrt_rpow_eq (x := lambda) (a := (1 / 2 : ℝ)) hlambda
    simp only [Real.rpow_eq_pow] at hroot ⊢
    rw [hroot]
    congr 1
    ring
  have hsqrtD : Real.sqrt d = 8 * Real.sqrt (pauliBaselinePointError e) := by
    dsimp [d]
    rw [Real.sqrt_mul (by norm_num)]
    norm_num
  have hrawSplit : Real.sqrt (a + b + c + d + collision) ≤
      Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d +
        Real.sqrt collision := by
    calc
      Real.sqrt (a + b + c + d + collision) ≤
          Real.sqrt (a + b + c + d) + Real.sqrt collision := by
          simpa only [Real.sqrt_eq_rpow] using
            Real.rpow_add_le_add_rpow
              (add_nonneg (add_nonneg (add_nonneg ha hb) hc) hd) hcollision
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ ≤ (Real.sqrt (a + b + c) + Real.sqrt d) + Real.sqrt collision := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow (add_nonneg (add_nonneg ha hb) hc) hd
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ ≤ ((Real.sqrt (a + b) + Real.sqrt c) + Real.sqrt d) +
          Real.sqrt collision := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ ≤ (((Real.sqrt a + Real.sqrt b) + Real.sqrt c) + Real.sqrt d) +
          Real.sqrt collision := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow ha hb
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ = _ := by ring
  have hrootG : Real.sqrt G ≤
      Real.sqrt 32 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
        Real.sqrt (32 * Real.sqrt 220) *
          quantitativeNativeSeparatedError P e (1 / 16 : ℝ) +
        Real.sqrt (64 * Real.sqrt 2) *
          quantitativeNativeSeparatedError P e (1 / 4 : ℝ) +
        8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision := by
    calc
      Real.sqrt G ≤ Real.sqrt
          (nativeGlobalPairRawError P lambda (pauliBaselinePointError e)) :=
        Real.sqrt_le_sqrt (min_le_right 1 _)
      _ = Real.sqrt (a + b + c + d + collision) := by rw [hrawEq]
      _ ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d +
          Real.sqrt collision := hrawSplit
      _ = Real.sqrt 32 * Real.rpow lambda (1 / 2 : ℝ) +
          Real.sqrt (32 * Real.sqrt 220) * Real.rpow lambda (1 / 16 : ℝ) +
          Real.sqrt (64 * Real.sqrt 2) * Real.rpow lambda (1 / 4 : ℝ) +
          8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision := by
        rw [hsqrtA, hsqrtB, hsqrtC, hsqrtD]
      _ ≤ Real.sqrt 32 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
          Real.sqrt (32 * Real.sqrt 220) * Real.rpow lambda (1 / 16 : ℝ) +
          Real.sqrt (64 * Real.sqrt 2) * Real.rpow lambda (1 / 4 : ℝ) +
          8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision := by
        gcongr
      _ ≤ Real.sqrt 32 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
          Real.sqrt (32 * Real.sqrt 220) *
            quantitativeNativeSeparatedError P e (1 / 16 : ℝ) +
          Real.sqrt (64 * Real.sqrt 2) * Real.rpow lambda (1 / 4 : ℝ) +
          8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision := by
        gcongr
      _ ≤ _ := by gcongr
  have hsqrtSqrt : Real.sqrt (Real.sqrt e) = Real.rpow e (1 / 4 : ℝ) := by
    have heRoot := Real.sqrt_eq_rpow e
    have hquarter := sqrt_rpow_eq (x := e) (a := (1 / 2 : ℝ)) he
    calc
      Real.sqrt (Real.sqrt e) = Real.sqrt (Real.rpow e (1 / 2 : ℝ)) := by
        exact congrArg Real.sqrt heRoot
      _ = Real.rpow e ((1 / 2 : ℝ) / 2) := hquarter
      _ = Real.rpow e (1 / 4 : ℝ) := by congr 1; ring
  constructor
  · unfold pauliSoundnessQuantitativeMixedScale
      pauliSoundnessQuantitativeSeparatedScale
    change 2800 * (G + Real.sqrt e + r) ≤
      2800 * (quantitativeNativeGlobalPairSeparatedError P e + Real.sqrt e + r)
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hGsep' le_rfl) le_rfl) (by norm_num)
  · unfold pauliSoundnessQuantitativeMixedScale
      pauliSoundnessQuantitativeSeparatedRoot
    change Real.sqrt (2800 * (G + Real.sqrt e + r)) ≤ Real.sqrt 2800 *
      (Real.sqrt 32 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
        Real.sqrt (32 * Real.sqrt 220) *
          quantitativeNativeSeparatedError P e (1 / 16 : ℝ) +
        Real.sqrt (64 * Real.sqrt 2) *
          quantitativeNativeSeparatedError P e (1 / 4 : ℝ) +
        8 * Real.sqrt (pauliBaselinePointError e) + Real.sqrt collision +
        Real.rpow e (1 / 4 : ℝ) + Real.sqrt r)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2800)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2800)
    calc
      Real.sqrt (G + Real.sqrt e + r) ≤
          Real.sqrt (G + Real.sqrt e) + Real.sqrt r := by
          simpa only [Real.sqrt_eq_rpow] using
            Real.rpow_add_le_add_rpow (add_nonneg hG (Real.sqrt_nonneg e)) hr
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ ≤ Real.sqrt G + Real.sqrt (Real.sqrt e) + Real.sqrt r := by
        gcongr
        simpa only [Real.sqrt_eq_rpow] using
          Real.rpow_add_le_add_rpow hG (Real.sqrt_nonneg e)
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      _ = Real.sqrt G + Real.rpow e (1 / 4 : ℝ) + Real.sqrt r := by
        rw [hsqrtSqrt]
      _ ≤ _ := by linarith

end

end MIPStarRE.QPBT
