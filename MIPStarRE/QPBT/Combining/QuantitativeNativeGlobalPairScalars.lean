module

public import MIPStarRE.QPBT.Combining.QuantitativeNativeScalars

/-!
# Separated native global-pair bounds for QPBT

This module bounds the exact native global polynomial-pair error by replacing
only the three powers of the native direct low-degree error.  The point error
and finite-field collision term remain unchanged.

## References

* Paper `lem:qld-4-7`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* Blueprint `thm:qld-native-small-regime-global-pair`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The separated global-pair error obtained from the native-power bounds.
The point and collision contributions are retained exactly. -/
def quantitativeNativeGlobalPairSeparatedError
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  min 1
    (32 * quantitativeNativeSeparatedError P e 1 +
      32 * Real.sqrt 220 * quantitativeNativeSeparatedError P e (1 / 8 : ℝ) +
      64 * Real.sqrt 2 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) +
      64 * pauliBaselinePointError e +
      (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q))

/-- The exact native global-pair error is bounded by the separated expression
without changing its point or collision contributions. -/
theorem quantitative_native_global_pair_error_le_separated
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    let lambda := directNativeError P.extendedDirectLd passing
    nativeGlobalPairError P lambda (pauliBaselinePointError e) ≤
      quantitativeNativeGlobalPairSeparatedError P e := by
  intro r passing lambda
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact direct_native_error_nonneg _ hpassing
  have h1 := quantitative_native_error_rpow_le_separated P e 1 he
    (by norm_num) (by norm_num)
  have h18 := quantitative_native_error_rpow_le_separated P e (1 / 8 : ℝ) he
    (by norm_num) (by norm_num)
  have h12 := quantitative_native_error_rpow_le_separated P e (1 / 2 : ℝ) he
    (by norm_num) (by norm_num)
  have h1' : lambda ≤ quantitativeNativeSeparatedError P e 1 := by
    calc
      lambda = Real.rpow lambda 1 := (Real.rpow_one lambda).symm
      _ ≤ quantitativeNativeSeparatedError P e 1 := by
        simpa only [r, passing, lambda] using h1
  have h18' : Real.rpow lambda (1 / 8 : ℝ) ≤
      quantitativeNativeSeparatedError P e (1 / 8 : ℝ) := by
    simpa only [r, passing, lambda] using h18
  have h12' : Real.rpow lambda (1 / 2 : ℝ) ≤
      quantitativeNativeSeparatedError P e (1 / 2 : ℝ) := by
    simpa only [r, passing, lambda] using h12
  have hround : 32 * nativeRoundingError lambda ≤
      32 * quantitativeNativeSeparatedError P e 1 +
        32 * Real.sqrt 220 * quantitativeNativeSeparatedError P e (1 / 8 : ℝ) +
        64 * Real.sqrt 2 * quantitativeNativeSeparatedError P e (1 / 2 : ℝ) := by
    unfold nativeRoundingError
    calc
      32 * (lambda + Real.sqrt 220 * Real.rpow lambda (1 / 8 : ℝ) +
          2 * Real.sqrt 2 * Real.rpow lambda (1 / 2 : ℝ)) =
          32 * lambda + 32 * Real.sqrt 220 * Real.rpow lambda (1 / 8 : ℝ) +
            64 * Real.sqrt 2 * Real.rpow lambda (1 / 2 : ℝ) := by ring
      _ ≤ _ := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left h1' (by norm_num))
            (mul_le_mul_of_nonneg_left h18'
              (mul_nonneg (by norm_num) (Real.sqrt_nonneg 220))))
          (mul_le_mul_of_nonneg_left h12'
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)))
  unfold nativeGlobalPairError quantitativeNativeGlobalPairSeparatedError
  apply min_le_min_left 1
  unfold nativeGlobalPairRawError
  exact add_le_add (add_le_add hround le_rfl) le_rfl

end

end MIPStarRE.QPBT
