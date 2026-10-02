module

public import MIPStarRE.LDT.Test.MainTheorem.LinearTriangle.MainFormal
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# Direct quantitative scalar bounds for QPBT

This module imports the complete-measurement linear-triangle improvement of the
low individual degree test into the one-coordinate QPBT low-degree test. It
contains the coefficient-`30` specialization and the three quantitative powers
shared with the subsequent global-pair calculation.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/ldt-paper/test_definition.tex:180-202`
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The exponent supplied by the complete-measurement linear-triangle LDT bound. -/
def quantitativeLowDegreePower : ℝ := 1 / 8192

/-- The exponent after the eighth-root projective-rounding step. -/
def quantitativeGlobalPairPower : ℝ := 1 / 33554432

/-- The exponent before the eighth-root projective-rounding loss. -/
def quantitativePreRoundingPower : ℝ := 1 / 4194304

/-- The three-term error envelope used by the coefficient-`30` direct LDT
specialization. -/
def directQuantitativeEnvelope (D : DirectLdParams) (ε : ℝ) : ℝ :=
  Real.rpow ε quantitativeLowDegreePower +
    Real.rpow (D.q : ℝ) (-quantitativeLowDegreePower) +
    Real.rpow 2
      (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ)))

/-- The exact capped error obtained by applying the complete-measurement
linear-triangle theorem at the direct-game auxiliary sample count. -/
def directNativeError (D : DirectLdParams) (ε : ℝ) : ℝ :=
  min 1 (400000 * Real.rpow (D.m : ℝ) (5 / 4 : ℝ) *
    Real.rpow (D.d : ℝ) (1 / 4 : ℝ) *
      (Real.rpow (3 * ε) quantitativeLowDegreePower +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower +
        Real.exp (-(4 * (D.m : ℝ) * (D.d : ℝ)))))

/-- The error introduced by same-space projective rounding at a supplied
direct low-degree error. -/
def nativeRoundingError (delta : ℝ) : ℝ :=
  delta + Real.sqrt 220 * Real.rpow delta (1 / 8 : ℝ) +
    2 * Real.sqrt 2 * Real.rpow delta (1 / 2 : ℝ)

/-- The common ordered polynomial error after projective rounding. -/
def nativeOrderedPolynomialError (delta deltaQ : ℝ) : ℝ :=
  4 * nativeRoundingError delta + 8 * deltaQ

/-- The uncapped error of the completed global polynomial-pair measurements. -/
def nativeGlobalPairRawError (P : AdmissibleParams) (delta deltaQ : ℝ) : ℝ :=
  32 * nativeRoundingError delta + 64 * deltaQ +
    (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)

/-- The unit-capped error of the completed global polynomial-pair measurements. -/
def nativeGlobalPairError (P : AdmissibleParams) (delta deltaQ : ℝ) : ℝ :=
  min 1 (nativeGlobalPairRawError P delta deltaQ)

/-- The three-term QPBT envelope before projective rounding. -/
def quantitativePreRoundingEnvelope (P : AdmissibleParams) (e : ℝ) : ℝ :=
  Real.rpow e quantitativePreRoundingPower +
    Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) +
    Real.rpow 2
      (-(quantitativePreRoundingPower * ((P.m * P.d : ℕ) : ℝ)))

/-- The three-term QPBT envelope after projective rounding. -/
def quantitativeGlobalPairEnvelope (P : AdmissibleParams) (e : ℝ) : ℝ :=
  Real.rpow e quantitativeGlobalPairPower +
    Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) +
    Real.rpow 2
      (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ)))

/-- The factor contributed by the incoming error `3 * ε` is at most two. -/
theorem three_rpow_quantitative_low_degree_power_le_two :
    Real.rpow 3 quantitativeLowDegreePower ≤ 2 := by
  calc
    Real.rpow 3 quantitativeLowDegreePower ≤
        Real.rpow 4 quantitativeLowDegreePower :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) (by
        unfold quantitativeLowDegreePower
        norm_num)
    _ = Real.rpow 2 (2 * quantitativeLowDegreePower) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
      symm
      exact Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 2
        quantitativeLowDegreePower
    _ ≤ Real.rpow 2 1 := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      unfold quantitativeLowDegreePower
      norm_num
    _ = 2 := Real.rpow_one 2

/-- The auxiliary LDT sampling parameter has decay argument `4 * m * d` at
the improved scale `640000 * m^2`. -/
theorem direct_ld_aux_parameter_linear_triangle_exp_arg (D : DirectLdParams) :
    (directLdAuxParameter D : ℝ) / (640000 * ((D.m : ℝ) ^ (2 : ℕ))) =
      4 * (D.m : ℝ) * (D.d : ℝ) := by
  have hm : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm
  have hne : (640000 : ℝ) * ((D.m : ℝ) ^ (2 : ℕ)) ≠ 0 := by positivity
  unfold directLdAuxParameter
  push_cast
  rw [div_eq_iff hne]
  ring

/-- The auxiliary sample count has exact fourth root
`40 * m^(3/4) * d^(1/4)`. -/
theorem direct_ld_aux_parameter_quarter_eq (D : DirectLdParams) :
    Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) =
      40 * Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
        Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
  have hm0 : (0 : ℝ) ≤ (D.m : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ (D.d : ℝ) := by positivity
  unfold directLdAuxParameter
  push_cast
  calc
    Real.rpow ((2560000 : ℝ) * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ))
        (1 / 4 : ℝ) =
        Real.rpow ((2560000 : ℝ) * (D.m : ℝ) ^ (3 : ℕ)) (1 / 4 : ℝ) *
          Real.rpow (D.d : ℝ) (1 / 4 : ℝ) :=
      Real.mul_rpow (mul_nonneg (by norm_num) (pow_nonneg hm0 3)) hd0
    _ = Real.rpow (2560000 : ℝ) (1 / 4 : ℝ) *
          Real.rpow ((D.m : ℝ) ^ (3 : ℕ)) (1 / 4 : ℝ) *
          Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
      congr 1
      exact Real.mul_rpow (by norm_num) (pow_nonneg hm0 3)
    _ = 40 * Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
          Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
      have h40 : Real.rpow (2560000 : ℝ) (1 / 4 : ℝ) = 40 := by
        rw [show (2560000 : ℝ) = (40 : ℝ) ^ (4 : ℕ) by norm_num]
        convert Real.pow_rpow_inv_natCast
          (show (0 : ℝ) ≤ 40 by norm_num) (show (4 : ℕ) ≠ 0 by norm_num) using 1
        norm_num
      have hm : Real.rpow ((D.m : ℝ) ^ (3 : ℕ)) (1 / 4 : ℝ) =
          Real.rpow (D.m : ℝ) (3 / 4 : ℝ) := by
        rw [← Real.rpow_natCast]
        calc
          Real.rpow (Real.rpow (D.m : ℝ) (3 : ℝ)) (1 / 4 : ℝ) =
              Real.rpow (D.m : ℝ) ((3 : ℝ) * (1 / 4 : ℝ)) :=
            (Real.rpow_mul hm0 _ _).symm
          _ = _ := by norm_num
      rw [h40, hm]

/-- The fourth root of the auxiliary sample count is bounded by
`40 * m * d`. -/
theorem direct_ld_aux_parameter_quarter_le (D : DirectLdParams) :
    Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) ≤
      40 * (D.m : ℝ) * (D.d : ℝ) := by
  have hm : (1 : ℝ) ≤ (D.m : ℝ) := by exact_mod_cast D.hm
  have hd : (1 : ℝ) ≤ (D.d : ℝ) := by exact_mod_cast D.hd
  have hmPow : (D.m : ℝ) ^ (3 : ℕ) ≤ (D.m : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_right₀ hm (by norm_num)
  have hdPow : (D.d : ℝ) ≤ (D.d : ℝ) ^ (4 : ℕ) := by
    simpa using pow_le_pow_right₀ hd (by norm_num : 1 ≤ 4)
  have hsample : (directLdAuxParameter D : ℝ) ≤
      (40 * (D.m : ℝ) * (D.d : ℝ)) ^ (4 : ℕ) := by
    unfold directLdAuxParameter
    push_cast
    calc
      (2560000 : ℝ) * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ) =
          (40 : ℝ) ^ (4 : ℕ) *
            ((D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ)) := by norm_num; ring
      _ ≤ (40 : ℝ) ^ (4 : ℕ) *
            ((D.m : ℝ) ^ (4 : ℕ) * (D.d : ℝ) ^ (4 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hmPow hdPow (by positivity) (by positivity)) (by positivity)
      _ = (40 * (D.m : ℝ) * (D.d : ℝ)) ^ (4 : ℕ) := by ring
  calc
    Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) ≤
        Real.rpow ((40 * (D.m : ℝ) * (D.d : ℝ)) ^ (4 : ℕ)) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hsample (by norm_num)
    _ = 40 * (D.m : ℝ) * (D.d : ℝ) := by
      convert Real.pow_rpow_inv_natCast
        (show 0 ≤ 40 * (D.m : ℝ) * (D.d : ℝ) by positivity)
        (show (4 : ℕ) ≠ 0 by norm_num) using 1
      all_goals norm_num

/-- A sharper fourth-root estimate retains the quarter power of the degree. -/
theorem direct_ld_aux_parameter_quarter_le_sharp (D : DirectLdParams) :
    Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) ≤
      40 * (D.m : ℝ) * Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
  have hm : (1 : ℝ) ≤ (D.m : ℝ) := by exact_mod_cast D.hm
  have hmPow : (D.m : ℝ) ^ (3 : ℕ) ≤ (D.m : ℝ) ^ (4 : ℕ) :=
    pow_le_pow_right₀ hm (by norm_num)
  have hsample : (directLdAuxParameter D : ℝ) ≤
      (40 * (D.m : ℝ)) ^ (4 : ℕ) * (D.d : ℝ) := by
    unfold directLdAuxParameter
    push_cast
    calc
      (2560000 : ℝ) * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ) =
          (40 : ℝ) ^ (4 : ℕ) * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ) := by
            norm_num
      _ ≤ (40 : ℝ) ^ (4 : ℕ) * (D.m : ℝ) ^ (4 : ℕ) * (D.d : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmPow (by positivity)) (by positivity)
      _ = (40 * (D.m : ℝ)) ^ (4 : ℕ) * (D.d : ℝ) := by ring
  calc
    Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) ≤
        Real.rpow ((40 * (D.m : ℝ)) ^ (4 : ℕ) * (D.d : ℝ)) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hsample (by norm_num)
    _ = Real.rpow ((40 * (D.m : ℝ)) ^ (4 : ℕ)) (1 / 4 : ℝ) *
        Real.rpow (D.d : ℝ) (1 / 4 : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    _ = 40 * (D.m : ℝ) * Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
      congr 1
      convert Real.pow_rpow_inv_natCast
        (show 0 ≤ 40 * (D.m : ℝ) by positivity)
        (show (4 : ℕ) ≠ 0 by norm_num) using 1
      norm_num

/-- The field term at the improved exponent separates into its degree and
field-size factors. -/
theorem direct_ld_field_term_quantitative_eq (D : DirectLdParams) :
    Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower =
      Real.rpow (D.d : ℝ) quantitativeLowDegreePower *
        Real.rpow (D.q : ℝ) (-quantitativeLowDegreePower) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (by positivity) (by positivity), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (D.q : ℝ))]

/-- The improved LDT exponential term is bounded by the base-two term of the
coefficient-`30` envelope. -/
theorem direct_ld_exponential_term_quantitative_le (D : DirectLdParams) :
    Real.exp (-((directLdAuxParameter D : ℝ) /
        (640000 * ((D.m : ℝ) ^ (2 : ℕ))))) ≤
      Real.rpow 2
        (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) := by
  calc
    Real.exp (-((directLdAuxParameter D : ℝ) /
        (640000 * ((D.m : ℝ) ^ (2 : ℕ))))) ≤
        Real.exp (-((directLdAuxParameter D : ℝ) /
          (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) := by
      apply Real.exp_le_exp.mpr
      rw [direct_ld_aux_parameter_linear_triangle_exp_arg,
        directLdAuxParameter_exp_arg]
      have hmd : 0 ≤ (D.m : ℝ) * (D.d : ℝ) := by positivity
      nlinarith
    _ ≤ Real.rpow 2
        (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) := by
      apply directLd_exponential_term_le D
      · unfold quantitativeLowDegreePower
        norm_num
      · unfold quantitativeLowDegreePower
        norm_num

/-- The incoming coordinate-test error contributes at most twice its
`1/8192` power. -/
theorem direct_ld_test_term_quantitative_le {ε : ℝ} (hε : 0 ≤ ε) :
    Real.rpow (3 * ε) quantitativeLowDegreePower ≤
      2 * Real.rpow ε quantitativeLowDegreePower := by
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by norm_num) hε]
  exact mul_le_mul_of_nonneg_right
    three_rpow_quantitative_low_degree_power_le_two
    (Real.rpow_nonneg hε _)

/-- The direct quantitative envelope is nonnegative. -/
theorem direct_quantitative_envelope_nonneg
    (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ directQuantitativeEnvelope D ε := by
  unfold directQuantitativeEnvelope
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg hε _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (by norm_num) _)

/-- The native direct low-degree error is nonnegative on nonnegative inputs. -/
theorem direct_native_error_nonneg
    (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ directNativeError D ε := by
  unfold directNativeError
  apply le_min zero_le_one
  have hinner : 0 ≤
      Real.rpow (3 * ε) quantitativeLowDegreePower +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower +
        Real.exp (-(4 * (D.m : ℝ) * (D.d : ℝ))) := by
    exact add_nonneg
      (add_nonneg
        (Real.rpow_nonneg (mul_nonneg (by norm_num) hε) _)
        (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _))
      (Real.exp_nonneg _)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hinner

/-- The square-root presentation used by the rounding theorem equals the
separated-power expression `nativeRoundingError`. -/
theorem native_rounding_error_eq
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
        2 * Real.sqrt (2 * delta) = nativeRoundingError delta := by
  have hrootQuarter : Real.sqrt (Real.rpow delta (1 / 4 : ℝ)) =
      Real.rpow delta (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (Real.rpow delta (1 / 4 : ℝ)) (1 / 2 : ℝ) =
          Real.rpow delta ((1 / 4 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hdelta _ _).symm
      _ = _ := by norm_num
  have hroot : Real.sqrt delta = Real.rpow delta (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow delta
  unfold nativeRoundingError
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 220), hrootQuarter,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hroot]
  ring

/-- The separated-power rounding error is nonnegative. -/
theorem native_rounding_error_nonneg {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ nativeRoundingError delta := by
  unfold nativeRoundingError
  exact add_nonneg
    (add_nonneg hdelta
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hdelta _)))
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hdelta _))

/-- The separated-power rounding error is monotone on nonnegative inputs. -/
theorem native_rounding_error_mono {delta delta' : ℝ}
    (hdelta : 0 ≤ delta) (h : delta ≤ delta') :
    nativeRoundingError delta ≤ nativeRoundingError delta' := by
  have h18 := Real.rpow_le_rpow hdelta h (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have h12 := Real.rpow_le_rpow hdelta h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold nativeRoundingError
  exact add_le_add
    (add_le_add h (mul_le_mul_of_nonneg_left h18 (Real.sqrt_nonneg _)))
    (mul_le_mul_of_nonneg_left h12
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- The ordered polynomial error is nonnegative when both inputs are. -/
theorem native_ordered_polynomial_error_nonneg
    {delta deltaQ : ℝ} (hdelta : 0 ≤ delta) (hdeltaQ : 0 ≤ deltaQ) :
    0 ≤ nativeOrderedPolynomialError delta deltaQ := by
  unfold nativeOrderedPolynomialError
  exact add_nonneg
    (mul_nonneg (by norm_num) (native_rounding_error_nonneg hdelta))
    (mul_nonneg (by norm_num) hdeltaQ)

/-- The uncapped global-pair error is nonnegative when both inputs are. -/
theorem native_global_pair_raw_error_nonneg
    (P : AdmissibleParams) {delta deltaQ : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaQ : 0 ≤ deltaQ) :
    0 ≤ nativeGlobalPairRawError P delta deltaQ := by
  unfold nativeGlobalPairRawError
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num) (native_rounding_error_nonneg hdelta))
      (mul_nonneg (by norm_num) hdeltaQ))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The capped global-pair error is nonnegative when both inputs are. -/
theorem native_global_pair_error_nonneg
    (P : AdmissibleParams) {delta deltaQ : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaQ : 0 ≤ deltaQ) :
    0 ≤ nativeGlobalPairError P delta deltaQ := by
  unfold nativeGlobalPairError
  exact le_min zero_le_one
    (native_global_pair_raw_error_nonneg P hdelta hdeltaQ)

/-- At the direct-game auxiliary sample count, the native error equals the capped
complete-measurement linear-triangle error. -/
theorem main_formal_linear_triangle_error_eq_direct_native_error
    (D : DirectLdParams) (ε : ℝ) :
    Test.mainFormalLinearTriangleError D.toLDTParameters
        (directLdAuxParameter D) (3 * ε) = directNativeError D ε := by
  have hmpos : (0 : ℝ) < (D.m : ℝ) := by
    exact_mod_cast D.toLDTParameters.hm
  have hmPower : Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
      Real.rpow (D.m : ℝ) (1 / 2 : ℝ) =
      Real.rpow (D.m : ℝ) (5 / 4 : ℝ) := by
    calc
      _ = Real.rpow (D.m : ℝ) ((3 / 4 : ℝ) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hmpos _ _).symm
      _ = _ := by norm_num
  have hprefactor :
      10000 *
          (40 * Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
            Real.rpow (D.d : ℝ) (1 / 4 : ℝ)) *
          Real.rpow (D.m : ℝ) (1 / 2 : ℝ) =
        400000 * Real.rpow (D.m : ℝ) (5 / 4 : ℝ) *
          Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by
    calc
      _ = 400000 *
          (Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
            Real.rpow (D.m : ℝ) (1 / 2 : ℝ)) *
          Real.rpow (D.d : ℝ) (1 / 4 : ℝ) := by ring
      _ = _ := by rw [hmPower]
  unfold Test.mainFormalLinearTriangleError Test.mainFormalLinearTriangleRawError
    Test.stepEnvelope directNativeError
  rw [direct_ld_aux_parameter_quarter_eq,
    direct_ld_aux_parameter_linear_triangle_exp_arg]
  unfold quantitativeLowDegreePower
  change min 1 (10000 *
      (40 * Real.rpow (D.m : ℝ) (3 / 4 : ℝ) *
        Real.rpow (D.d : ℝ) (1 / 4 : ℝ)) *
      Real.rpow (D.m : ℝ) (1 / 2 : ℝ) * _) = _
  rw [hprefactor]

/-- Before applying the unit cap, the native linear-triangle LDT error is
bounded by a quadratic parameter factor times the direct envelope. -/
theorem direct_ld_linear_triangle_raw_error_le
    (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    Test.mainFormalLinearTriangleRawError D.toLDTParameters
        (directLdAuxParameter D) (3 * ε) ≤
      1000000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) *
        directQuantitativeEnvelope D ε := by
  have hm : (1 : ℝ) ≤ (D.m : ℝ) := by exact_mod_cast D.hm
  have hd : (1 : ℝ) ≤ (D.d : ℝ) := by exact_mod_cast D.hd
  have hmRoot : Real.rpow (D.m : ℝ) (1 / 2 : ℝ) ≤ (D.m : ℝ) := by
    calc
      Real.rpow (D.m : ℝ) (1 / 2 : ℝ) ≤ Real.rpow (D.m : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
      _ = (D.m : ℝ) := Real.rpow_one _
  have hdRoot : Real.rpow (D.d : ℝ) quantitativeLowDegreePower ≤ (D.d : ℝ) := by
    calc
      Real.rpow (D.d : ℝ) quantitativeLowDegreePower ≤ Real.rpow (D.d : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hd (by
          unfold quantitativeLowDegreePower
          norm_num)
      _ = (D.d : ℝ) := Real.rpow_one _
  have htest := direct_ld_test_term_quantitative_le hε
  have hfield := direct_ld_field_term_quantitative_eq D
  have hexp := direct_ld_exponential_term_quantitative_le D
  have hx : 0 ≤ Real.rpow ε quantitativeLowDegreePower := Real.rpow_nonneg hε _
  have hy : 0 ≤ Real.rpow (D.q : ℝ) (-quantitativeLowDegreePower) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz : 0 ≤ Real.rpow 2
      (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsource : 0 ≤
      Real.rpow (3 * ε) quantitativeLowDegreePower +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower +
        Real.exp (-((directLdAuxParameter D : ℝ) /
          (640000 * ((D.m : ℝ) ^ (2 : ℕ))))) := by
    exact add_nonneg
      (add_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hε) _)
        (Real.rpow_nonneg (by positivity) _))
      (Real.exp_nonneg _)
  have hprefactor :
      10000 * Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) *
          Real.rpow (D.m : ℝ) (1 / 2 : ℝ) ≤
        400000 * (D.m : ℝ) ^ (2 : ℕ) * (D.d : ℝ) := by
    calc
      _ ≤ 10000 * (40 * (D.m : ℝ) * (D.d : ℝ)) *
          Real.rpow (D.m : ℝ) (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (direct_ld_aux_parameter_quarter_le D) (by norm_num))
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ 10000 * (40 * (D.m : ℝ) * (D.d : ℝ)) * (D.m : ℝ) := by
            exact mul_le_mul_of_nonneg_left hmRoot (by positivity)
      _ = _ := by ring
  have hinner :
      Real.rpow (3 * ε) quantitativeLowDegreePower +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower +
          Real.exp (-((directLdAuxParameter D : ℝ) /
            (640000 * ((D.m : ℝ) ^ (2 : ℕ))))) ≤
        2 * (D.d : ℝ) * directQuantitativeEnvelope D ε := by
    rw [hfield]
    have hfieldTerm := mul_le_mul_of_nonneg_right hdRoot hy
    have hdSub : 0 ≤ (D.d : ℝ) - 1 := sub_nonneg.mpr hd
    have hdx : 0 ≤ ((D.d : ℝ) - 1) *
        Real.rpow ε quantitativeLowDegreePower := mul_nonneg hdSub hx
    have hdNonneg : 0 ≤ (D.d : ℝ) := le_trans zero_le_one hd
    have hdy : 0 ≤ (D.d : ℝ) *
        Real.rpow (D.q : ℝ) (-quantitativeLowDegreePower) :=
      mul_nonneg hdNonneg hy
    have htwoD : 0 ≤ 2 * (D.d : ℝ) - 1 := by linarith
    have hdz : 0 ≤ (2 * (D.d : ℝ) - 1) *
        Real.rpow 2
          (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) :=
      mul_nonneg htwoD hz
    unfold directQuantitativeEnvelope
    nlinarith
  rw [Test.mainFormalLinearTriangleRawError, Test.stepEnvelope]
  change
    10000 * Real.rpow (directLdAuxParameter D : ℝ) (1 / 4 : ℝ) *
        Real.rpow (D.m : ℝ) (1 / 2 : ℝ) * _ ≤ _
  calc
    _ ≤ (400000 * (D.m : ℝ) ^ (2 : ℕ) * (D.d : ℝ)) *
        (Real.rpow (3 * ε) quantitativeLowDegreePower +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) quantitativeLowDegreePower +
          Real.exp (-((directLdAuxParameter D : ℝ) /
            (640000 * ((D.m : ℝ) ^ (2 : ℕ)))))) :=
      mul_le_mul_of_nonneg_right hprefactor hsource
    _ ≤ (400000 * (D.m : ℝ) ^ (2 : ℕ) * (D.d : ℝ)) *
        (2 * (D.d : ℝ) * directQuantitativeEnvelope D ε) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 800000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) *
        directQuantitativeEnvelope D ε := by push_cast; ring
    _ ≤ 1000000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) *
        directQuantitativeEnvelope D ε := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
      · exact direct_quantitative_envelope_nonneg D hε

/-- Weakening: `directNativeError` implies the coefficient-`30` common error
form, because paper `lem:ld-soundness` prints one `deltaLd` bound for all three
consistency conclusions. -/
theorem main_formal_linear_triangle_error_le_delta_ld_quantitative
    (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) (hk : D.k = 1) :
    Test.mainFormalLinearTriangleError D.toLDTParameters
        (directLdAuxParameter D) (3 * ε) ≤
      deltaLd 30 quantitativeLowDegreePower ε D.q D.m D.d D.k := by
  have henv := direct_quantitative_envelope_nonneg D hε
  have hraw := direct_ld_linear_triangle_raw_error_le D hε
  have hdelta :
      deltaLd 30 quantitativeLowDegreePower ε D.q D.m D.d D.k =
        30 * Real.rpow (((D.m * D.d : ℕ) : ℝ)) 30 *
          directQuantitativeEnvelope D ε := by
    unfold deltaLd directQuantitativeEnvelope
    rw [hk]
    push_cast
    ring_nf
  rw [hdelta]
  by_cases hone : D.m * D.d = 1
  · have htail : (1 / 2 : ℝ) ≤ Real.rpow 2
        (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) := by
      rw [hone]
      norm_num only [Nat.cast_one, mul_one]
      calc
        (1 / 2 : ℝ) = Real.rpow 2 (-1) := by
          calc
            (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
            _ = Real.rpow 2 (-1) := (Real.rpow_neg_one 2).symm
        _ ≤ Real.rpow 2 (-quantitativeLowDegreePower) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          unfold quantitativeLowDegreePower
          norm_num
    have honeEnv : 1 ≤ 30 * directQuantitativeEnvelope D ε := by
      have htailEnv : Real.rpow 2
          (-(quantitativeLowDegreePower * ((D.m * D.d : ℕ) : ℝ))) ≤
          directQuantitativeEnvelope D ε := by
        unfold directQuantitativeEnvelope
        have he := Real.rpow_nonneg hε quantitativeLowDegreePower
        have hq := Real.rpow_nonneg (Nat.cast_nonneg D.q)
          (-quantitativeLowDegreePower)
        exact le_add_of_nonneg_left (add_nonneg he hq)
      linarith
    rw [hone]
    norm_num only [Nat.cast_one]
    simp only [Real.rpow_eq_pow, Real.one_rpow, mul_one]
    exact (min_le_left _ _).trans honeEnv
  · have hmdNat : 2 ≤ D.m * D.d := by
      have hpos : 0 < D.m * D.d := Nat.mul_pos D.hm D.hd
      omega
    have hmd : (2 : ℝ) ≤ ((D.m * D.d : ℕ) : ℝ) := by exact_mod_cast hmdNat
    have hpow28 : (2 : ℝ) ^ (28 : ℕ) ≤
        (((D.m * D.d : ℕ) : ℝ) ^ (28 : ℕ)) :=
      pow_le_pow_left₀ (by norm_num) hmd 28
    have hcoefficient :
        1000000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) ≤
          30 * Real.rpow (((D.m * D.d : ℕ) : ℝ)) 30 := by
      rw [show Real.rpow (((D.m * D.d : ℕ) : ℝ)) 30 =
          (((D.m * D.d : ℕ) : ℝ) ^ (30 : ℕ)) by
        exact Real.rpow_natCast (((D.m * D.d : ℕ) : ℝ)) 30]
      calc
        1000000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) ≤
            (30 * (2 : ℝ) ^ (28 : ℕ)) *
              (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) := by
          gcongr
          norm_num
        _ ≤ (30 * (((D.m * D.d : ℕ) : ℝ) ^ (28 : ℕ))) *
              (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) := by gcongr
        _ = 30 * (((D.m * D.d : ℕ) : ℝ) ^ (30 : ℕ)) := by ring
    calc
      Test.mainFormalLinearTriangleError D.toLDTParameters
          (directLdAuxParameter D) (3 * ε) ≤
          Test.mainFormalLinearTriangleRawError D.toLDTParameters
            (directLdAuxParameter D) (3 * ε) := min_le_right _ _
      _ ≤ 1000000 * (((D.m * D.d : ℕ) : ℝ) ^ (2 : ℕ)) *
          directQuantitativeEnvelope D ε := hraw
      _ ≤ 30 * Real.rpow (((D.m * D.d : ℕ) : ℝ)) 30 *
          directQuantitativeEnvelope D ε :=
        mul_le_mul_of_nonneg_right hcoefficient henv

/-- The explicit native direct error is bounded by the paper-form
coefficient-`30` error at simultaneity parameter one. -/
theorem direct_native_error_le_delta_ld_quantitative
    (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) (hk : D.k = 1) :
    directNativeError D ε ≤
      deltaLd 30 quantitativeLowDegreePower ε D.q D.m D.d D.k := by
  rw [← main_formal_linear_triangle_error_eq_direct_native_error]
  exact main_formal_linear_triangle_error_le_delta_ld_quantitative D hε hk

end

end MIPStarRE.QPBT
