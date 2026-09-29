import MIPStarRE.LDT.Test.MainTheorem.LinearTriangle.MainFormal
import MIPStarRE.QPBT.Combining.ActualErrorBounds
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error
import MIPStarRE.QPBT.Combining.ExplicitScalarBounds

/-!
# Quantitative scalar bounds for the QPBT combining argument

This module records the numerical estimates used to import the
complete-measurement linear-triangle improvement of the low individual degree
test into the QPBT combining construction.  It also exposes the uncapped
small-regime direct-game passing estimate needed before projective rounding.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* `references/ldt-paper/test_definition.tex:180-202`
-/

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

/-- At simultaneity parameter one, the capped native LDT error is absorbed by
the coefficient-`30` error function used by quantitative direct soundness. -/
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

/-! ## Fixed baseline coefficient certificates -/

/-- The fixed combined-point coefficient is below `10^15`. -/
theorem pauli_baseline_point_constant_le :
    pauliBaselinePointConstant ≤ (1000000000000000 : ℝ) := by
  have hsqrt : Real.sqrt 344 ≤ (19 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  unfold pauliBaselinePointConstant pauliBaselineTwistedConstant
    pauliBaselineCommutatorConstant
  nlinarith

/-- The fixed combined-line coefficient is below `10^5`. -/
theorem pauli_baseline_line_constant_le :
    pauliBaselineLineConstant ≤ (100000 : ℝ) := by
  have hbase : 0 ≤ 16 * pauliBaselinePointConstant + 8320 := by
    nlinarith [one_le_pauli_baseline_point_constant]
  have hbaseBound : 16 * pauliBaselinePointConstant + 8320 ≤ (128 : ℝ) ^ (8 : ℕ) := by
    nlinarith [pauli_baseline_point_constant_le]
  have hroot : Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) ≤
      128 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_le_iff_of_pos hbase (by norm_num) (by norm_num)]
    exact hbaseBound.trans_eq (Real.rpow_natCast (128 : ℝ) 8).symm
  unfold pauliBaselineLineConstant
  nlinarith

/-- The fixed extended-line coefficient is below `10^9`. -/
theorem pauli_baseline_extended_line_constant_le :
    pauliBaselineExtendedLineConstant ≤ (1000000000 : ℝ) := by
  have hpoint0 : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hline0 : 0 ≤ pauliBaselineLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_line_constant
  have hpointSqrt : Real.sqrt pauliBaselinePointConstant ≤ (40000000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pauli_baseline_point_constant_le]
  have hlineRoot : Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) ≤ 32 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_le_iff_of_pos hline0 (by norm_num) (by norm_num)]
    exact pauli_baseline_line_constant_le.trans (by norm_num)
  have hpointRoot : Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) ≤ 10000 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_le_iff_of_pos hpoint0 (by norm_num) (by norm_num)]
    exact pauli_baseline_point_constant_le.trans (by norm_num)
  unfold pauliBaselineExtendedLineConstant
  nlinarith

/-- The fixed coefficient in the direct passing estimate is below `10^8`. -/
theorem pauli_baseline_passing_constant_le :
    pauliBaselinePassingConstant ≤ (100000000 : ℝ) := by
  have hsum : 0 ≤ pauliBaselinePointConstant + pauliBaselineExtendedLineConstant := by
    nlinarith [one_le_pauli_baseline_point_constant,
      one_le_pauli_baseline_extended_line_constant]
  have hroot : Real.sqrt
      (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) ≤
      (33000000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pauli_baseline_point_constant_le,
      pauli_baseline_extended_line_constant_le]
  unfold pauliBaselinePassingConstant
  nlinarith

/-! ## The uncapped direct passing estimate -/

/-- In the unit regime, the actual direct-game passing envelope is bounded by
the fixed passing error before any unit cap is applied.  This is the
small-regime calculation inside `pauli_baseline_direct_passing_bound`, exposed
for the quantitative global-pair construction. -/
theorem pauli_baseline_direct_passing_bound_uncapped
    (error ratio dimension : ℝ) (herror : 0 ≤ error) (herrorOne : error ≤ 1)
    (hratio : 0 ≤ ratio) (hratioOne : ratio ≤ 1) (hdimension : 1 ≤ dimension) :
    directPassingErrorEnvelope
        (pauliBaselinePointError error +
          dimension * pauliBaselineExtendedLineError error ratio) ratio ≤
      dimension * pauliBaselinePassingError error ratio := by
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have hpointConstant : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hextendedConstant : 0 ≤ pauliBaselineExtendedLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_extended_line_constant
  have hsumConstant : 0 ≤
      pauliBaselinePointConstant + pauliBaselineExtendedLineConstant := by
    linarith
  have he : 0 ≤ error ^ (1 / 512 : ℝ) := Real.rpow_nonneg herror _
  have hy : 0 ≤ ratio ^ (1 / 32 : ℝ) := Real.rpow_nonneg hratio _
  have hpointBound : pauliBaselinePointError error ≤
      pauliBaselinePointConstant * Real.rpow error (1 / 256 : ℝ) := by
    unfold pauliBaselinePointError
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne (by norm_num) (by norm_num))
      hpointConstant
  have hlineBound : pauliBaselineExtendedLineError error ratio ≤
      pauliBaselineExtendedLineConstant *
        (Real.rpow error (1 / 256 : ℝ) +
          Real.rpow ratio (1 / 16 : ℝ)) := le_rfl
  have herrorFull : 0 ≤ Real.rpow error (1 / 256 : ℝ) :=
    Real.rpow_nonneg herror _
  have hratioFull : 0 ≤ Real.rpow ratio (1 / 16 : ℝ) :=
    Real.rpow_nonneg hratio _
  have hsum : pauliBaselinePointError error +
      dimension * pauliBaselineExtendedLineError error ratio ≤
      dimension *
        (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) *
          (Real.rpow error (1 / 256 : ℝ) +
            Real.rpow ratio (1 / 16 : ℝ)) := by
    have hpointDim : pauliBaselinePointConstant *
        Real.rpow error (1 / 256 : ℝ) ≤
        dimension * (pauliBaselinePointConstant *
          Real.rpow error (1 / 256 : ℝ)) :=
      le_mul_of_one_le_left (mul_nonneg hpointConstant herrorFull) hdimension
    have hlineDim := mul_le_mul_of_nonneg_left hlineBound hdimensionNonneg
    calc
      _ ≤ pauliBaselinePointConstant * Real.rpow error (1 / 256 : ℝ) +
          dimension * (pauliBaselineExtendedLineConstant *
            (Real.rpow error (1 / 256 : ℝ) +
              Real.rpow ratio (1 / 16 : ℝ))) := add_le_add hpointBound hlineDim
      _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hdimensionNonneg hpointConstant) hratioFull]
  have heSq : (error ^ (1 / 512 : ℝ)) ^ (2 : ℕ) =
      error ^ (1 / 256 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul herror]
    congr 1
    ring
  have hySq : (ratio ^ (1 / 32 : ℝ)) ^ (2 : ℕ) =
      ratio ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
    congr 1
    ring
  have hrootSum : Real.sqrt
      (error ^ (1 / 256 : ℝ) + ratio ^ (1 / 16 : ℝ)) ≤
      error ^ (1 / 512 : ℝ) + ratio ^ (1 / 32 : ℝ) := by
    apply (Real.sqrt_le_left (add_nonneg he hy)).mpr
    nlinarith [mul_nonneg he hy]
  have hrootDim : Real.sqrt dimension ≤ dimension := by
    apply (Real.sqrt_le_left hdimensionNonneg).mpr
    nlinarith
  have hroot : Real.sqrt
      (pauliBaselinePointError error +
        dimension * pauliBaselineExtendedLineError error ratio) ≤
      dimension * Real.sqrt
        (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) *
        (Real.rpow error (1 / 512 : ℝ) +
          Real.rpow ratio (1 / 32 : ℝ)) := by
    calc
      _ ≤ Real.sqrt (dimension *
          (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) *
            (Real.rpow error (1 / 256 : ℝ) +
              Real.rpow ratio (1 / 16 : ℝ))) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt dimension *
          Real.sqrt (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) *
          Real.sqrt (Real.rpow error (1 / 256 : ℝ) +
            Real.rpow ratio (1 / 16 : ℝ)) := by
        rw [Real.sqrt_mul (mul_nonneg hdimensionNonneg hsumConstant),
          Real.sqrt_mul hdimensionNonneg]
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hrootDim (Real.sqrt_nonneg _)) hrootSum
        (Real.sqrt_nonneg _) (mul_nonneg hdimensionNonneg (Real.sqrt_nonneg _))
  have hratioSmall : ratio ≤ Real.rpow ratio (1 / 32 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne
      (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) ≤ 1)
  have hratioDim : ratio ≤ dimension * Real.rpow ratio (1 / 32 : ℝ) :=
    hratioSmall.trans (le_mul_of_one_le_left hy hdimension)
  unfold directPassingErrorEnvelope pauliBaselinePassingError
    pauliBaselinePassingConstant
  have hgap : 0 ≤ dimension *
      (4 * Real.rpow error (1 / 512 : ℝ) + Real.rpow ratio (1 / 32 : ℝ)) :=
    mul_nonneg hdimensionNonneg
      (add_nonneg (mul_nonneg (by norm_num) he) hy)
  calc
    3 * (Real.sqrt (pauliBaselinePointError error +
          dimension * pauliBaselineExtendedLineError error ratio) + ratio) =
        3 * Real.sqrt (pauliBaselinePointError error +
          dimension * pauliBaselineExtendedLineError error ratio) + 3 * ratio := by ring
    _ ≤ 3 * (dimension * Real.sqrt
          (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant) *
            (Real.rpow error (1 / 512 : ℝ) +
              Real.rpow ratio (1 / 32 : ℝ))) +
          3 * (dimension * Real.rpow ratio (1 / 32 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hroot (by norm_num))
        (mul_le_mul_of_nonneg_left hratioDim (by norm_num))
    _ ≤ dimension * ((4 + 3 * Real.sqrt
          (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant)) *
            (Real.rpow error (1 / 512 : ℝ) +
              Real.rpow ratio (1 / 32 : ℝ))) := by
      apply le_trans (le_add_of_nonneg_right hgap)
      ring_nf
      exact le_rfl

/-- The actual direct-game passing envelope has the explicit uncapped bound
`10^8 * m * (e^(1/512) + r^(1/32))` in the unit regime. -/
theorem direct_passing_error_envelope_quantitative_bound
    (P : AdmissibleParams) (e r : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    directPassingErrorEnvelope
        (pauliBaselinePointError e +
          (P.m : ℝ) * pauliBaselineExtendedLineError e r) r ≤
      100000000 * (P.m : ℝ) *
        (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)) := by
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hsum : 0 ≤ Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ) :=
    add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)
  calc
    _ ≤ (P.m : ℝ) * pauliBaselinePassingError e r :=
      pauli_baseline_direct_passing_bound_uncapped e r (P.m : ℝ)
        he he1 hr hr1 hm
    _ = (P.m : ℝ) * pauliBaselinePassingConstant *
        (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)) := by
      unfold pauliBaselinePassingError
      ring
    _ ≤ 100000000 * (P.m : ℝ) *
        (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hsum
      have hcoefficient := mul_le_mul_of_nonneg_left
        pauli_baseline_passing_constant_le (show 0 ≤ (P.m : ℝ) by positivity)
      nlinarith

/-! ## Absorption before projective rounding -/

set_option maxHeartbeats 800000 in
-- The nested power monotonicity and coefficient normalization exceed the default budget.
/-- The coefficient-`30` low-degree error at the actual direct passing
parameter is bounded by `10^30 n^32` times the pre-rounding envelope. -/
theorem quantitative_low_degree_error_bound
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr1 : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1) :
    deltaLd 30 quantitativeLowDegreePower
        (directPassingErrorEnvelope
          (pauliBaselinePointError e + (P.m : ℝ) *
            pauliBaselineExtendedLineError e
              (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
          (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
        P.q (2 * P.m + 2) P.d 1 ≤
      1000000000000000000000000000000 *
        (((P.m * P.d : ℕ) : ℝ) ^ (32 : ℕ)) *
        quantitativePreRoundingEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let M : ℝ := (((2 * P.m + 2) * P.d : ℕ) : ℝ)
  let r : ℝ := n / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError e + (P.m : ℝ) *
      pauliBaselineExtendedLineError e r) r
  let E := quantitativePreRoundingEnvelope P e
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hd : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast P.hd
  have hn : (1 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn0 : 0 ≤ n := by linarith
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow power 2 (by norm_num)
  have hq0 : 0 ≤ (P.q : ℝ) := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrOne : r ≤ 1 := by simpa only [r, n] using hr1
  have hE : 0 ≤ E := by
    dsimp [E, quantitativePreRoundingEnvelope]
    positivity
  have heE : Real.rpow e quantitativePreRoundingPower ≤ E := by
    dsimp [E, quantitativePreRoundingEnvelope]
    have hqTerm := Real.rpow_nonneg hq0 (-quantitativePreRoundingPower)
    have htail := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(quantitativePreRoundingPower * n))
    linarith
  have hqE : Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) ≤ E := by
    dsimp [E, quantitativePreRoundingEnvelope]
    have heTerm := Real.rpow_nonneg he quantitativePreRoundingPower
    have htail := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(quantitativePreRoundingPower * n))
    linarith
  have htailE : Real.rpow 2
      (-(quantitativePreRoundingPower * n)) ≤ E := by
    dsimp [E, quantitativePreRoundingEnvelope]
    have heTerm := Real.rpow_nonneg he quantitativePreRoundingPower
    have hqTerm := Real.rpow_nonneg hq0 (-quantitativePreRoundingPower)
    linarith
  have hmN : (P.m : ℝ) ≤ n := by dsimp [n]; push_cast; nlinarith
  have hM : M ≤ 4 * n := by
    dsimp [M, n]
    push_cast
    nlinarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hpassing : passing ≤ 100000000 * (P.m : ℝ) *
      (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)) := by
    dsimp [passing]
    exact direct_passing_error_envelope_quantitative_bound P e r he he1 hr hrOne
  have hpassing0 : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have htau0 : 0 ≤ quantitativeLowDegreePower := by
    unfold quantitativeLowDegreePower
    norm_num
  have htau1 : quantitativeLowDegreePower ≤ 1 := by
    unfold quantitativeLowDegreePower
    norm_num
  have hu0 : 0 ≤ quantitativePreRoundingPower := by
    unfold quantitativePreRoundingPower
    norm_num
  have huTau : quantitativePreRoundingPower ≤ quantitativeLowDegreePower := by
    unfold quantitativePreRoundingPower quantitativeLowDegreePower
    norm_num
  have hconstant : Real.rpow (100000000 : ℝ) quantitativeLowDegreePower ≤
      100000000 := by
    calc
      _ ≤ Real.rpow (100000000 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) htau1
      _ = _ := Real.rpow_one _
  have hmPow : Real.rpow (P.m : ℝ) quantitativeLowDegreePower ≤ n := by
    calc
      _ ≤ Real.rpow (P.m : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hm htau1
      _ = (P.m : ℝ) := Real.rpow_one _
      _ ≤ n := hmN
  have hxPow : Real.rpow (Real.rpow e (1 / 512 : ℝ))
      quantitativeLowDegreePower = Real.rpow e quantitativePreRoundingPower := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul he]
    congr 1
    unfold quantitativeLowDegreePower quantitativePreRoundingPower
    norm_num
  have hrPowEq : Real.rpow r quantitativePreRoundingPower =
      Real.rpow n quantitativePreRoundingPower *
        Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) := by
    dsimp [r]
    rw [Real.div_rpow hn0 hq0, div_eq_mul_inv,
      ← Real.rpow_neg hq0]
  have hnPow : Real.rpow n quantitativePreRoundingPower ≤ n := by
    calc
      _ ≤ Real.rpow n 1 := Real.rpow_le_rpow_of_exponent_le hn (by
        unfold quantitativePreRoundingPower
        norm_num)
      _ = n := Real.rpow_one _
  have hrUPow : Real.rpow r quantitativePreRoundingPower ≤ n * E := by
    rw [hrPowEq]
    exact (mul_le_mul hnPow hqE (Real.rpow_nonneg hq0 _) hn0)
  have hratioExponent : quantitativePreRoundingPower ≤
      (1 / 32 : ℝ) * quantitativeLowDegreePower := by
    unfold quantitativePreRoundingPower quantitativeLowDegreePower
    norm_num
  have hyPow : Real.rpow (Real.rpow r (1 / 32 : ℝ))
      quantitativeLowDegreePower ≤ n * E := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hr]
    exact (Real.rpow_le_rpow_of_exponent_ge' hr hrOne hu0 hratioExponent).trans hrUPow
  have hsumPow : Real.rpow
      (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ))
      quantitativeLowDegreePower ≤ 2 * n * E := by
    have hsplit : Real.rpow
        (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ))
          quantitativeLowDegreePower ≤
        Real.rpow (Real.rpow e (1 / 512 : ℝ)) quantitativeLowDegreePower +
          Real.rpow (Real.rpow r (1 / 32 : ℝ)) quantitativeLowDegreePower :=
      Real.rpow_add_le_add_rpow
        (Real.rpow_nonneg he (1 / 512 : ℝ))
        (Real.rpow_nonneg hr (1 / 32 : ℝ)) htau0 htau1
    rw [hxPow] at hsplit
    have hfirst : Real.rpow e quantitativePreRoundingPower ≤ n * E :=
      heE.trans (le_mul_of_one_le_left hE hn)
    nlinarith
  have hpassingPow : Real.rpow passing quantitativeLowDegreePower ≤
      200000000 * n ^ (2 : ℕ) * E := by
    calc
      _ ≤ Real.rpow (100000000 * (P.m : ℝ) *
          (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)))
          quantitativeLowDegreePower :=
        Real.rpow_le_rpow hpassing0 hpassing htau0
      _ = Real.rpow (100000000 : ℝ) quantitativeLowDegreePower *
          Real.rpow (P.m : ℝ) quantitativeLowDegreePower *
          Real.rpow (Real.rpow e (1 / 512 : ℝ) +
            Real.rpow r (1 / 32 : ℝ)) quantitativeLowDegreePower := by
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow
            (mul_nonneg (by norm_num) (show 0 ≤ (P.m : ℝ) by positivity))
            (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)),
          Real.mul_rpow (by norm_num) (show 0 ≤ (P.m : ℝ) by positivity)]
      _ ≤ 100000000 * n * (2 * n * E) := by
        have hmPow0 : 0 ≤ Real.rpow (P.m : ℝ) quantitativeLowDegreePower :=
          Real.rpow_nonneg (by positivity) _
        have hsumPow0 : 0 ≤ Real.rpow
            (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ))
              quantitativeLowDegreePower :=
          Real.rpow_nonneg
            (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)) _
        have hfirst := mul_le_mul hconstant hmPow hmPow0 (by norm_num)
        exact mul_le_mul hfirst hsumPow hsumPow0 (by positivity)
      _ = 200000000 * n ^ (2 : ℕ) * E := by ring
  have hfield : Real.rpow (P.q : ℝ) (-quantitativeLowDegreePower) ≤ E := by
    exact (Real.rpow_le_rpow_of_exponent_le hq
      (neg_le_neg huTau)).trans hqE
  have htail : Real.rpow 2 (-(quantitativeLowDegreePower * M)) ≤ E := by
    have hsize : n ≤ M := by
      dsimp [n, M]
      push_cast
      nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans htailE
    exact neg_le_neg ((mul_le_mul_of_nonneg_right huTau hn0).trans
      (mul_le_mul_of_nonneg_left hsize htau0))
  have hbracket : Real.rpow passing quantitativeLowDegreePower +
      Real.rpow (P.q : ℝ) (-quantitativeLowDegreePower) +
      Real.rpow 2 (-(quantitativeLowDegreePower * M)) ≤
      200000002 * n ^ (2 : ℕ) * E := by
    have hnSq : 1 ≤ n ^ (2 : ℕ) := by nlinarith [sq_nonneg (n - 1)]
    have hrest : Real.rpow (P.q : ℝ) (-quantitativeLowDegreePower) +
        Real.rpow 2 (-(quantitativeLowDegreePower * M)) ≤
        2 * n ^ (2 : ℕ) * E := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnSq) hE]
    nlinarith
  have hprefactor : 30 * Real.rpow M 30 ≤
      30 * (4 : ℝ) ^ (30 : ℕ) * n ^ (30 : ℕ) := by
    have hpow := Real.rpow_le_rpow hM0 hM (by norm_num : (0 : ℝ) ≤ (30 : ℝ))
    have hpowNat : Real.rpow M 30 ≤ (4 * n) ^ (30 : ℕ) :=
      hpow.trans_eq (Real.rpow_natCast (4 * n) 30)
    calc
      _ ≤ 30 * (4 * n) ^ (30 : ℕ) :=
        mul_le_mul_of_nonneg_left hpowNat (by norm_num)
      _ = _ := by ring
  have hdelta : deltaLd 30 quantitativeLowDegreePower passing
      P.q (2 * P.m + 2) P.d 1 =
      30 * Real.rpow M 30 *
        (Real.rpow passing quantitativeLowDegreePower +
          Real.rpow (P.q : ℝ) (-quantitativeLowDegreePower) +
          Real.rpow 2 (-(quantitativeLowDegreePower * M))) := by
    simp only [deltaLd, M, Nat.mul_one, Real.rpow_eq_pow,
      Nat.mul_comm P.d (2 * P.m + 2)]
  change deltaLd 30 quantitativeLowDegreePower passing
      P.q (2 * P.m + 2) P.d 1 ≤ _
  rw [hdelta]
  calc
    _ ≤ (30 * (4 : ℝ) ^ (30 : ℕ) * n ^ (30 : ℕ)) *
        (200000002 * n ^ (2 : ℕ) * E) :=
      mul_le_mul hprefactor hbracket
        (add_nonneg
          (add_nonneg (Real.rpow_nonneg hpassing0 _)
            (Real.rpow_nonneg hq0 _))
          (Real.rpow_nonneg (by norm_num) _))
        (by positivity)
    _ = (30 * (4 : ℝ) ^ (30 : ℕ) * 200000002) *
        n ^ (32 : ℕ) * E := by ring
    _ ≤ 1000000000000000000000000000000 * n ^ (32 : ℕ) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ n ^ (32 : ℕ))
      norm_num

/-! ## The eighth-root rounding step -/

/-- The pre-rounding envelope is nonnegative. -/
theorem quantitative_pre_rounding_envelope_nonneg
    (P : AdmissibleParams) {e : ℝ} (he : 0 ≤ e) :
    0 ≤ quantitativePreRoundingEnvelope P e := by
  unfold quantitativePreRoundingEnvelope
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg he _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (by norm_num) _)

/-- The square root of the fixed point error is controlled by the
pre-rounding envelope. -/
theorem quantitative_point_error_root_bound
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    Real.sqrt (pauliBaselinePointError e) ≤
      40000000 * quantitativePreRoundingEnvelope P e := by
  have hconstant0 : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hconstantRoot : Real.sqrt pauliBaselinePointConstant ≤ (40000000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pauli_baseline_point_constant_le]
  have hpower : Real.sqrt (Real.rpow e (1 / 8 : ℝ)) =
      Real.rpow e (1 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul he]
    congr 1
    norm_num
  have hroot : Real.sqrt (pauliBaselinePointError e) ≤
      40000000 * Real.rpow e (1 / 16 : ℝ) := by
    unfold pauliBaselinePointError
    rw [Real.sqrt_mul hconstant0, hpower]
    exact mul_le_mul_of_nonneg_right hconstantRoot (Real.rpow_nonneg he _)
  have hexponent : quantitativePreRoundingPower ≤ (1 / 16 : ℝ) := by
    unfold quantitativePreRoundingPower
    norm_num
  have hmono : Real.rpow e (1 / 16 : ℝ) ≤
      Real.rpow e quantitativePreRoundingPower :=
    Real.rpow_le_rpow_of_exponent_ge' he he1 (by
      unfold quantitativePreRoundingPower
      norm_num) hexponent
  have henvelope : Real.rpow e quantitativePreRoundingPower ≤
      quantitativePreRoundingEnvelope P e := by
    unfold quantitativePreRoundingEnvelope
    have hqTerm : 0 ≤ Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have htail : 0 ≤ Real.rpow 2
        (-(quantitativePreRoundingPower * ((P.m * P.d : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    exact (le_add_of_nonneg_right hqTerm).trans (le_add_of_nonneg_right htail)
  exact hroot.trans (mul_le_mul_of_nonneg_left (hmono.trans henvelope) (by norm_num))

/-- The ratio bound with the envelope at any nonnegative strategy error. -/
theorem quantitative_ratio_bound_of_nonneg
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤
      ((P.m * P.d : ℕ) : ℝ) * quantitativePreRoundingEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow power 2 (by norm_num)
  have hq0 : 0 ≤ (P.q : ℝ) := by linarith
  have hu1 : quantitativePreRoundingPower ≤ 1 := by
    unfold quantitativePreRoundingPower
    norm_num
  have hfield : (P.q : ℝ)⁻¹ ≤
      Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) := by
    simp only [Real.rpow_eq_pow]
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hu1)
  have hfieldEnvelope : Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) ≤
      quantitativePreRoundingEnvelope P e := by
    unfold quantitativePreRoundingEnvelope
    have heTerm := Real.rpow_nonneg he quantitativePreRoundingPower
    have ht := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(quantitativePreRoundingPower * n))
    change Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) ≤
      Real.rpow e quantitativePreRoundingPower +
        Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower) +
        Real.rpow 2 (-(quantitativePreRoundingPower * n))
    exact (le_add_of_nonneg_left heTerm).trans (le_add_of_nonneg_right ht)
  change n / (P.q : ℝ) ≤ n * quantitativePreRoundingEnvelope P e
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (hfield.trans hfieldEnvelope) hn0

/-- Three square roots of the pre-rounding envelope are bounded by the final
three-term envelope at exponent `1/33554432`. -/
theorem quantitative_pre_rounding_envelope_eighth_root_le
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    Real.sqrt (Real.sqrt (Real.sqrt (quantitativePreRoundingEnvelope P e))) ≤
      quantitativeGlobalPairEnvelope P e := by
  let x := Real.rpow e quantitativePreRoundingPower
  let y := Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower)
  let z := Real.rpow 2
    (-(quantitativePreRoundingPower * ((P.m * P.d : ℕ) : ℝ)))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hsum : quantitativePreRoundingEnvelope P e = x + y + z := rfl
  have hroot : Real.sqrt (Real.sqrt (Real.sqrt (x + y + z))) =
      Real.rpow (x + y + z) (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (add_nonneg (add_nonneg hx hy) hz),
      ← Real.rpow_mul (add_nonneg (add_nonneg hx hy) hz)]
    congr 1
    norm_num
  rw [hsum, hroot]
  have hsplit : Real.rpow (x + y + z) (1 / 8 : ℝ) ≤
      Real.rpow x (1 / 8 : ℝ) + Real.rpow y (1 / 8 : ℝ) +
        Real.rpow z (1 / 8 : ℝ) :=
    (Real.rpow_add_le_add_rpow (add_nonneg hx hy) hz
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans
      (add_le_add (Real.rpow_add_le_add_rpow hx hy
        (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)) le_rfl)
  have hxRoot : Real.rpow x (1 / 8 : ℝ) =
      Real.rpow e quantitativeGlobalPairPower := by
    dsimp [x]
    calc
      Real.rpow (Real.rpow e quantitativePreRoundingPower) (1 / 8 : ℝ) =
          Real.rpow e (quantitativePreRoundingPower * (1 / 8 : ℝ)) :=
        (Real.rpow_mul he _ _).symm
      _ = Real.rpow e quantitativeGlobalPairPower := by
        congr 1
        unfold quantitativePreRoundingPower quantitativeGlobalPairPower
        norm_num
  have hyRoot : Real.rpow y (1 / 8 : ℝ) =
      Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) := by
    dsimp [y]
    calc
      Real.rpow (Real.rpow (P.q : ℝ) (-quantitativePreRoundingPower))
          (1 / 8 : ℝ) =
          Real.rpow (P.q : ℝ)
            ((-quantitativePreRoundingPower) * (1 / 8 : ℝ)) :=
        (Real.rpow_mul (show 0 ≤ (P.q : ℝ) by positivity) _ _).symm
      _ = Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) := by
        congr 1
        unfold quantitativePreRoundingPower quantitativeGlobalPairPower
        norm_num
  have hzRoot : Real.rpow z (1 / 8 : ℝ) = Real.rpow 2
      (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ))) := by
    dsimp [z]
    calc
      Real.rpow (Real.rpow 2
          (-(quantitativePreRoundingPower * ((P.m * P.d : ℕ) : ℝ))))
          (1 / 8 : ℝ) = Real.rpow 2
          ((-(quantitativePreRoundingPower * ((P.m * P.d : ℕ) : ℝ))) *
            (1 / 8 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = Real.rpow 2
          (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ))) := by
        congr 1
        unfold quantitativePreRoundingPower quantitativeGlobalPairPower
        ring
  rw [hxRoot, hyRoot, hzRoot] at hsplit
  simpa only [quantitativeGlobalPairEnvelope] using hsplit

set_option maxHeartbeats 800000 in
-- The three successive square-root normalizations exceed the default budget.
/-- The unit cap of the exact error of the quantitative rounded pair is bounded
by `10^7 n^4` times the final three-term envelope.  The left-hand side is the
error appearing in `pair_witness_of_points_lines_quantitative`. -/
theorem quantitative_actual_rounded_global_pair_error_bound
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr1 : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1) :
    let delta := deltaLd 30 quantitativeLowDegreePower
      (directPassingErrorEnvelope
        (pauliBaselinePointError e + (P.m : ℝ) *
          pauliBaselineExtendedLineError e
            (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
        (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
      P.q (2 * P.m + 2) P.d 1
    let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
      2 * Real.sqrt (2 * delta)
    min 1 (8 * (4 * eta + 8 * pauliBaselinePointError e) +
      (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
      10000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e := by
  intro delta eta
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let r : ℝ := n / (P.q : ℝ)
  let E := quantitativePreRoundingEnvelope P e
  let F := quantitativeGlobalPairEnvelope P e
  let t := delta + Real.sqrt (pauliBaselinePointError e) + r
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hdNat : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast P.hd
  have hn : (1 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn0 : 0 ≤ n := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact quantitative_pre_rounding_envelope_nonneg P he
  have hF : 0 ≤ F := by
    dsimp [F, quantitativeGlobalPairEnvelope]
    positivity
  have hp : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  have hd : 0 ≤ delta := by
    dsimp [delta, deltaLd, directPassingErrorEnvelope]
    positivity
  have hdelta : delta ≤
      1000000000000000000000000000000 * n ^ (32 : ℕ) * E := by
    dsimp [delta, n, E]
    exact quantitative_low_degree_error_bound P e he he1 hr1
  have hpoint : Real.sqrt (pauliBaselinePointError e) ≤ 40000000 * E := by
    dsimp [E]
    exact quantitative_point_error_root_bound P e he he1
  have hratio : r ≤ n * E := by
    dsimp [r, n, E]
    exact quantitative_ratio_bound_of_nonneg P e he
  have hn32 : 1 ≤ n ^ (32 : ℕ) := by
    exact one_le_pow₀ hn
  have hn4 : 0 ≤ n ^ (4 : ℕ) := by positivity
  have hbase : 0 ≤ n ^ (32 : ℕ) * E := mul_nonneg (by positivity) hE
  have hpointLarge : Real.sqrt (pauliBaselinePointError e) ≤
      40000000 * (n ^ (32 : ℕ) * E) := by
    exact hpoint.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hE hn32) (by norm_num))
  have hnLe : n ≤ n ^ (32 : ℕ) := by
    simpa using pow_le_pow_right₀ hn (by norm_num : 1 ≤ 32)
  have hratioLarge : r ≤ n ^ (32 : ℕ) * E :=
    hratio.trans (mul_le_mul_of_nonneg_right hnLe hE)
  have ht : t ≤ 10000000000000000000000000000000 *
      (n ^ (32 : ℕ) * E) := by
    dsimp [t]
    nlinarith
  have hdt : delta ≤ t := by
    dsimp [t]
    linarith [Real.sqrt_nonneg (pauliBaselinePointError e)]
  have hpt : Real.sqrt (pauliBaselinePointError e) ≤ t := by
    dsimp [t]
    linarith
  have hrt : r ≤ t := by
    dsimp [t]
    linarith [Real.sqrt_nonneg (pauliBaselinePointError e)]
  have hratioCoefficient :
      (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤ 30 * r := by
    dsimp [r, n]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have hraw :
      8 * (4 * eta + 8 * pauliBaselinePointError e) +
          (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤
        32 * delta + 32 * Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
          64 * Real.sqrt (2 * delta) + 64 * pauliBaselinePointError e + 30 * r := by
    dsimp [eta]
    linarith
  have hround := actual_rounding_error_le_root hd hp hdt hpt hrt
  have hminT : min 1 t ≤
      10000000000000000000000000000000 * (n ^ (32 : ℕ) * E) :=
    (min_le_right 1 t).trans ht
  have hrootMon := Real.sqrt_le_sqrt
    (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hminT))
  have hCroot : Real.rpow (10000000000000000000000000000000 : ℝ)
      (1 / 8 : ℝ) ≤ 8000 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hnRoot : Real.rpow (n ^ (32 : ℕ)) (1 / 8 : ℝ) = n ^ (4 : ℕ) := by
    calc
      Real.rpow (n ^ (32 : ℕ)) (1 / 8 : ℝ) =
          Real.rpow (Real.rpow n (32 : ℝ)) (1 / 8 : ℝ) := by
        exact congrArg (fun x => Real.rpow x (1 / 8 : ℝ))
          (Real.rpow_natCast n 32).symm
      _ = Real.rpow n ((32 : ℝ) * (1 / 8 : ℝ)) :=
        (Real.rpow_mul hn0 _ _).symm
      _ = Real.rpow n (4 : ℝ) := by norm_num
      _ = n ^ (4 : ℕ) := Real.rpow_natCast n 4
  have hproductRoot : Real.sqrt (Real.sqrt (Real.sqrt
      (10000000000000000000000000000000 * (n ^ (32 : ℕ) * E)))) ≤
      8000 * n ^ (4 : ℕ) * F := by
    have hX : 0 ≤ 10000000000000000000000000000000 *
        (n ^ (32 : ℕ) * E) := mul_nonneg (by norm_num) hbase
    have hrootEq : Real.sqrt (Real.sqrt (Real.sqrt
        (10000000000000000000000000000000 * (n ^ (32 : ℕ) * E)))) =
        Real.rpow (10000000000000000000000000000000 *
          (n ^ (32 : ℕ) * E)) (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hX, ← Real.rpow_mul hX]
      congr 1
      norm_num
    rw [hrootEq]
    have hfactor : Real.rpow
        (10000000000000000000000000000000 * (n ^ (32 : ℕ) * E))
          (1 / 8 : ℝ) =
        Real.rpow (10000000000000000000000000000000 : ℝ) (1 / 8 : ℝ) *
          Real.rpow (n ^ (32 : ℕ)) (1 / 8 : ℝ) *
          Real.rpow E (1 / 8 : ℝ) := by
      calc
        _ = Real.rpow (10000000000000000000000000000000 : ℝ) (1 / 8 : ℝ) *
            Real.rpow (n ^ (32 : ℕ) * E) (1 / 8 : ℝ) :=
          Real.mul_rpow (by norm_num) hbase
        _ = _ := by
          simpa only [Real.rpow_eq_pow, mul_assoc] using congrArg
            (fun x => Real.rpow (10000000000000000000000000000000 : ℝ)
              (1 / 8 : ℝ) * x)
            (Real.mul_rpow (show 0 ≤ n ^ (32 : ℕ) by positivity) hE)
    rw [hfactor, hnRoot]
    have hERoot : Real.rpow E (1 / 8 : ℝ) ≤ F := by
      have h := quantitative_pre_rounding_envelope_eighth_root_le P e he
      have hEq : Real.sqrt (Real.sqrt (Real.sqrt E)) =
          Real.rpow E (1 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_mul hE, ← Real.rpow_mul hE]
        congr 1
        norm_num
      dsimp [E, F] at h ⊢
      rw [hEq] at h
      exact h
    have hleft := mul_le_mul hCroot (le_refl (n ^ (4 : ℕ))) hn4 (by norm_num)
    exact mul_le_mul hleft hERoot (Real.rpow_nonneg hE _) (by positivity)
  have hrootBound : Real.sqrt (Real.sqrt (Real.sqrt (min 1 t))) ≤
      8000 * n ^ (4 : ℕ) * F := hrootMon.trans hproductRoot
  calc
    min 1 (8 * (4 * eta + 8 * pauliBaselinePointError e) +
        (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
        min 1 (32 * delta + 32 * Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
          64 * Real.sqrt (2 * delta) + 64 * pauliBaselinePointError e + 30 * r) :=
      min_le_min_left 1 hraw
    _ ≤ 1024 * Real.sqrt (Real.sqrt (Real.sqrt (min 1 t))) := hround
    _ ≤ 1024 * (8000 * n ^ (4 : ℕ) * F) :=
      mul_le_mul_of_nonneg_left hrootBound (by norm_num)
    _ ≤ 10000000 * n ^ (4 : ℕ) * F := by
      calc
        1024 * (8000 * n ^ (4 : ℕ) * F) =
            (1024 * 8000) * (n ^ (4 : ℕ) * F) := by ring
        _ ≤ 10000000 * (n ^ (4 : ℕ) * F) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hn4 hF)
        _ = 10000000 * n ^ (4 : ℕ) * F := by ring

end

end MIPStarRE.QPBT
