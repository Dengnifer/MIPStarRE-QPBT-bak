module

public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.Fractional

/-!
# Canonical comparisons for quantitative Pauli soundness

This module compares the quantitative Pauli-soundness errors with the canonical
`deltaQld` form and the fixed explicit baseline.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1491`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- Weakening: the terminal fractional-dimensional error is bounded by the
degree-two compatibility error at the same exponent.

Bound: deferred #727. -/
theorem pauli_soundness_quantitative_fractional_error_le_degree_two
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeFractionalError P epsilon ≤
      pauliSoundnessQuantitativeDegreeTwoError P epsilon := by
  let e := min epsilon 1
  let m : ℝ := P.m
  let d : ℝ := P.d
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast P.one_le_m
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast P.hd
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hdimension : pauliSoundnessQuantitativeFractionalDimension P ≤ n ^ (2 : ℕ) := by
    have hmPower : Real.rpow m (20481 / 262144 : ℝ) ≤ m ^ (2 : ℕ) := by
      calc
        Real.rpow m (20481 / 262144 : ℝ) ≤ Real.rpow m 2 :=
          Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
        _ = m ^ (2 : ℕ) := Real.rpow_natCast m 2
    have hdPower : Real.rpow d (1 / 64 : ℝ) ≤ d ^ (2 : ℕ) := by
      calc
        Real.rpow d (1 / 64 : ℝ) ≤ Real.rpow d 2 :=
          Real.rpow_le_rpow_of_exponent_le hd (by norm_num)
        _ = d ^ (2 : ℕ) := Real.rpow_natCast d 2
    dsimp [pauliSoundnessQuantitativeFractionalDimension, m, d, n]
    push_cast
    calc
      Real.rpow (P.m : ℝ) (20481 / 262144 : ℝ) *
          Real.rpow (P.d : ℝ) (1 / 64 : ℝ) ≤
          (P.m : ℝ) ^ (2 : ℕ) * Real.rpow (P.d : ℝ) (1 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_right hmPower (Real.rpow_nonneg (by positivity) _)
      _ ≤ (P.m : ℝ) ^ (2 : ℕ) * (P.d : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hdPower (by positivity)
      _ = ((P.m : ℝ) * (P.d : ℝ)) ^ (2 : ℕ) := by ring
  have hdimension0 : 0 ≤ pauliSoundnessQuantitativeFractionalDimension P := by
    unfold pauliSoundnessQuantitativeFractionalDimension
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hraw : pauliSoundnessQuantitativeFractionalRawError P e ≤
      pauliSoundnessQuantitativeDegreeTwoRawError P e := by
    unfold pauliSoundnessQuantitativeFractionalRawError
      pauliSoundnessQuantitativeDegreeTwoRawError
    change 10769120 * pauliSoundnessQuantitativeFractionalDimension P * F ≤
      1000000000 * n ^ (2 : ℕ) * F
    calc
      10769120 * pauliSoundnessQuantitativeFractionalDimension P * F ≤
          1000000000 * pauliSoundnessQuantitativeFractionalDimension P * F := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) hdimension0) hF
      _ ≤ 1000000000 * n ^ (2 : ℕ) * F :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdimension (by norm_num)) hF
  unfold pauliSoundnessQuantitativeFractionalError
    pauliSoundnessQuantitativeDegreeTwoError
  change min 4 (pauliSoundnessQuantitativeFractionalRawError P e) ≤
    min 4 (pauliSoundnessQuantitativeDegreeTwoRawError P e)
  exact min_le_min_left 4 hraw

/-- The degree-four structured error is bounded by the canonical
`deltaQld 100` error at the same exponent. -/
theorem pauli_soundness_quantitative_error_le_deltaQld
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeError P epsilon ≤
      deltaQld 100 pauliSoundnessQuantitativePower epsilon P.m P.d P.q := by
  let e := min epsilon 1
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  have he1 : e ≤ 1 := by dsimp [e]; exact min_le_right _ _
  have hepsilonBound : e ≤ epsilon := by dsimp [e]; exact min_le_left _ _
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have henvMono := pauli_soundness_quantitative_envelope_mono_error
    P he hepsilonBound
  by_cases hmd : P.m * P.d = 1
  · have htail : (1 / 2 : ℝ) ≤ Real.rpow 2
        (-(pauliSoundnessQuantitativePower * n)) := by
      dsimp [n]
      rw [hmd]
      norm_num only [Nat.cast_one, mul_one]
      calc
        (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
        _ = Real.rpow 2 (-1) := (Real.rpow_neg_one 2).symm
        _ ≤ Real.rpow 2 (-pauliSoundnessQuantitativePower) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [pauli_soundness_quantitative_power_lt_one]
    have hdelta : 4 ≤
        deltaQld 100 pauliSoundnessQuantitativePower epsilon P.m P.d P.q := by
      have heTerm := Real.rpow_nonneg hepsilon pauliSoundnessQuantitativePower
      have hqTerm := Real.rpow_nonneg (Nat.cast_nonneg P.q)
        (-pauliSoundnessQuantitativePower)
      have htail' : (1 / 2 : ℝ) ≤
          Real.rpow 2 (-pauliSoundnessQuantitativePower) := by
        simpa only [n, hmd, Nat.cast_one, mul_one] using htail
      have hsum : (1 / 2 : ℝ) ≤
          Real.rpow epsilon pauliSoundnessQuantitativePower +
            Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) +
            Real.rpow 2 (-pauliSoundnessQuantitativePower) := by
        exact htail'.trans (le_add_of_nonneg_left (add_nonneg heTerm hqTerm))
      unfold deltaQld
      rw [hmd]
      norm_num only [Nat.cast_one, mul_one]
      have hone : Real.rpow 1 100 = 1 := Real.one_rpow 100
      rw [hone]
      nlinarith
    exact (min_le_left _ _).trans hdelta
  · have hmdNat : 2 ≤ P.m * P.d := by
      have hpos : 0 < P.m * P.d := Nat.mul_pos P.one_le_m P.hd
      omega
    have hn2 : (2 : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hmdNat
    have hpow96 : (2 : ℝ) ^ (96 : ℕ) ≤ n ^ (96 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hn2 96
    have hcoefficient :
        100000000000000 * n ^ (4 : ℕ) ≤ 100 * n ^ (100 : ℕ) := by
      calc
        100000000000000 * n ^ (4 : ℕ) ≤
            (100 * (2 : ℝ) ^ (96 : ℕ)) * n ^ (4 : ℕ) := by
          gcongr
          norm_num
        _ ≤ (100 * n ^ (96 : ℕ)) * n ^ (4 : ℕ) := by gcongr
        _ = 100 * n ^ (100 : ℕ) := by ring
    have henv0 : 0 ≤ pauliSoundnessQuantitativeEnvelope P e :=
      pauli_soundness_quantitative_envelope_nonneg P he
    change min 4 (pauliSoundnessQuantitativeRawError P e) ≤
      deltaQld 100 pauliSoundnessQuantitativePower epsilon P.m P.d P.q
    refine (min_le_right _ _).trans ?_
    unfold pauliSoundnessQuantitativeRawError deltaQld
    have hnat : Real.rpow n 100 = n ^ (100 : ℕ) := by
      exact Real.rpow_natCast n 100
    change 100000000000000 * n ^ (4 : ℕ) *
        pauliSoundnessQuantitativeEnvelope P e ≤
      100 * Real.rpow n 100 *
        (Real.rpow epsilon pauliSoundnessQuantitativePower +
          Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) +
          Real.rpow 2 (-(pauliSoundnessQuantitativePower * n)))
    rw [hnat]
    exact mul_le_mul hcoefficient henvMono henv0 (by positivity)

/-- The capped degree-two error is bounded by the historical capped
degree-four error on the source domain. -/
theorem pauli_soundness_quantitative_degree_two_error_le_quantitative_error
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeDegreeTwoError P epsilon ≤
      pauliSoundnessQuantitativeError P epsilon := by
  let e := min epsilon 1
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn24 : n ^ (2 : ℕ) ≤ n ^ (4 : ℕ) :=
    pow_le_pow_right₀ hn (by norm_num)
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hraw : pauliSoundnessQuantitativeDegreeTwoRawError P e ≤
      pauliSoundnessQuantitativeRawError P e := by
    unfold pauliSoundnessQuantitativeDegreeTwoRawError
      pauliSoundnessQuantitativeRawError
    change 1000000000 * n ^ (2 : ℕ) * F ≤ 100000000000000 * n ^ (4 : ℕ) * F
    calc
      1000000000 * n ^ (2 : ℕ) * F ≤
          100000000000000 * n ^ (2 : ℕ) * F := by
        gcongr
        norm_num
      _ ≤ 100000000000000 * n ^ (4 : ℕ) * F := by gcongr
  unfold pauliSoundnessQuantitativeDegreeTwoError pauliSoundnessQuantitativeError
  change min 4 (pauliSoundnessQuantitativeDegreeTwoRawError P e) ≤
    min 4 (pauliSoundnessQuantitativeRawError P e)
  exact min_le_min_left 4 hraw

/-- The degree-two improvement over the historical degree-four error is
strict exactly on the nonsaturated degree-two branch. -/
theorem pauli_soundness_quantitative_degree_two_error_lt_quantitative_error_iff
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeDegreeTwoError P epsilon <
        pauliSoundnessQuantitativeError P epsilon ↔
      pauliSoundnessQuantitativeDegreeTwoRawError P (min epsilon 1) < 4 := by
  let e := min epsilon 1
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  constructor
  · intro hlt
    by_contra hsmall
    have hge : 4 ≤ pauliSoundnessQuantitativeDegreeTwoRawError P e :=
      le_of_not_gt hsmall
    have hnew : pauliSoundnessQuantitativeDegreeTwoError P epsilon = 4 := by
      unfold pauliSoundnessQuantitativeDegreeTwoError
      change min 4 (pauliSoundnessQuantitativeDegreeTwoRawError P e) = 4
      exact min_eq_left hge
    have hold : pauliSoundnessQuantitativeError P epsilon ≤ 4 := by
      unfold pauliSoundnessQuantitativeError
      exact min_le_left _ _
    rw [hnew] at hlt
    linarith
  · intro hsmall
    let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
    let F := pauliSoundnessQuantitativeEnvelope P e
    have hn : 1 ≤ n := by
      dsimp [n]
      exact_mod_cast Nat.mul_pos P.one_le_m P.hd
    have hn24 : n ^ (2 : ℕ) ≤ n ^ (4 : ℕ) :=
      pow_le_pow_right₀ hn (by norm_num)
    have hbase : 0 < n ^ (2 : ℕ) * F := by
      have hF : 0 < F := by
        dsimp [F]
        exact pauli_soundness_quantitative_envelope_pos P he
      positivity
    have hraw : pauliSoundnessQuantitativeDegreeTwoRawError P e <
        pauliSoundnessQuantitativeRawError P e := by
      unfold pauliSoundnessQuantitativeDegreeTwoRawError
        pauliSoundnessQuantitativeRawError
      change 1000000000 * n ^ (2 : ℕ) * F < 100000000000000 * n ^ (4 : ℕ) * F
      calc
        1000000000 * n ^ (2 : ℕ) * F <
            100000000000000 * n ^ (2 : ℕ) * F := by
          simpa only [mul_assoc] using
            mul_lt_mul_of_pos_right
              (show (1000000000 : ℝ) < 100000000000000 by norm_num) hbase
        _ ≤ 100000000000000 * n ^ (4 : ℕ) * F := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hn24
              (pauli_soundness_quantitative_envelope_nonneg P he))
            (by norm_num : (0 : ℝ) ≤ 100000000000000)
    unfold pauliSoundnessQuantitativeDegreeTwoError pauliSoundnessQuantitativeError
    change min 4 (pauliSoundnessQuantitativeDegreeTwoRawError P e) <
      min 4 (pauliSoundnessQuantitativeRawError P e)
    rw [min_eq_right hsmall.le]
    exact lt_min hsmall hraw

/-- The capped degree-two error has the same canonical `deltaQld 100` upper
bound as the historical degree-four result. -/
theorem pauli_soundness_quantitative_degree_two_error_le_deltaQld
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeDegreeTwoError P epsilon ≤
      deltaQld 100 pauliSoundnessQuantitativePower epsilon P.m P.d P.q :=
  (pauli_soundness_quantitative_degree_two_error_le_quantitative_error
    P epsilon hepsilon).trans
    (pauli_soundness_quantitative_error_le_deltaQld P epsilon hepsilon)

/-- The fixed explicit baseline coefficient is strictly larger than the
canonical quantitative coefficient `100`. -/
theorem one_hundred_lt_pauli_soundness_baseline_constant :
    (100 : ℝ) < pauliSoundnessBaselineConstant := by
  obtain ⟨habsorption, -, -, -⟩ := pauli_baseline_global_absorption_bound
  have hglobal : 1 ≤ pauliBaselineGlobalPairConstant := by
    unfold pauliBaselineGlobalPairConstant
    nlinarith
  have hextraction : 1 ≤ pauliBaselineExtractionConstant := by
    unfold pauliBaselineExtractionConstant
    norm_num
  have hprojective : 1 ≤ pauliBaselineProjectiveConstant := by
    have hextractionSq : 1 ≤ pauliBaselineExtractionConstant ^ (2 : ℕ) :=
      one_le_pow₀ hextraction
    have hproduct : 1 ≤
        pauliBaselineExtractionConstant ^ (2 : ℕ) *
          pauliBaselineGlobalPairConstant :=
      one_le_mul_of_one_le_of_one_le hextractionSq hglobal
    unfold pauliBaselineProjectiveConstant
    nlinarith
  have hprojective4 : 1 ≤ pauliBaselineProjectiveConstant ^ (4 : ℕ) :=
    one_le_pow₀ hprojective
  unfold pauliSoundnessBaselineConstant
  nlinarith

/-- At a clipped nonnegative error, the new canonical error is strictly below
the independently proved explicit baseline error. -/
theorem deltaQld_quantitative_lt_explicit_baseline
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    deltaQld 100 pauliSoundnessQuantitativePower e P.m P.d P.q <
      deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
        e P.m P.d P.q := by
  have hbaselinePower : 0 < pauliSoundnessBaselinePower := by
    unfold pauliSoundnessBaselinePower
    norm_num
  have hpower : pauliSoundnessBaselinePower ≤ pauliSoundnessQuantitativePower := by
    unfold pauliSoundnessBaselinePower pauliSoundnessQuantitativePower
    norm_num
  have hmono : deltaQld 100 pauliSoundnessQuantitativePower e P.m P.d P.q ≤
      deltaQld 100 pauliSoundnessBaselinePower e P.m P.d P.q :=
    deltaQld_mono (by norm_num) le_rfl hpower hbaselinePower he he1
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hconstant := one_hundred_lt_pauli_soundness_baseline_constant
  have hpowerN : Real.rpow n 100 ≤
      Real.rpow n pauliSoundnessBaselineConstant :=
    Real.rpow_le_rpow_of_exponent_le hn hconstant.le
  have hprefactor : 100 * Real.rpow n 100 <
      pauliSoundnessBaselineConstant *
        Real.rpow n pauliSoundnessBaselineConstant := by
    exact (mul_lt_mul_of_pos_right hconstant (Real.rpow_pos_of_pos hnpos 100)).trans_le
      (mul_le_mul_of_nonneg_left hpowerN (by linarith))
  have hqpos : (0 : ℝ) < (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    positivity
  have htail : 0 < Real.rpow e pauliSoundnessBaselinePower +
      Real.rpow (P.q : ℝ) (-pauliSoundnessBaselinePower) +
      Real.rpow 2
        (-(pauliSoundnessBaselinePower * ((P.m * P.d : ℕ) : ℝ))) := by
    have heTerm := Real.rpow_nonneg he pauliSoundnessBaselinePower
    have hqTerm := Real.rpow_pos_of_pos hqpos (-pauliSoundnessBaselinePower)
    have htwoTerm := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(pauliSoundnessBaselinePower * ((P.m * P.d : ℕ) : ℝ)))
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos heTerm hqTerm) htwoTerm
  have hstrict : deltaQld 100 pauliSoundnessBaselinePower e P.m P.d P.q <
      deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
        e P.m P.d P.q := by
    unfold deltaQld
    exact mul_lt_mul_of_pos_right hprefactor htail
  exact hmono.trans_lt hstrict

/-- On the clipped source domain, the structured degree-four error is strictly
smaller than the actual explicit baseline error. -/
theorem pauli_soundness_quantitative_error_lt_explicit_baseline_of_le_one
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    pauliSoundnessQuantitativeError P e <
      deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
        e P.m P.d P.q := by
  have hcanonical := pauli_soundness_quantitative_error_le_deltaQld P e he
  unfold pauliSoundnessQuantitativeError at hcanonical
  rw [min_eq_left he1] at hcanonical
  simpa only [pauliSoundnessQuantitativeError, min_eq_left he1] using
    hcanonical.trans_lt (deltaQld_quantitative_lt_explicit_baseline P e he he1)

/-- The before/after comparison for an arbitrary nonnegative source error,
with both bounds evaluated at the clipped error `min epsilon 1`. -/
theorem pauli_soundness_quantitative_error_lt_explicit_baseline_clipped
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeError P epsilon <
      deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
        (min epsilon 1) P.m P.d P.q := by
  let e := min epsilon 1
  have he : 0 ≤ e := by dsimp [e]; exact le_min hepsilon zero_le_one
  have he1 : e ≤ 1 := by dsimp [e]; exact min_le_right _ _
  have h := pauli_soundness_quantitative_error_lt_explicit_baseline_of_le_one
    P e he he1
  simpa only [pauliSoundnessQuantitativeError, e, min_eq_left he1] using h

/-- On the actual clipped source domain, the degree-two common error is
strictly below the independently proved historical explicit baseline. -/
theorem pauli_soundness_quantitative_degree_two_error_lt_explicit_baseline_clipped
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    pauliSoundnessQuantitativeDegreeTwoError P epsilon <
      deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
        (min epsilon 1) P.m P.d P.q :=
  (pauli_soundness_quantitative_degree_two_error_le_quantitative_error
    P epsilon hepsilon).trans_lt
    (pauli_soundness_quantitative_error_lt_explicit_baseline_clipped
      P epsilon hepsilon)

end

end MIPStarRE.QPBT
