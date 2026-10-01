module

public import MIPStarRE.QPBT.Combining.QuantitativeScalars
public import MIPStarRE.QPBT.Test.Soundness.ScalarAbsorption

/-!
# Quantitative scalar component bounds for Pauli soundness

This module defines the final scalar errors and proves the component estimates
used to convert the quantitative global-pair error into the common state and
raw-operator errors of the final Pauli soundness theorem.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1491`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The uncapped degree-four quantitative Pauli-soundness error. -/
def pauliSoundnessQuantitativeRawError (P : AdmissibleParams) (e : ℝ) : ℝ :=
  100000000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
    pauliSoundnessQuantitativeEnvelope P e

/-- The final common error, with the source error clipped to the probability
range and the universal state/operator cap applied. -/
def pauliSoundnessQuantitativeError (P : AdmissibleParams) (epsilon : ℝ) : ℝ :=
  min 4 (pauliSoundnessQuantitativeRawError P (min epsilon 1))

/-- The uncapped degree-two Pauli-soundness error retained for compatibility
with the issue #729 quantitative interface.

Bound: deferred #727. -/
def pauliSoundnessQuantitativeDegreeTwoRawError
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  1000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (2 : ℕ)) *
    pauliSoundnessQuantitativeEnvelope P e

/-- The degree-two common error, with the source error clipped to the
probability range and the universal cap applied.

Bound: deferred #727. -/
def pauliSoundnessQuantitativeDegreeTwoError
    (P : AdmissibleParams) (epsilon : ℝ) : ℝ :=
  min 4 (pauliSoundnessQuantitativeDegreeTwoRawError P (min epsilon 1))

/-- The extraction scale at the concrete native global-pair error. The direct
passing error, native low-degree error, and rounded-pair error are retained
without replacing them by the common polynomial envelope. -/
def pauliSoundnessQuantitativeMixedScale (P : AdmissibleParams) (e : ℝ) : ℝ :=
  let r := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError e + (P.m : ℝ) *
      pauliBaselineExtendedLineError e r) r
  let lambda := directNativeError P.extendedDirectLd passing
  2800 *
    (nativeGlobalPairError P lambda (pauliBaselinePointError e) +
      Real.sqrt e + r)

/-- The raw operator-family component expression at the native mixed
extraction scale. -/
def pauliSoundnessQuantitativeMixedOperatorError
    (P : AdmissibleParams) (e : ℝ) : ℝ :=
  472 * pauliSoundnessQuantitativeMixedScale P e +
    24 * (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) +
    192 * Real.sqrt (pauliSoundnessQuantitativeMixedScale P e) + 344 * e

/-- The final exponent is half the quantitative global-pair exponent. -/
theorem pauli_soundness_quantitative_power_eq_half_global_pair :
    pauliSoundnessQuantitativePower = quantitativeGlobalPairPower / 2 := by
  unfold pauliSoundnessQuantitativePower quantitativeGlobalPairPower
  norm_num

/-- The final exponent is positive. -/
theorem pauli_soundness_quantitative_power_pos :
    0 < pauliSoundnessQuantitativePower := by
  unfold pauliSoundnessQuantitativePower
  norm_num

/-- The final exponent is strictly below one. -/
theorem pauli_soundness_quantitative_power_lt_one :
    pauliSoundnessQuantitativePower < 1 := by
  unfold pauliSoundnessQuantitativePower
  norm_num

/-- The final exponent improves the explicit baseline exponent by the exact
factor `625 / 8 = 78.125`. -/
theorem pauli_soundness_quantitative_power_eq_gain_mul_baseline :
    pauliSoundnessQuantitativePower =
      (625 / 8 : ℝ) * pauliSoundnessBaselinePower := by
  unfold pauliSoundnessQuantitativePower pauliSoundnessBaselinePower
  norm_num

/-- The final three-term envelope is strictly positive on the nonnegative
error domain. -/
theorem pauli_soundness_quantitative_envelope_pos
    (P : AdmissibleParams) {e : ℝ} (he : 0 ≤ e) :
    0 < pauliSoundnessQuantitativeEnvelope P e := by
  have hq : (0 : ℝ) < (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    positivity
  unfold pauliSoundnessQuantitativeEnvelope
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_nonneg_of_pos (Real.rpow_nonneg he _)
      (Real.rpow_pos_of_pos hq _))
    (Real.rpow_nonneg (by norm_num) _)

/-- Shrinking the exponent from the global-pair power to the final power
enlarges each term of the envelope on the probability domain. -/
theorem quantitative_global_pair_envelope_le_pauli_soundness
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    quantitativeGlobalPairEnvelope P e ≤
      pauliSoundnessQuantitativeEnvelope P e := by
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow power 2 (by norm_num)
  have hn0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by positivity
  have hpower : pauliSoundnessQuantitativePower ≤ quantitativeGlobalPairPower := by
    unfold pauliSoundnessQuantitativePower quantitativeGlobalPairPower
    norm_num
  unfold quantitativeGlobalPairEnvelope pauliSoundnessQuantitativeEnvelope
  exact add_le_add
    (add_le_add
      (Real.rpow_le_rpow_of_exponent_ge' he he1
        pauli_soundness_quantitative_power_pos.le hpower)
      (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hpower)))
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (mul_le_mul_of_nonneg_right hpower hn0)))

/-- The square root of the global-pair envelope is bounded by the final
three-term envelope. -/
theorem sqrt_quantitative_global_pair_envelope_le_pauli_soundness
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    Real.sqrt (quantitativeGlobalPairEnvelope P e) ≤
      pauliSoundnessQuantitativeEnvelope P e := by
  let x := Real.rpow e quantitativeGlobalPairPower
  let y := Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower)
  let z := Real.rpow 2
    (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ)))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  rw [show quantitativeGlobalPairEnvelope P e = x + y + z by rfl,
    Real.sqrt_eq_rpow]
  have hsplit : Real.rpow (x + y + z) (1 / 2 : ℝ) ≤
      Real.rpow x (1 / 2 : ℝ) + Real.rpow y (1 / 2 : ℝ) +
        Real.rpow z (1 / 2 : ℝ) :=
    (Real.rpow_add_le_add_rpow (add_nonneg hx hy) hz
      (by norm_num) (by norm_num)).trans
      (add_le_add
        (Real.rpow_add_le_add_rpow hx hy (by norm_num) (by norm_num)) le_rfl)
  have hxRoot : Real.rpow x (1 / 2 : ℝ) =
      Real.rpow e pauliSoundnessQuantitativePower := by
    dsimp [x]
    calc
      Real.rpow (Real.rpow e quantitativeGlobalPairPower) (1 / 2 : ℝ) =
          Real.rpow e (quantitativeGlobalPairPower * (1 / 2 : ℝ)) :=
        (Real.rpow_mul he _ _).symm
      _ = _ := by
        congr 1
        unfold quantitativeGlobalPairPower pauliSoundnessQuantitativePower
        norm_num
  have hyRoot : Real.rpow y (1 / 2 : ℝ) =
      Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) := by
    dsimp [y]
    calc
      Real.rpow (Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower))
          (1 / 2 : ℝ) =
          Real.rpow (P.q : ℝ)
            ((-quantitativeGlobalPairPower) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by positivity) _ _).symm
      _ = _ := by
        congr 1
        unfold quantitativeGlobalPairPower pauliSoundnessQuantitativePower
        norm_num
  have hzRoot : Real.rpow z (1 / 2 : ℝ) = Real.rpow 2
      (-(pauliSoundnessQuantitativePower * ((P.m * P.d : ℕ) : ℝ))) := by
    dsimp [z]
    calc
      Real.rpow
          (Real.rpow 2
            (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ))))
          (1 / 2 : ℝ) =
          Real.rpow 2
            ((-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ))) *
              (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = _ := by
        congr 1
        unfold quantitativeGlobalPairPower pauliSoundnessQuantitativePower
        ring
  rw [hxRoot, hyRoot, hzRoot] at hsplit
  simpa only [Real.rpow_eq_pow, pauliSoundnessQuantitativeEnvelope] using hsplit

/-- The square root of the clipped strategy error is absorbed by the
global-pair envelope. -/
theorem sqrt_error_le_quantitative_global_pair_envelope
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    Real.sqrt e ≤ quantitativeGlobalPairEnvelope P e := by
  have hpower : quantitativeGlobalPairPower ≤ (1 / 2 : ℝ) := by
    unfold quantitativeGlobalPairPower
    norm_num
  have hpower0 : 0 ≤ quantitativeGlobalPairPower := by
    unfold quantitativeGlobalPairPower
    norm_num
  have hterm : Real.sqrt e ≤ Real.rpow e quantitativeGlobalPairPower := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' he he1 hpower0 hpower
  calc
    Real.sqrt e ≤ Real.rpow e quantitativeGlobalPairPower := hterm
    _ ≤ quantitativeGlobalPairEnvelope P e := by
      unfold quantitativeGlobalPairEnvelope
      exact (le_add_of_nonneg_right
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))

/-- The field ratio is absorbed by the global-pair envelope with one factor
of `m*d`. -/
theorem quantitative_ratio_le_global_pair_envelope
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤
      ((P.m * P.d : ℕ) : ℝ) * quantitativeGlobalPairEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    exact_mod_cast Nat.one_le_pow power 2 (by norm_num)
  have hpower : quantitativeGlobalPairPower ≤ 1 := by
    unfold quantitativeGlobalPairPower
    norm_num
  have hinv : (P.q : ℝ)⁻¹ ≤
      Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) := by
    simp only [Real.rpow_eq_pow]
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hpower)
  have hfield : Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) ≤
      quantitativeGlobalPairEnvelope P e := by
    unfold quantitativeGlobalPairEnvelope
    exact (le_add_of_nonneg_left (Real.rpow_nonneg he _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  change n / (P.q : ℝ) ≤ n * quantitativeGlobalPairEnvelope P e
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (hinv.trans hfield) hn0

/-- The extraction scale obtained from a quantitative global-pair witness is
bounded by `10^11 (m*d)^4` times the global-pair envelope. -/
theorem quantitative_extraction_scale_le
    (P : AdmissibleParams) (e g : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hg : g ≤ 10000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
      quantitativeGlobalPairEnvelope P e) :
    2800 * (g + Real.sqrt e + ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let E := quantitativeGlobalPairEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn4 : 1 ≤ n ^ (4 : ℕ) := one_le_pow₀ hn
  have hE : 0 ≤ E := by
    dsimp [E, quantitativeGlobalPairEnvelope]
    positivity
  have hsqrt : Real.sqrt e ≤ E := by
    dsimp [E]
    exact sqrt_error_le_quantitative_global_pair_envelope P e he he1
  have hsqrtLarge : Real.sqrt e ≤ n ^ (4 : ℕ) * E :=
    hsqrt.trans (le_mul_of_one_le_left hE hn4)
  have hratio : n / (P.q : ℝ) ≤ n * E := by
    dsimp [n, E]
    exact quantitative_ratio_le_global_pair_envelope P e he
  have hnLe : n ≤ n ^ (4 : ℕ) := by
    simpa using pow_le_pow_right₀ hn (by norm_num : 1 ≤ 4)
  have hratioLarge : n / (P.q : ℝ) ≤ n ^ (4 : ℕ) * E :=
    hratio.trans (mul_le_mul_of_nonneg_right hnLe hE)
  have hbase : 0 ≤ n ^ (4 : ℕ) * E := mul_nonneg (by positivity) hE
  change 2800 * (g + Real.sqrt e + n / (P.q : ℝ)) ≤
    100000000000 * n ^ (4 : ℕ) * E
  calc
    2800 * (g + Real.sqrt e + n / (P.q : ℝ)) ≤
        2800 * ((10000000 + 2) * (n ^ (4 : ℕ) * E)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      nlinarith
    _ = (2800 * (10000000 + 2)) * (n ^ (4 : ℕ) * E) := by ring
    _ ≤ 100000000000 * (n ^ (4 : ℕ) * E) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = 100000000000 * n ^ (4 : ℕ) * E := by ring

/-- Taking the square root of the extraction-scale bound retains the degree-two
parameter factor supplied by the square root of `(m*d)^4`. -/
theorem sqrt_quantitative_extraction_scale_le_degree_two
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (_hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e) :
    Real.sqrt x ≤
      1000000 * (((P.m * P.d : ℕ) : ℝ) ^ (2 : ℕ)) *
        pauliSoundnessQuantitativeEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let E := quantitativeGlobalPairEnvelope P e
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hE : 0 ≤ E := by dsimp [E, quantitativeGlobalPairEnvelope]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hEF : Real.sqrt E ≤ F := by
    dsimp [E, F]
    exact sqrt_quantitative_global_pair_envelope_le_pauli_soundness P e he
  have hconstant : Real.sqrt (100000000000 : ℝ) ≤ 1000000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hnRoot : Real.sqrt (n ^ (4 : ℕ)) = n ^ (2 : ℕ) := by
    rw [show n ^ (4 : ℕ) = (n ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
      Real.sqrt_sq (sq_nonneg n)]
  have hfactor : Real.sqrt (100000000000 * (n ^ (4 : ℕ) * E)) =
      Real.sqrt 100000000000 * n ^ (2 : ℕ) * Real.sqrt E := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100000000000),
      Real.sqrt_mul (by positivity : 0 ≤ n ^ (4 : ℕ)), hnRoot]
    ring
  have hroot := Real.sqrt_le_sqrt hbound
  have hroot' : Real.sqrt x ≤
      Real.sqrt (100000000000 * (n ^ (4 : ℕ) * E)) := by
    simpa only [n, E, mul_assoc] using hroot
  change Real.sqrt x ≤ 1000000 * n ^ (2 : ℕ) * F
  rw [hfactor] at hroot'
  exact hroot'.trans (mul_le_mul
    (mul_le_mul hconstant le_rfl (by positivity) (by norm_num)) hEF
    (Real.sqrt_nonneg E) (mul_nonneg (by norm_num) (by positivity)))

/-- Weakening: `sqrt_quantitative_extraction_scale_le_degree_two` implies this
degree-four form because the historical structured theorem retains the older
parameter factor.

Bound: deferred #727. -/
theorem sqrt_quantitative_extraction_scale_le
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (_hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e) :
    Real.sqrt x ≤
      1000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        pauliSoundnessQuantitativeEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn2 : n ^ (2 : ℕ) ≤ n ^ (4 : ℕ) :=
    pow_le_pow_right₀ hn (by norm_num)
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hsharp := sqrt_quantitative_extraction_scale_le_degree_two
    P e x he _hx hbound
  change Real.sqrt x ≤ 1000000 * n ^ (4 : ℕ) * F
  exact hsharp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn2 (by norm_num)) hF)

/-- The field ratio is bounded by the degree-two final-envelope factor. -/
theorem quantitative_ratio_le_degree_two_base
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤
      (((P.m * P.d : ℕ) : ℝ) ^ (2 : ℕ)) *
        pauliSoundnessQuantitativeEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let E := quantitativeGlobalPairEnvelope P e
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hE : 0 ≤ E := by dsimp [E, quantitativeGlobalPairEnvelope]; positivity
  have hEF : E ≤ F := by
    dsimp [E, F]
    exact quantitative_global_pair_envelope_le_pauli_soundness P e he he1
  have hratio : n / (P.q : ℝ) ≤ n * E := by
    dsimp [n, E]
    exact quantitative_ratio_le_global_pair_envelope P e he
  have hn2 : n ≤ n ^ (2 : ℕ) := by
    simpa using pow_le_pow_right₀ hn (by norm_num : 1 ≤ 2)
  change n / (P.q : ℝ) ≤ n ^ (2 : ℕ) * F
  exact hratio.trans ((mul_le_mul_of_nonneg_right hn2 hE).trans
    (mul_le_mul_of_nonneg_left hEF (by positivity)))

/-- The clipped strategy error is bounded by the degree-two final-envelope
factor. -/
theorem quantitative_error_le_degree_two_base
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    e ≤ (((P.m * P.d : ℕ) : ℝ) ^ (2 : ℕ)) *
      pauliSoundnessQuantitativeEnvelope P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn2 : 1 ≤ n ^ (2 : ℕ) := one_le_pow₀ hn
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hePower : e ≤ Real.rpow e pauliSoundnessQuantitativePower := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' he he1
      pauli_soundness_quantitative_power_pos.le
      pauli_soundness_quantitative_power_lt_one.le
  have heF : e ≤ F := by
    dsimp [F, pauliSoundnessQuantitativeEnvelope]
    exact hePower.trans ((le_add_of_nonneg_right
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)))
  change e ≤ n ^ (2 : ℕ) * F
  exact heF.trans (le_mul_of_one_le_left hF hn2)

/-- On the nonsaturated degree-two branch, the field ratio is below
`4 * 10^-9`. -/
theorem quantitative_ratio_lt_four_billionth_of_degree_two_raw_lt_four
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : pauliSoundnessQuantitativeDegreeTwoRawError P e < 4) :
    ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) < 4 / 1000000000 := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hratio : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ n ^ (2 : ℕ) * F := by
    simpa only [n, F] using quantitative_ratio_le_degree_two_base P e he he1
  have hbase : n ^ (2 : ℕ) * F < 4 / 1000000000 := by
    unfold pauliSoundnessQuantitativeDegreeTwoRawError at hsmall
    change 1000000000 * n ^ (2 : ℕ) * F < 4 at hsmall
    nlinarith
  exact hratio.trans_lt hbase

/-- The extraction square root is below `0.004` on the nonsaturated
degree-two branch. -/
theorem sqrt_quantitative_extraction_scale_lt_four_thousandths
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e)
    (hsmall : pauliSoundnessQuantitativeDegreeTwoRawError P e < 4) :
    Real.sqrt x < 4 / 1000 := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hsqrt : Real.sqrt x ≤ 1000000 * (n ^ (2 : ℕ) * F) := by
    simpa only [n, F, mul_assoc] using
      sqrt_quantitative_extraction_scale_le_degree_two P e x he hx hbound
  have hbase : n ^ (2 : ℕ) * F < 4 / 1000000000 := by
    unfold pauliSoundnessQuantitativeDegreeTwoRawError at hsmall
    change 1000000000 * n ^ (2 : ℕ) * F < 4 at hsmall
    nlinarith
  nlinarith

/-- The extraction scale is below one on the nonsaturated degree-two branch. -/
theorem quantitative_extraction_scale_lt_one_of_degree_two_raw_lt_four
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e)
    (hsmall : pauliSoundnessQuantitativeDegreeTwoRawError P e < 4) :
    x < 1 := by
  have hsqrt := sqrt_quantitative_extraction_scale_lt_four_thousandths
    P e x he hx hbound hsmall
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- The unsquared state component is strictly below the uncapped degree-two
error. -/
theorem quantitative_state_component_lt_degree_two_raw_error
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e) :
    4 * Real.sqrt x < pauliSoundnessQuantitativeDegreeTwoRawError P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hsqrt : Real.sqrt x ≤ 1000000 * (n ^ (2 : ℕ) * F) := by
    simpa only [n, F, mul_assoc] using
      sqrt_quantitative_extraction_scale_le_degree_two P e x he hx hbound
  have hbase : 0 < n ^ (2 : ℕ) * F := by
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast Nat.mul_pos P.one_le_m P.hd
    have hF : 0 < F := by
      dsimp [F]
      exact pauli_soundness_quantitative_envelope_pos P he
    positivity
  have hscaled : 4 * Real.sqrt x ≤ 4000000 * (n ^ (2 : ℕ) * F) := by
    nlinarith
  have hstrict : 4000000 * (n ^ (2 : ℕ) * F) <
      1000000000 * (n ^ (2 : ℕ) * F) :=
    mul_lt_mul_of_pos_right (by norm_num) hbase
  unfold pauliSoundnessQuantitativeDegreeTwoRawError
  simpa only [n, F, mul_assoc] using hscaled.trans_lt hstrict

/-- On the nonsaturated degree-two branch, each raw operator component is
strictly below the uncapped degree-two error. -/
theorem quantitative_operator_component_lt_degree_two_raw_error
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e)
    (hsmall : pauliSoundnessQuantitativeDegreeTwoRawError P e < 4) :
    472 * x + 24 * (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) +
        192 * Real.sqrt x + 344 * e <
      pauliSoundnessQuantitativeDegreeTwoRawError P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let F := pauliSoundnessQuantitativeEnvelope P e
  let base := n ^ (2 : ℕ) * F
  have hratio : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ base := by
    simpa only [n, F, base] using quantitative_ratio_le_degree_two_base P e he he1
  have heBase : e ≤ base := by
    simpa only [n, F, base] using quantitative_error_le_degree_two_base P e he he1
  have hsqrt : Real.sqrt x ≤ 1000000 * base := by
    simpa only [n, F, base, mul_assoc] using
      sqrt_quantitative_extraction_scale_le_degree_two P e x he hx hbound
  have hx1 := quantitative_extraction_scale_lt_one_of_degree_two_raw_lt_four
    P e x he hx hbound hsmall
  have hxSqrt : x ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  have hbase : 0 < base := by
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast Nat.mul_pos P.one_le_m P.hd
    have hF : 0 < F := by
      dsimp [F]
      exact pauli_soundness_quantitative_envelope_pos P he
    dsimp only [base]
    positivity
  have hcomponents :
      472 * x + 24 * (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) +
          192 * Real.sqrt x + 344 * e ≤ 664000368 * base := by
    nlinarith
  have hstrict : 664000368 * base < 1000000000 * base :=
    mul_lt_mul_of_pos_right (by norm_num) hbase
  unfold pauliSoundnessQuantitativeDegreeTwoRawError
  simpa only [n, F, base, mul_assoc] using hcomponents.trans_lt hstrict

/-- The unsquared state error obtained from the componentwise extraction bound
is absorbed by the common degree-four error. -/
theorem quantitative_state_component_le_raw_error
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e) :
    4 * Real.sqrt x ≤ pauliSoundnessQuantitativeRawError P e := by
  have hsqrt := sqrt_quantitative_extraction_scale_le P e x he hx hbound
  have hF : 0 ≤ pauliSoundnessQuantitativeEnvelope P e :=
    pauli_soundness_quantitative_envelope_nonneg P he
  unfold pauliSoundnessQuantitativeRawError
  calc
    4 * Real.sqrt x ≤
        4 * (1000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
          pauliSoundnessQuantitativeEnvelope P e) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ 100000000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
          pauliSoundnessQuantitativeEnvelope P e := by
      calc
        4 * (1000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
            pauliSoundnessQuantitativeEnvelope P e) =
            4000000 * ((((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
              pauliSoundnessQuantitativeEnvelope P e) := by ring
        _ ≤ 100000000000000 * ((((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
              pauliSoundnessQuantitativeEnvelope P e) :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (mul_nonneg (by positivity) hF)
        _ = _ := by ring

/-- Both raw operator-component estimates are absorbed by the same common
degree-four error. -/
theorem quantitative_operator_component_le_raw_error
    (P : AdmissibleParams) (e x : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) (hx : 0 ≤ x)
    (hbound : x ≤
      100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e) :
    472 * x + 24 * (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) +
        192 * Real.sqrt x + 344 * e ≤
      pauliSoundnessQuantitativeRawError P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let E := quantitativeGlobalPairEnvelope P e
  let F := pauliSoundnessQuantitativeEnvelope P e
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hn4 : 1 ≤ n ^ (4 : ℕ) := one_le_pow₀ hn
  have hE : 0 ≤ E := by dsimp [E, quantitativeGlobalPairEnvelope]; positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    exact pauli_soundness_quantitative_envelope_nonneg P he
  have hEF : E ≤ F := by
    dsimp [E, F]
    exact quantitative_global_pair_envelope_le_pauli_soundness P e he he1
  have hxF : x ≤ 100000000000 * (n ^ (4 : ℕ) * F) := by
    have hbound' : x ≤ 100000000000 * (n ^ (4 : ℕ) * E) := by
      simpa only [n, E, mul_assoc] using hbound
    exact hbound'.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hEF (by positivity)) (by norm_num))
  have hratio : n / (P.q : ℝ) ≤ n * E := by
    dsimp [n, E]
    exact quantitative_ratio_le_global_pair_envelope P e he
  have hnLe : n ≤ n ^ (4 : ℕ) := by
    simpa using pow_le_pow_right₀ hn (by norm_num : 1 ≤ 4)
  have hratioF : n / (P.q : ℝ) ≤ n ^ (4 : ℕ) * F :=
    hratio.trans ((mul_le_mul_of_nonneg_right hnLe hE).trans
      (mul_le_mul_of_nonneg_left hEF (by positivity)))
  have hsqrt := sqrt_quantitative_extraction_scale_le P e x he hx hbound
  have hsqrtF : Real.sqrt x ≤ 1000000 * (n ^ (4 : ℕ) * F) := by
    simpa only [n, F, mul_assoc] using hsqrt
  have hePower : e ≤ Real.rpow e pauliSoundnessQuantitativePower := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' he he1
      pauli_soundness_quantitative_power_pos.le
      pauli_soundness_quantitative_power_lt_one.le
  have heF : e ≤ n ^ (4 : ℕ) * F := by
    have heEnvelope : e ≤ F := by
      dsimp [F, pauliSoundnessQuantitativeEnvelope]
      exact hePower.trans ((le_add_of_nonneg_right
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)))
    exact heEnvelope.trans (le_mul_of_one_le_left hF hn4)
  have hbase : 0 ≤ n ^ (4 : ℕ) * F := mul_nonneg (by positivity) hF
  change 472 * x + 24 * (n / (P.q : ℝ)) + 192 * Real.sqrt x + 344 * e ≤
    pauliSoundnessQuantitativeRawError P e
  unfold pauliSoundnessQuantitativeRawError
  calc
    472 * x + 24 * (n / (P.q : ℝ)) + 192 * Real.sqrt x + 344 * e ≤
        472 * (100000000000 * (n ^ (4 : ℕ) * F)) +
          24 * (n ^ (4 : ℕ) * F) +
          192 * (1000000 * (n ^ (4 : ℕ) * F)) +
          344 * (n ^ (4 : ℕ) * F) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hxF (by norm_num))
            (mul_le_mul_of_nonneg_left hratioF (by norm_num)))
          (mul_le_mul_of_nonneg_left hsqrtF (by norm_num)))
        (mul_le_mul_of_nonneg_left heF (by norm_num))
    _ = (472 * 100000000000 + 24 + 192 * 1000000 + 344) *
        (n ^ (4 : ℕ) * F) := by ring
    _ ≤ 100000000000000 * (n ^ (4 : ℕ) * F) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = 100000000000000 * n ^ (4 : ℕ) * F := by ring

/-- When `m*d = 1`, the base-two tail alone forces the uncapped quantitative
error above the universal cap four. -/
theorem four_le_pauli_soundness_quantitative_raw_error_of_md_eq_one
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (hmd : P.m * P.d = 1) :
    4 ≤ pauliSoundnessQuantitativeRawError P e := by
  have hpowerOne : pauliSoundnessQuantitativePower ≤ 1 := by
    unfold pauliSoundnessQuantitativePower
    norm_num
  have htail : (1 / 2 : ℝ) ≤ Real.rpow 2 (-pauliSoundnessQuantitativePower) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      _ = Real.rpow 2 (-1) := (Real.rpow_neg_one 2).symm
      _ ≤ Real.rpow 2 (-pauliSoundnessQuantitativePower) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hpowerOne)
  have htailEnvelope : Real.rpow 2 (-pauliSoundnessQuantitativePower) ≤
      pauliSoundnessQuantitativeEnvelope P e := by
    unfold pauliSoundnessQuantitativeEnvelope
    rw [hmd]
    norm_num only [Nat.cast_one, mul_one]
    exact le_add_of_nonneg_left
      (add_nonneg (Real.rpow_nonneg he _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  unfold pauliSoundnessQuantitativeRawError
  rw [hmd]
  norm_num only [Nat.cast_one, one_pow, mul_one]
  nlinarith

/-- If the field ratio is at least one, the field term forces the uncapped
quantitative error above the universal cap four. -/
theorem four_le_pauli_soundness_quantitative_raw_error_of_one_le_ratio
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e)
    (hr : 1 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) :
    4 ≤ pauliSoundnessQuantitativeRawError P e := by
  let n : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hqpos : (0 : ℝ) < (P.q : ℝ) := by
    obtain ⟨power, _, hq⟩ := P.hq
    rw [hq]
    positivity
  have hqle : (P.q : ℝ) ≤ n := by
    dsimp [n]
    simpa only [one_mul] using (le_div_iff₀ hqpos).mp hr
  have hpower0 : 0 ≤ pauliSoundnessQuantitativePower :=
    pauli_soundness_quantitative_power_pos.le
  have hfield : Real.rpow n (-pauliSoundnessQuantitativePower) ≤
      Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) :=
    Real.rpow_le_rpow_of_nonpos hqpos hqle (neg_nonpos.mpr hpower0)
  have hexponent : 0 ≤ (4 : ℝ) - pauliSoundnessQuantitativePower := by
    nlinarith [pauli_soundness_quantitative_power_lt_one]
  have hproduct : 1 ≤ n ^ (4 : ℕ) *
      Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) := by
    have hsplit : Real.rpow n ((4 : ℝ) - pauliSoundnessQuantitativePower) =
        Real.rpow n 4 * Real.rpow n (-pauliSoundnessQuantitativePower) := by
      rw [sub_eq_add_neg]
      exact Real.rpow_add hnpos 4 (-pauliSoundnessQuantitativePower)
    have hnat : Real.rpow n 4 = n ^ (4 : ℕ) := by
      exact Real.rpow_natCast n 4
    calc
      1 ≤ Real.rpow n ((4 : ℝ) - pauliSoundnessQuantitativePower) :=
        Real.one_le_rpow hn hexponent
      _ = Real.rpow n 4 * Real.rpow n (-pauliSoundnessQuantitativePower) := hsplit
      _ = n ^ (4 : ℕ) * Real.rpow n (-pauliSoundnessQuantitativePower) := by rw [hnat]
      _ ≤ n ^ (4 : ℕ) *
          Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) :=
        mul_le_mul_of_nonneg_left hfield (by positivity)
  have hfieldEnvelope : Real.rpow (P.q : ℝ) (-pauliSoundnessQuantitativePower) ≤
      pauliSoundnessQuantitativeEnvelope P e := by
    unfold pauliSoundnessQuantitativeEnvelope
    exact (le_add_of_nonneg_left (Real.rpow_nonneg he _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  have hbase : 1 ≤ n ^ (4 : ℕ) * pauliSoundnessQuantitativeEnvelope P e :=
    hproduct.trans (mul_le_mul_of_nonneg_left hfieldEnvelope (by positivity))
  change 4 ≤ pauliSoundnessQuantitativeRawError P e
  unfold pauliSoundnessQuantitativeRawError
  change 4 ≤ 100000000000000 * n ^ (4 : ℕ) *
    pauliSoundnessQuantitativeEnvelope P e
  nlinarith

/-- The final envelope is monotone in its error argument on nonnegative
inputs. -/
theorem pauli_soundness_quantitative_envelope_mono_error
    (P : AdmissibleParams) {e epsilon : ℝ} (he : 0 ≤ e) (hle : e ≤ epsilon) :
    pauliSoundnessQuantitativeEnvelope P e ≤
      pauliSoundnessQuantitativeEnvelope P epsilon := by
  unfold pauliSoundnessQuantitativeEnvelope
  exact add_le_add
    (add_le_add
      (Real.rpow_le_rpow he hle pauli_soundness_quantitative_power_pos.le)
      le_rfl) le_rfl

end

end MIPStarRE.QPBT
