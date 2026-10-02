module

public import MIPStarRE.QPBT.Combining.QuantitativeScalarBase

/-!
# Separated native scalar bounds for QPBT

This module propagates the exact native direct low-degree error through
fractional powers without replacing numerical coefficients by parameter
degrees.  The six resulting contributions retain the point error, the two
extended-line terms, the direct ratio term, the field term, and the
exponential tail separately.

## References

* Paper `lem:qld-4-7`,
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* Blueprint `thm:qld-native-small-regime-global-pair`
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The uncapped six-term bound for a power of the native direct low-degree
error. -/
def quantitativeNativeSeparatedRaw
    (P : AdmissibleParams) (e s : ℝ) : ℝ :=
  let h : ℝ := (2 * P.m + 2 : ℕ)
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  Real.rpow h (5 * s / 4) * Real.rpow (P.d : ℝ) (s / 4) *
    (Real.rpow 800000 s *
        (Real.rpow e (quantitativeLowDegreePower * s / 16) +
          Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) *
            Real.rpow e (quantitativeLowDegreePower * s / 512) +
          Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) *
            Real.rpow r (quantitativeLowDegreePower * s / 32) +
          Real.rpow r (quantitativeLowDegreePower * s)) +
      Real.rpow 400000 s *
        (Real.rpow ((P.d : ℝ) / (P.q : ℝ))
            (quantitativeLowDegreePower * s) +
          Real.exp (-(4 * h * (P.d : ℝ) * s))))

/-- The unit-capped six-term bound for a power of the native direct
low-degree error. -/
def quantitativeNativeSeparatedError
    (P : AdmissibleParams) (e s : ℝ) : ℝ :=
  min 1 (quantitativeNativeSeparatedRaw P e s)

private theorem rpow_add_four_le
    {a b c d s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.rpow (a + b + c + d) s ≤
      Real.rpow a s + Real.rpow b s + Real.rpow c s + Real.rpow d s := by
  exact (Real.rpow_add_le_add_rpow (add_nonneg (add_nonneg ha hb) hc) hd hs0 hs1).trans
    (add_le_add
      ((Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hs0 hs1).trans
        (add_le_add (Real.rpow_add_le_add_rpow ha hb hs0 hs1) le_rfl))
      le_rfl)

private theorem rpow_rpow_eq {x a b : ℝ} (hx : 0 ≤ x) :
    Real.rpow (Real.rpow x a) b = Real.rpow x (a * b) :=
  (Real.rpow_mul hx a b).symm

private theorem rpow_le_two_of_le_two_pow_thirty_two
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ (32 : ℕ)) :
    Real.rpow x quantitativeLowDegreePower ≤ 2 := by
  calc
    Real.rpow x quantitativeLowDegreePower ≤
        Real.rpow ((2 : ℝ) ^ (32 : ℕ)) quantitativeLowDegreePower :=
      Real.rpow_le_rpow hx0 hx (by unfold quantitativeLowDegreePower; norm_num)
    _ = Real.rpow 2 (32 * quantitativeLowDegreePower) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 32
        quantitativeLowDegreePower).symm
    _ ≤ Real.rpow 2 1 := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      unfold quantitativeLowDegreePower
      norm_num
    _ = 2 := Real.rpow_one 2

private theorem nine_sqrt_point_constant_rpow_le_two :
    Real.rpow (9 * Real.sqrt pauliBaselinePointConstant)
      quantitativeLowDegreePower ≤ 2 := by
  have hconstant0 : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hroot : Real.sqrt pauliBaselinePointConstant ≤ (40000000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pauli_baseline_point_constant_le]
  apply rpow_le_two_of_le_two_pow_thirty_two
  · positivity
  · calc
      9 * Real.sqrt pauliBaselinePointConstant ≤ 9 * 40000000 := by gcongr
      _ ≤ (2 : ℝ) ^ (32 : ℕ) := by norm_num

private theorem nine_sqrt_extended_constant_rpow_le_two :
    Real.rpow (9 * Real.sqrt pauliBaselineExtendedLineConstant)
      quantitativeLowDegreePower ≤ 2 := by
  have hconstant0 : 0 ≤ pauliBaselineExtendedLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_extended_line_constant
  have hroot : Real.sqrt pauliBaselineExtendedLineConstant ≤ (40000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [pauli_baseline_extended_line_constant_le]
  apply rpow_le_two_of_le_two_pow_thirty_two
  · positivity
  · calc
      9 * Real.sqrt pauliBaselineExtendedLineConstant ≤ 9 * 40000 := by gcongr
      _ ≤ (2 : ℝ) ^ (32 : ℕ) := by norm_num

private theorem nine_rpow_quantitative_low_degree_power_le_two :
    Real.rpow 9 quantitativeLowDegreePower ≤ 2 := by
  apply rpow_le_two_of_le_two_pow_thirty_two (by norm_num)
  norm_num

private theorem quantitative_native_passing_term_le
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    Real.rpow (3 * passing) quantitativeLowDegreePower ≤
      2 * (Real.rpow e (quantitativeLowDegreePower / 16) +
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow e (quantitativeLowDegreePower / 512) +
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow r (quantitativeLowDegreePower / 32) +
        Real.rpow r quantitativeLowDegreePower) := by
  intro r passing
  let Q := pauliBaselinePointError e
  let L := (P.m : ℝ) * pauliBaselineExtendedLineError e r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hm0 : 0 ≤ (P.m : ℝ) := by positivity
  have hpointConstant : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hextendedConstant : 0 ≤ pauliBaselineExtendedLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_extended_line_constant
  have hQ : 0 ≤ Q := by
    dsimp [Q, pauliBaselinePointError]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L, pauliBaselineExtendedLineError]
    positivity
  have htau0 : 0 ≤ quantitativeLowDegreePower := by
    unfold quantitativeLowDegreePower
    norm_num
  have htau1 : quantitativeLowDegreePower ≤ 1 := by
    unfold quantitativeLowDegreePower
    norm_num
  have hQroot : Real.sqrt Q =
      Real.sqrt pauliBaselinePointConstant * Real.rpow e (1 / 16 : ℝ) := by
    dsimp [Q, pauliBaselinePointError]
    rw [Real.sqrt_mul hpointConstant]
    congr 1
    convert (sqrt_rpow_eq (x := e) (a := (1 / 8 : ℝ)) he) using 1
    all_goals simp only [Real.rpow_eq_pow]
    all_goals ring
  have hsumRoot : Real.sqrt
      (Real.rpow e (1 / 256 : ℝ) + Real.rpow r (1 / 16 : ℝ)) ≤
      Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ) := by
    have h := Real.rpow_add_le_add_rpow
      (Real.rpow_nonneg he (1 / 256 : ℝ))
      (Real.rpow_nonneg hr (1 / 16 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have heRoot : Real.sqrt (Real.rpow e (1 / 256 : ℝ)) =
        Real.rpow e (1 / 512 : ℝ) := by
      convert (sqrt_rpow_eq (x := e) (a := (1 / 256 : ℝ)) he) using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    have hrRoot : Real.sqrt (Real.rpow r (1 / 16 : ℝ)) =
        Real.rpow r (1 / 32 : ℝ) := by
      convert (sqrt_rpow_eq (x := r) (a := (1 / 16 : ℝ)) hr) using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    simp only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] at heRoot hrRoot h ⊢
    rw [heRoot, hrRoot] at h
    exact h
  have hLroot : Real.sqrt L ≤
      Real.sqrt (P.m : ℝ) * Real.sqrt pauliBaselineExtendedLineConstant *
        (Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)) := by
    dsimp [L, pauliBaselineExtendedLineError]
    rw [Real.sqrt_mul hm0,
      Real.sqrt_mul hextendedConstant]
    simpa only [Real.rpow_eq_pow, mul_assoc] using mul_le_mul_of_nonneg_left hsumRoot
      (mul_nonneg (Real.sqrt_nonneg (P.m : ℝ))
        (Real.sqrt_nonneg pauliBaselineExtendedLineConstant))
  have hQLroot : Real.sqrt (Q + L) ≤ Real.sqrt Q + Real.sqrt L := by
    simpa only [Real.sqrt_eq_rpow] using
      Real.rpow_add_le_add_rpow hQ hL
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hfirst : Real.rpow (9 * Real.sqrt Q) quantitativeLowDegreePower ≤
      2 * Real.rpow e (quantitativeLowDegreePower / 16) := by
    rw [hQroot]
    calc
      Real.rpow (9 * (Real.sqrt pauliBaselinePointConstant *
          Real.rpow e (1 / 16 : ℝ))) quantitativeLowDegreePower =
          Real.rpow (9 * Real.sqrt pauliBaselinePointConstant)
              quantitativeLowDegreePower *
            Real.rpow (Real.rpow e (1 / 16 : ℝ))
              quantitativeLowDegreePower := by
        rw [show 9 * (Real.sqrt pauliBaselinePointConstant *
            Real.rpow e (1 / 16 : ℝ)) =
          (9 * Real.sqrt pauliBaselinePointConstant) *
            Real.rpow e (1 / 16 : ℝ) by ring]
        exact Real.mul_rpow (by positivity) (Real.rpow_nonneg he _)
      _ = Real.rpow (9 * Real.sqrt pauliBaselinePointConstant)
              quantitativeLowDegreePower *
            Real.rpow e (quantitativeLowDegreePower / 16) := by
        congr 1
        convert (rpow_rpow_eq (x := e) (a := (1 / 16 : ℝ))
          (b := quantitativeLowDegreePower) he) using 1
        all_goals simp only [Real.rpow_eq_pow]
        all_goals ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        nine_sqrt_point_constant_rpow_le_two (Real.rpow_nonneg he _)
  have hsecond : Real.rpow (9 * Real.sqrt L) quantitativeLowDegreePower ≤
      2 * (Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow e (quantitativeLowDegreePower / 512) +
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow r (quantitativeLowDegreePower / 32)) := by
    let Eroot := Real.rpow e (1 / 512 : ℝ) + Real.rpow r (1 / 32 : ℝ)
    have hmono := Real.rpow_le_rpow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) (Real.sqrt_nonneg L))
      (mul_le_mul_of_nonneg_left hLroot (by norm_num : (0 : ℝ) ≤ 9)) htau0
    have hmSqrtPow : Real.rpow (Real.sqrt (P.m : ℝ)) quantitativeLowDegreePower =
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) := by
      rw [Real.sqrt_eq_rpow]
      convert (rpow_rpow_eq (x := (P.m : ℝ)) (a := (1 / 2 : ℝ))
        (b := quantitativeLowDegreePower) hm0) using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    calc
      Real.rpow (9 * Real.sqrt L) quantitativeLowDegreePower ≤
          Real.rpow
            (9 * (Real.sqrt (P.m : ℝ) *
              Real.sqrt pauliBaselineExtendedLineConstant * Eroot))
            quantitativeLowDegreePower := by
        exact hmono
      _ = Real.rpow
            ((9 * Real.sqrt pauliBaselineExtendedLineConstant) *
              (Real.sqrt (P.m : ℝ) * Eroot)) quantitativeLowDegreePower := by
        congr 1
        ring
      _ = Real.rpow (9 * Real.sqrt pauliBaselineExtendedLineConstant)
              quantitativeLowDegreePower *
            Real.rpow (Real.sqrt (P.m : ℝ) * Eroot)
              quantitativeLowDegreePower :=
        Real.mul_rpow (by positivity) (by dsimp [Eroot]; positivity)
      _ ≤ 2 * Real.rpow (Real.sqrt (P.m : ℝ) *
              Eroot)
              quantitativeLowDegreePower :=
        mul_le_mul_of_nonneg_right nine_sqrt_extended_constant_rpow_le_two
          (Real.rpow_nonneg (by dsimp [Eroot]; positivity) _)
      _ = 2 * (Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
            Real.rpow
              Eroot
              quantitativeLowDegreePower) := by
        have hmul := Real.mul_rpow (x := Real.sqrt (P.m : ℝ)) (y := Eroot)
          (z := quantitativeLowDegreePower) (Real.sqrt_nonneg _)
          (by dsimp [Eroot]; positivity)
        calc
          2 * Real.rpow (Real.sqrt (P.m : ℝ) * Eroot)
              quantitativeLowDegreePower =
              2 * (Real.rpow (Real.sqrt (P.m : ℝ)) quantitativeLowDegreePower *
                Real.rpow Eroot quantitativeLowDegreePower) := congrArg (fun x => 2 * x) hmul
          _ = _ := by rw [hmSqrtPow]
      _ ≤ 2 * (Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          (Real.rpow (Real.rpow e (1 / 512 : ℝ)) quantitativeLowDegreePower +
            Real.rpow (Real.rpow r (1 / 32 : ℝ)) quantitativeLowDegreePower)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (by
              dsimp [Eroot]
              exact Real.rpow_add_le_add_rpow
                (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _) htau0 htau1)
            (Real.rpow_nonneg (by positivity : 0 ≤ (P.m : ℝ)) _))
          (by norm_num)
      _ = _ := by
        have hePow := rpow_rpow_eq (x := e) (a := (1 / 512 : ℝ))
          (b := quantitativeLowDegreePower) he
        have hrPow := rpow_rpow_eq (x := r) (a := (1 / 32 : ℝ))
          (b := quantitativeLowDegreePower) hr
        have hePow' : Real.rpow (Real.rpow e (1 / 512 : ℝ))
            quantitativeLowDegreePower =
            Real.rpow e (quantitativeLowDegreePower / 512) := by
          convert hePow using 1
          all_goals simp only [Real.rpow_eq_pow]
          all_goals ring
        have hrPow' : Real.rpow (Real.rpow r (1 / 32 : ℝ))
            quantitativeLowDegreePower =
            Real.rpow r (quantitativeLowDegreePower / 32) := by
          convert hrPow using 1
          all_goals simp only [Real.rpow_eq_pow]
          all_goals ring
        rw [hePow', hrPow']
        ring
  have hthird : Real.rpow (9 * r) quantitativeLowDegreePower ≤
      2 * Real.rpow r quantitativeLowDegreePower := by
    calc
      Real.rpow (9 * r) quantitativeLowDegreePower =
          Real.rpow 9 quantitativeLowDegreePower *
            Real.rpow r quantitativeLowDegreePower :=
        Real.mul_rpow (by norm_num) hr
      _ ≤ _ := mul_le_mul_of_nonneg_right
        nine_rpow_quantitative_low_degree_power_le_two
        (Real.rpow_nonneg hr _)
  have hrootMono : Real.rpow (9 * Real.sqrt (Q + L)) quantitativeLowDegreePower ≤
      Real.rpow (9 * (Real.sqrt Q + Real.sqrt L)) quantitativeLowDegreePower :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_left hQLroot (by norm_num)) htau0
  have hrootSplit : Real.rpow (9 * (Real.sqrt Q + Real.sqrt L))
      quantitativeLowDegreePower ≤
      Real.rpow (9 * Real.sqrt Q) quantitativeLowDegreePower +
        Real.rpow (9 * Real.sqrt L) quantitativeLowDegreePower := by
    rw [mul_add]
    exact Real.rpow_add_le_add_rpow
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg Q))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg L)) htau0 htau1
  have hfinal :
      Real.rpow (9 * (Real.sqrt (Q + L) + r)) quantitativeLowDegreePower ≤
        2 * (Real.rpow e (quantitativeLowDegreePower / 16) +
          Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
            Real.rpow e (quantitativeLowDegreePower / 512) +
          Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
            Real.rpow r (quantitativeLowDegreePower / 32) +
          Real.rpow r quantitativeLowDegreePower) := by
    calc
      Real.rpow (9 * (Real.sqrt (Q + L) + r)) quantitativeLowDegreePower =
          Real.rpow (9 * Real.sqrt (Q + L) + 9 * r)
            quantitativeLowDegreePower := by congr 1; ring
      _ ≤ Real.rpow (9 * Real.sqrt (Q + L)) quantitativeLowDegreePower +
          Real.rpow (9 * r) quantitativeLowDegreePower :=
        Real.rpow_add_le_add_rpow
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (mul_nonneg (by norm_num) hr) htau0 htau1
      _ ≤ (Real.rpow (9 * Real.sqrt Q) quantitativeLowDegreePower +
            Real.rpow (9 * Real.sqrt L) quantitativeLowDegreePower) +
          Real.rpow (9 * r) quantitativeLowDegreePower :=
        add_le_add (hrootMono.trans hrootSplit) le_rfl
      _ ≤ (2 * Real.rpow e (quantitativeLowDegreePower / 16) +
            2 * (Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
                Real.rpow e (quantitativeLowDegreePower / 512) +
              Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
                Real.rpow r (quantitativeLowDegreePower / 32))) +
          2 * Real.rpow r quantitativeLowDegreePower :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = _ := by ring
  dsimp only [passing, directPassingErrorEnvelope]
  have hbase : 3 * (3 * (Real.sqrt
      (pauliBaselinePointError e + (P.m : ℝ) * pauliBaselineExtendedLineError e r) + r)) =
      9 * (Real.sqrt
        (pauliBaselinePointError e + (P.m : ℝ) * pauliBaselineExtendedLineError e r) + r) := by
    ring
  rw [hbase]
  simpa only [Q, L] using hfinal

/-- Every fractional power of the exact native direct low-degree error is
bounded by the unit-capped six-term expression, with numerical coefficients
kept outside all parameter powers. -/
theorem quantitative_native_error_rpow_le_separated
    (P : AdmissibleParams) (e s : ℝ) (he : 0 ≤ e)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e r) r
    Real.rpow (directNativeError P.extendedDirectLd passing) s ≤
      quantitativeNativeSeparatedError P e s := by
  intro r passing
  let h : ℝ := (2 * P.m + 2 : ℕ)
  let d : ℝ := P.d
  let field : ℝ := d / (P.q : ℝ)
  let passTerm := Real.rpow (3 * passing) quantitativeLowDegreePower
  let tail := Real.exp (-(4 * h * d))
  let raw := 400000 * Real.rpow h (5 / 4 : ℝ) *
    Real.rpow d (1 / 4 : ℝ) * (passTerm + Real.rpow field
      quantitativeLowDegreePower + tail)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hfield : 0 ≤ field := by dsimp [field]; positivity
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hpassTerm : 0 ≤ passTerm := Real.rpow_nonneg (by positivity) _
  have hfieldTerm : 0 ≤ Real.rpow field quantitativeLowDegreePower :=
    Real.rpow_nonneg hfield _
  have htail : 0 ≤ tail := by dsimp [tail]; positivity
  have hraw : 0 ≤ raw := by dsimp [raw]; positivity
  have hlambda0 : 0 ≤ directNativeError P.extendedDirectLd passing :=
    direct_native_error_nonneg _ hpassing
  have hlambdaRaw : directNativeError P.extendedDirectLd passing ≤ raw := by
    unfold directNativeError
    exact min_le_right _ _
  have hpass := quantitative_native_passing_term_le P e he
  have hpass' : passTerm ≤ 2 *
      (Real.rpow e (quantitativeLowDegreePower / 16) +
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow e (quantitativeLowDegreePower / 512) +
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
          Real.rpow r (quantitativeLowDegreePower / 32) +
        Real.rpow r quantitativeLowDegreePower) := by
    simpa only [r, passing] using hpass
  let a := Real.rpow e (quantitativeLowDegreePower / 16)
  let b := Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
    Real.rpow e (quantitativeLowDegreePower / 512)
  let c := Real.rpow (P.m : ℝ) (quantitativeLowDegreePower / 2) *
    Real.rpow r (quantitativeLowDegreePower / 32)
  let z := Real.rpow r quantitativeLowDegreePower
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpassPow : Real.rpow passTerm s ≤
      Real.rpow 2 s * (Real.rpow a s + Real.rpow b s +
        Real.rpow c s + Real.rpow z s) := by
    calc
      Real.rpow passTerm s ≤ Real.rpow (2 * (a + b + c + z)) s :=
        Real.rpow_le_rpow hpassTerm (by simpa only [a, b, c, z] using hpass') hs0
      _ = Real.rpow 2 s * Real.rpow (a + b + c + z) s := by
        exact Real.mul_rpow (by norm_num)
          (add_nonneg (add_nonneg (add_nonneg ha hb) hc) hz)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_add_four_le ha hb hc hz hs0 hs1) (Real.rpow_nonneg (by norm_num) _)
  have haPow : Real.rpow a s =
      Real.rpow e (quantitativeLowDegreePower * s / 16) := by
    dsimp [a]
    convert (rpow_rpow_eq (x := e) (a := quantitativeLowDegreePower / 16)
      (b := s) he) using 1
    all_goals simp only [Real.rpow_eq_pow]
    all_goals ring
  have hbPow : Real.rpow b s =
      Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) *
        Real.rpow e (quantitativeLowDegreePower * s / 512) := by
    dsimp [b]
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg he _)]
    have hmPow := rpow_rpow_eq (x := (P.m : ℝ))
      (a := quantitativeLowDegreePower / 2) (b := s) (by positivity)
    have hePow := rpow_rpow_eq (x := e)
      (a := quantitativeLowDegreePower / 512) (b := s) he
    have hmPow' : Real.rpow (Real.rpow (P.m : ℝ)
        (quantitativeLowDegreePower / 2)) s =
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) := by
      convert hmPow using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    have hePow' : Real.rpow (Real.rpow e (quantitativeLowDegreePower / 512)) s =
        Real.rpow e (quantitativeLowDegreePower * s / 512) := by
      convert hePow using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    simpa only [Real.rpow_eq_pow] using congrArg₂ (· * ·) hmPow' hePow'
  have hcPow : Real.rpow c s =
      Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) *
        Real.rpow r (quantitativeLowDegreePower * s / 32) := by
    dsimp [c]
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hr _)]
    have hmPow := rpow_rpow_eq (x := (P.m : ℝ))
      (a := quantitativeLowDegreePower / 2) (b := s) (by positivity)
    have hrPow := rpow_rpow_eq (x := r)
      (a := quantitativeLowDegreePower / 32) (b := s) hr
    have hmPow' : Real.rpow (Real.rpow (P.m : ℝ)
        (quantitativeLowDegreePower / 2)) s =
        Real.rpow (P.m : ℝ) (quantitativeLowDegreePower * s / 2) := by
      convert hmPow using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    have hrPow' : Real.rpow (Real.rpow r (quantitativeLowDegreePower / 32)) s =
        Real.rpow r (quantitativeLowDegreePower * s / 32) := by
      convert hrPow using 1
      all_goals simp only [Real.rpow_eq_pow]
      all_goals ring
    simpa only [Real.rpow_eq_pow] using congrArg₂ (· * ·) hmPow' hrPow'
  have hzPow : Real.rpow z s =
      Real.rpow r (quantitativeLowDegreePower * s) := by
    dsimp [z]
    simpa only [Real.rpow_eq_pow] using
      (rpow_rpow_eq (x := r) (a := quantitativeLowDegreePower) (b := s) hr)
  have hfieldPow : Real.rpow
      (Real.rpow field quantitativeLowDegreePower) s =
      Real.rpow field (quantitativeLowDegreePower * s) := by
    simpa only [Real.rpow_eq_pow] using
      (rpow_rpow_eq (x := field) (a := quantitativeLowDegreePower) (b := s) hfield)
  have htailPow : Real.rpow tail s = Real.exp (-(4 * h * d * s)) := by
    dsimp [tail]
    rw [← Real.exp_mul]
    congr 1
    ring
  have hsumPow : Real.rpow
      (passTerm + Real.rpow field quantitativeLowDegreePower + tail) s ≤
      Real.rpow passTerm s +
        Real.rpow (Real.rpow field quantitativeLowDegreePower) s +
        Real.rpow tail s := by
    exact (Real.rpow_add_le_add_rpow
      (add_nonneg hpassTerm hfieldTerm) htail hs0 hs1).trans
      (add_le_add (Real.rpow_add_le_add_rpow hpassTerm hfieldTerm hs0 hs1) le_rfl)
  have hrawPow : Real.rpow raw s ≤
      quantitativeNativeSeparatedRaw P e s := by
    calc
      Real.rpow raw s =
          Real.rpow h (5 * s / 4) * Real.rpow d (s / 4) *
            (Real.rpow 400000 s * Real.rpow
              (passTerm + Real.rpow field quantitativeLowDegreePower + tail) s) := by
        dsimp [raw]
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) (Real.rpow_nonneg hh _)]
        have hhPow := rpow_rpow_eq (x := h) (a := (5 / 4 : ℝ)) (b := s) hh
        have hdPow := rpow_rpow_eq (x := d) (a := (1 / 4 : ℝ)) (b := s) hd
        simp only [Real.rpow_eq_pow] at hhPow hdPow ⊢
        rw [hhPow, hdPow]
        ring_nf
      _ ≤ Real.rpow h (5 * s / 4) * Real.rpow d (s / 4) *
          (Real.rpow 400000 s *
            (Real.rpow passTerm s +
              Real.rpow (Real.rpow field quantitativeLowDegreePower) s +
              Real.rpow tail s)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsumPow (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (Real.rpow_nonneg hh _) (Real.rpow_nonneg hd _))
      _ ≤ Real.rpow h (5 * s / 4) * Real.rpow d (s / 4) *
          (Real.rpow 400000 s *
            (Real.rpow 2 s * (Real.rpow a s + Real.rpow b s +
                Real.rpow c s + Real.rpow z s) +
              Real.rpow (Real.rpow field quantitativeLowDegreePower) s +
              Real.rpow tail s)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add hpassPow le_rfl) le_rfl)
            (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (Real.rpow_nonneg hh _) (Real.rpow_nonneg hd _))
      _ = quantitativeNativeSeparatedRaw P e s := by
        rw [haPow, hbPow, hcPow, hzPow, hfieldPow, htailPow]
        dsimp [quantitativeNativeSeparatedRaw, h, d, field, r]
        have hcoefficient : Real.rpow (800000 : ℝ) s =
            Real.rpow 400000 s * Real.rpow 2 s := by
          calc
            Real.rpow (800000 : ℝ) s = Real.rpow (400000 * 2 : ℝ) s := by norm_num
            _ = _ := Real.mul_rpow (by norm_num) (by norm_num)
        simp only [Real.rpow_eq_pow] at hcoefficient ⊢
        rw [hcoefficient]
        ring
  apply le_min
  · calc
      Real.rpow (directNativeError P.extendedDirectLd passing) s ≤
          Real.rpow 1 s := Real.rpow_le_rpow hlambda0 (min_le_left _ _) hs0
      _ = 1 := Real.one_rpow s
  · exact (Real.rpow_le_rpow hlambda0 hlambdaRaw hs0).trans hrawPow

end

end MIPStarRE.QPBT
