import MIPStarRE.QPBT.Combining.ErrorBounds
import MIPStarRE.QPBT.Combining.PassingError
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error
import MIPStarRE.QPBT.ExplicitConstants
import MIPStarRE.QPBT.Games.Sandwich.Pasting.Heterogeneous

/-!
# Explicit scalar bounds for the QPBT baseline

This module instantiates the scalar absorption arguments in the current QPBT
proof with closed numerical witnesses.  The results are Lean-only quantitative
auxiliaries for the source lemmas `lem:qld-xz-lines`, `lem:qld-4-13`, and
`lem:qld-4-7`.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,
1134-1404`.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- The combined-point coefficient is at least one. -/
theorem one_le_pauli_baseline_point_constant :
    1 ≤ pauliBaselinePointConstant := by
  unfold pauliBaselinePointConstant pauliBaselineTwistedConstant
    pauliBaselineCommutatorConstant
  nlinarith [Real.sqrt_nonneg (344 : ℝ)]

/-- The fixed combined-point error has its displayed polynomial bound. -/
theorem pauli_baseline_point_error_is_poly_err : IsPolyErr pauliBaselinePointError := by
  exact ⟨pauliBaselinePointConstant, 1 / 8, one_le_pauli_baseline_point_constant,
    by norm_num, fun error herror =>
      ⟨mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_point_constant)
        (Real.rpow_nonneg herror _), le_rfl⟩⟩

/-- The combined-line coefficient is at least one. -/
theorem one_le_pauli_baseline_line_constant :
    1 ≤ pauliBaselineLineConstant := by
  unfold pauliBaselineLineConstant
  change 1 ≤ 115 *
    (1 + Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ)) + 1
  have hbase : 0 ≤ 16 * pauliBaselinePointConstant + 8320 := by
    nlinarith [one_le_pauli_baseline_point_constant]
  have hterm : 0 ≤ 115 *
      (1 + Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ)) :=
    mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (Real.rpow_nonneg hbase (1 / 8 : ℝ)))
  linarith

/-- The fixed combined-line error has its displayed polynomial bound. -/
theorem pauli_baseline_line_error_is_poly_err₂ : IsPolyErr₂ pauliBaselineLineError := by
  exact ⟨pauliBaselineLineConstant, 1 / 64, 1 / 4,
    one_le_pauli_baseline_line_constant, by norm_num, by norm_num,
    fun error ratio herror hratio =>
      ⟨mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_line_constant)
        (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _)), le_rfl⟩⟩

/-- The conditioned-pasting scalar expression is bounded by the fixed line
error `L * (ε^(1/64) + ratio^(1/4))`.  This is the numerical specialization
used in the current proof of paper `lem:qld-xz-lines`. -/
theorem pauli_baseline_conditioned_line_bound
    (error ratio mass : ℝ) (herror : 0 ≤ error) (hratio : 0 ≤ ratio)
    (hmass : 1 / 2 ≤ mass) (hmassOne : mass ≤ 1) :
    min 1 (mass * heterogeneousPastingError ratio
      ((8 * pauliBaselinePointError error +
        2080 * (error + Real.sqrt error)) / mass) + ratio) ≤
      pauliBaselineLineError error ratio := by
  have hmassPos : 0 < mass := by linarith
  have hpointNonneg : 0 ≤ pauliBaselinePointError error := by
    unfold pauliBaselinePointError
    exact mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg herror _)
  have herrorTerm : 0 ≤ Real.rpow error (1 / 64 : ℝ) := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ Real.rpow ratio (1 / 4 : ℝ) := Real.rpow_nonneg hratio _
  have hlarge (hlarge : 1 ≤ Real.rpow error (1 / 64 : ℝ) +
      Real.rpow ratio (1 / 4 : ℝ)) :
      min 1 (mass * heterogeneousPastingError ratio
        ((8 * pauliBaselinePointError error +
          2080 * (error + Real.sqrt error)) / mass) + ratio) ≤
        pauliBaselineLineError error ratio := by
    refine (min_le_left _ _).trans ?_
    unfold pauliBaselineLineError
    change 1 ≤ pauliBaselineLineConstant *
      (Real.rpow error (1 / 64 : ℝ) + Real.rpow ratio (1 / 4 : ℝ))
    exact hlarge.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right one_le_pauli_baseline_line_constant
          (add_nonneg herrorTerm hratioTerm))
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have herrorSmall : error ≤ Real.rpow error (1 / 8 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' herror herrorOne
          (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
      have hsqrtSmall : Real.sqrt error ≤ Real.rpow error (1 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge' herror herrorOne
          (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
      have hmarginalNonneg : 0 ≤ 8 * pauliBaselinePointError error +
          2080 * (error + Real.sqrt error) :=
        add_nonneg (mul_nonneg (by norm_num) hpointNonneg)
          (mul_nonneg (by norm_num) (add_nonneg herror (Real.sqrt_nonneg _)))
      have hmarginalSmall : 8 * pauliBaselinePointError error +
          2080 * (error + Real.sqrt error) ≤
          (8 * pauliBaselinePointConstant + 4160) *
            Real.rpow error (1 / 8 : ℝ) := by
        unfold pauliBaselinePointError
        calc
          _ ≤ 8 * (pauliBaselinePointConstant * Real.rpow error (1 / 8 : ℝ)) +
              2080 * (Real.rpow error (1 / 8 : ℝ) +
                Real.rpow error (1 / 8 : ℝ)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (add_le_add herrorSmall hsqrtSmall) (by norm_num))
          _ = _ := by ring
      have hmarginalConstant :
          0 ≤ 8 * pauliBaselinePointConstant + 4160 := by
        nlinarith [one_le_pauli_baseline_point_constant]
      have hdivSmall : (8 * pauliBaselinePointError error +
          2080 * (error + Real.sqrt error)) / mass ≤
          (16 * pauliBaselinePointConstant + 8320) *
            Real.rpow error (1 / 8 : ℝ) := by
        apply (div_le_iff₀ hmassPos).mpr
        calc
          _ ≤ (8 * pauliBaselinePointConstant + 4160) *
              Real.rpow error (1 / 8 : ℝ) := hmarginalSmall
          _ ≤ (16 * pauliBaselinePointConstant + 8320) *
              Real.rpow error (1 / 8 : ℝ) * mass := by
            have hterm : 0 ≤ (8 * pauliBaselinePointConstant + 4160) *
                Real.rpow error (1 / 8 : ℝ) :=
              mul_nonneg hmarginalConstant (Real.rpow_nonneg herror _)
            nlinarith [mul_nonneg (show 0 ≤ mass - 1 / 2 by linarith) hterm]
      have hpowerConstant : 0 ≤
          Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) := by
        apply Real.rpow_nonneg
        nlinarith [one_le_pauli_baseline_point_constant]
      have hbaseConstant : 0 ≤ 16 * pauliBaselinePointConstant + 8320 := by
        nlinarith [one_le_pauli_baseline_point_constant]
      have hdivPower : Real.rpow ((8 * pauliBaselinePointError error +
          2080 * (error + Real.sqrt error)) / mass) (1 / 8 : ℝ) ≤
          Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) *
            Real.rpow error (1 / 64 : ℝ) := by
        calc
          _ ≤ Real.rpow ((16 * pauliBaselinePointConstant + 8320) *
              Real.rpow error (1 / 8 : ℝ)) (1 / 8 : ℝ) :=
            Real.rpow_le_rpow (div_nonneg hmarginalNonneg hmassPos.le)
              hdivSmall (by norm_num)
          _ = _ := by
            simp only [Real.rpow_eq_pow]
            rw [Real.mul_rpow hbaseConstant (Real.rpow_nonneg herror _),
              ← Real.rpow_mul herror]
            norm_num
      have hratioLinear : ratio ≤ Real.rpow ratio (1 / 4 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
      have hpastingNonneg : 0 ≤ heterogeneousPastingError ratio
          ((8 * pauliBaselinePointError error +
            2080 * (error + Real.sqrt error)) / mass) := by
        unfold heterogeneousPastingError
        positivity
      refine (min_le_right _ _).trans ?_
      calc
        _ ≤ heterogeneousPastingError ratio
              ((8 * pauliBaselinePointError error +
                2080 * (error + Real.sqrt error)) / mass) + ratio :=
          add_le_add (mul_le_of_le_one_left hpastingNonneg hmassOne) le_rfl
        _ ≤ 115 * (Real.rpow ratio (1 / 4 : ℝ) +
              Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) *
                Real.rpow error (1 / 64 : ℝ)) +
              Real.rpow ratio (1 / 4 : ℝ) := by
          unfold heterogeneousPastingError
          exact add_le_add (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hdivPower) (by norm_num)) hratioLinear
        _ ≤ pauliBaselineLineError error ratio := by
          unfold pauliBaselineLineError pauliBaselineLineConstant
          have hremaining : 0 ≤ 116 * Real.rpow error (1 / 64 : ℝ) +
              115 * Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) *
                Real.rpow ratio (1 / 4 : ℝ) :=
            add_nonneg (mul_nonneg (by norm_num) herrorTerm)
              (mul_nonneg (mul_nonneg (by norm_num) hpowerConstant) hratioTerm)
          calc
            _ = 116 * Real.rpow ratio (1 / 4 : ℝ) +
                115 * Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ) *
                  Real.rpow error (1 / 64 : ℝ) := by ring
            _ ≤ (116 + 115 *
                  Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ)) *
                (Real.rpow error (1 / 64 : ℝ) +
                  Real.rpow ratio (1 / 4 : ℝ)) := by
              nlinarith
            _ = _ := by ring
    · apply hlarge
      exact (Real.one_le_rpow (le_of_not_ge hratioOne)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans
          (le_add_of_nonneg_left herrorTerm)
  · apply hlarge
    exact (Real.one_le_rpow (le_of_not_ge herrorOne)
      (by norm_num : (0 : ℝ) ≤ 1 / 64)).trans
        (le_add_of_nonneg_right hratioTerm)

/-- The extended-line coefficient is at least one. -/
theorem one_le_pauli_baseline_extended_line_constant :
    1 ≤ pauliBaselineExtendedLineConstant := by
  unfold pauliBaselineExtendedLineConstant
  have hpoint : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hline : 0 ≤ pauliBaselineLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_line_constant
  have hsum : 0 ≤ Real.sqrt pauliBaselinePointConstant +
      Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
      Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1 := by
    exact add_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hline _)) (Real.rpow_nonneg hpoint _)) zero_le_one
  nlinarith

/-- The fixed extended-line error has its displayed polynomial bound. -/
theorem pauli_baseline_extended_line_error_is_poly_err₂ :
    IsPolyErr₂ pauliBaselineExtendedLineError := by
  exact ⟨pauliBaselineExtendedLineConstant, 1 / 256, 1 / 16,
    one_le_pauli_baseline_extended_line_constant, by norm_num, by norm_num,
    fun error ratio herror hratio =>
      ⟨mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_extended_line_constant)
        (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _)), le_rfl⟩⟩

/-- The first-route paired-overlap expression is bounded by the fixed
extended-line error. This is the closed numerical specialization of the
scalar calculation supporting paper `lem:qld-4-13`, lines 1134--1246, for
issue #729. -/
theorem pauli_baseline_combining_bound
    (error ratio dimension : ℝ) (herror : 0 ≤ error) (hratio : 0 ≤ ratio)
    (hdimension : 1 ≤ dimension) :
    min 1 (6 * (Real.rpow (pauliBaselinePointError error) (1 / 2 : ℝ) +
      Real.sqrt dimension *
        (Real.rpow (pauliBaselineLineError error ratio) (1 / 4 : ℝ) +
          Real.rpow (pauliBaselinePointError error) (1 / 4 : ℝ) +
          Real.rpow error (1 / 4 : ℝ)))) ≤
      dimension * pauliBaselineExtendedLineError error ratio := by
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have herrorTerm : 0 ≤ Real.rpow error (1 / 256 : ℝ) := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ Real.rpow ratio (1 / 16 : ℝ) := Real.rpow_nonneg hratio _
  have hpointConstant : 0 ≤ pauliBaselinePointConstant :=
    le_trans zero_le_one one_le_pauli_baseline_point_constant
  have hlineConstant : 0 ≤ pauliBaselineLineConstant :=
    le_trans zero_le_one one_le_pauli_baseline_line_constant
  have hcoefficient : 0 ≤ Real.sqrt pauliBaselinePointConstant +
      Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
      Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1 := by
    exact add_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hlineConstant _)) (Real.rpow_nonneg hpointConstant _)) zero_le_one
  by_cases herrorOne : error ≤ 1
  · have hpointNonneg : 0 ≤ pauliBaselinePointError error := by
      unfold pauliBaselinePointError
      exact mul_nonneg hpointConstant (Real.rpow_nonneg herror _)
    have hlineNonneg : 0 ≤ pauliBaselineLineError error ratio := by
      unfold pauliBaselineLineError
      exact mul_nonneg hlineConstant
        (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _))
    have hpointRoot (power : ℝ) (hpower : 0 ≤ power)
        (hsmall : (1 / 256 : ℝ) ≤ (1 / 8 : ℝ) * power) :
        Real.rpow (pauliBaselinePointError error) power ≤
          Real.rpow pauliBaselinePointConstant power *
            Real.rpow error (1 / 256 : ℝ) := by
      unfold pauliBaselinePointError
      calc
        _ = Real.rpow pauliBaselinePointConstant power *
            Real.rpow (Real.rpow error (1 / 8 : ℝ)) power := by
          simp only [Real.rpow_eq_pow]
          rw [Real.mul_rpow hpointConstant (Real.rpow_nonneg herror _)]
        _ = Real.rpow pauliBaselinePointConstant power *
            Real.rpow error ((1 / 8 : ℝ) * power) := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_mul herror]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne
            (by norm_num) hsmall)
          (Real.rpow_nonneg hpointConstant _)
    have hpointQuarter := hpointRoot (1 / 4) (by norm_num) (by norm_num)
    have hpointHalf := hpointRoot (1 / 2) (by norm_num) (by norm_num)
    have hlineQuarter :
        Real.rpow (pauliBaselineLineError error ratio) (1 / 4 : ℝ) ≤
          Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
            (Real.rpow error (1 / 256 : ℝ) +
              Real.rpow ratio (1 / 16 : ℝ)) := by
      unfold pauliBaselineLineError
      calc
        _ = Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
            Real.rpow (Real.rpow error (1 / 64 : ℝ) +
              Real.rpow ratio (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.mul_rpow hlineConstant (by positivity)]
        _ ≤ Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
            (Real.rpow (Real.rpow error (1 / 64 : ℝ)) (1 / 4 : ℝ) +
              Real.rpow (Real.rpow ratio (1 / 4 : ℝ)) (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror _)
              (Real.rpow_nonneg hratio _) (by norm_num) (by norm_num))
            (Real.rpow_nonneg hlineConstant _)
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_mul herror, ← Real.rpow_mul hratio]
          norm_num
    have herrorQuarter : Real.rpow error (1 / 4 : ℝ) ≤
        Real.rpow error (1 / 256 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne (by norm_num) (by norm_num)
    have hsqrt : Real.sqrt dimension ≤ dimension := by
      nlinarith [Real.sq_sqrt hdimensionNonneg, Real.sqrt_nonneg dimension]
    have hrootNonneg : 0 ≤
        Real.rpow (pauliBaselineLineError error ratio) (1 / 4 : ℝ) +
          Real.rpow (pauliBaselinePointError error) (1 / 4 : ℝ) +
          Real.rpow error (1 / 4 : ℝ) := by
      exact add_nonneg (add_nonneg (Real.rpow_nonneg hlineNonneg _)
        (Real.rpow_nonneg hpointNonneg _)) (Real.rpow_nonneg herror _)
    have hrootSum := add_le_add (add_le_add hlineQuarter hpointQuarter) herrorQuarter
    have hscaled := mul_le_mul hsqrt hrootSum hrootNonneg hdimensionNonneg
    have hpointScaled : Real.rpow (pauliBaselinePointError error) (1 / 2 : ℝ) ≤
        dimension * (Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) *
          Real.rpow error (1 / 256 : ℝ)) := by
      exact hpointHalf.trans (le_mul_of_one_le_left
        (mul_nonneg (Real.rpow_nonneg hpointConstant _) herrorTerm) hdimension)
    have hsum : Real.rpow (pauliBaselinePointError error) (1 / 2 : ℝ) +
        Real.sqrt dimension *
          (Real.rpow (pauliBaselineLineError error ratio) (1 / 4 : ℝ) +
            Real.rpow (pauliBaselinePointError error) (1 / 4 : ℝ) +
            Real.rpow error (1 / 4 : ℝ)) ≤
        dimension * ((Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) +
          Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
          Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1) *
            (Real.rpow error (1 / 256 : ℝ) +
              Real.rpow ratio (1 / 16 : ℝ))) := by
      calc
        _ ≤ dimension * (Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) *
              Real.rpow error (1 / 256 : ℝ)) +
            dimension *
              (Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
                  (Real.rpow error (1 / 256 : ℝ) +
                    Real.rpow ratio (1 / 16 : ℝ)) +
                Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) *
                  Real.rpow error (1 / 256 : ℝ) +
                Real.rpow error (1 / 256 : ℝ)) := add_le_add hpointScaled hscaled
        _ = dimension * (Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) *
              Real.rpow error (1 / 256 : ℝ) +
            Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
              (Real.rpow error (1 / 256 : ℝ) +
                Real.rpow ratio (1 / 16 : ℝ)) +
            Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) *
              Real.rpow error (1 / 256 : ℝ) +
            Real.rpow error (1 / 256 : ℝ)) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hdimensionNonneg
          rw [show
            (Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) +
                Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
                Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1) *
                (Real.rpow error (1 / 256 : ℝ) +
                  Real.rpow ratio (1 / 16 : ℝ)) =
              Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) *
                  Real.rpow error (1 / 256 : ℝ) +
                Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) *
                  (Real.rpow error (1 / 256 : ℝ) +
                    Real.rpow ratio (1 / 16 : ℝ)) +
                Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) *
                  Real.rpow error (1 / 256 : ℝ) +
                Real.rpow error (1 / 256 : ℝ) +
                (Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) *
                    Real.rpow ratio (1 / 16 : ℝ) +
                  Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) *
                    Real.rpow ratio (1 / 16 : ℝ) +
                  Real.rpow ratio (1 / 16 : ℝ)) by ring]
          exact le_add_of_nonneg_right (add_nonneg
            (add_nonneg
              (mul_nonneg (Real.rpow_nonneg hpointConstant (1 / 2 : ℝ)) hratioTerm)
              (mul_nonneg (Real.rpow_nonneg hpointConstant (1 / 4 : ℝ)) hratioTerm))
            hratioTerm)
    refine (min_le_right _ _).trans ?_
    unfold pauliBaselineExtendedLineError pauliBaselineExtendedLineConstant
    have hsqrtPoint : Real.sqrt pauliBaselinePointConstant =
        Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) := by
      simpa only [Real.rpow_eq_pow] using Real.sqrt_eq_rpow pauliBaselinePointConstant
    rw [hsqrtPoint]
    calc
      _ ≤ 6 * (dimension *
          ((Real.rpow pauliBaselinePointConstant (1 / 2 : ℝ) +
            Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
            Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1) *
              (Real.rpow error (1 / 256 : ℝ) +
                Real.rpow ratio (1 / 16 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ _ := by
        have hnonneg : 0 ≤ dimension *
            (Real.rpow error (1 / 256 : ℝ) + Real.rpow ratio (1 / 16 : ℝ)) :=
          mul_nonneg hdimensionNonneg (add_nonneg herrorTerm hratioTerm)
        nlinarith
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge herrorOne)
      (by norm_num : (0 : ℝ) ≤ 1 / 256)
    have hsumOne : 1 ≤ pauliBaselineExtendedLineConstant *
        (Real.rpow error (1 / 256 : ℝ) + Real.rpow ratio (1 / 16 : ℝ)) := by
      exact one_le_mul_of_one_le_of_one_le one_le_pauli_baseline_extended_line_constant
        (hone.trans (le_add_of_nonneg_right hratioTerm))
    unfold pauliBaselineExtendedLineError
    exact one_le_mul_of_one_le_of_one_le hdimension hsumOne

/-- The direct passing-error coefficient is at least one. -/
theorem one_le_pauli_baseline_passing_constant :
    1 ≤ pauliBaselinePassingConstant := by
  unfold pauliBaselinePassingConstant
  nlinarith [Real.sqrt_nonneg
    (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant)]

/-- The fixed direct passing error has its displayed polynomial bound. -/
theorem pauli_baseline_passing_error_is_poly_err₂ :
    IsPolyErr₂ pauliBaselinePassingError := by
  exact ⟨pauliBaselinePassingConstant, 1 / 512, 1 / 32,
    one_le_pauli_baseline_passing_constant, by norm_num, by norm_num,
    fun error ratio herror hratio =>
      ⟨mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_passing_constant)
        (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _)), le_rfl⟩⟩

/-- The capped direct-game passing error is bounded by the fixed baseline
error. This is the closed specialization of the scalar calculation at paper
`lem:qld-4-7`, lines 1279--1288, for issue #729. -/
theorem pauli_baseline_direct_passing_bound
    (error ratio dimension : ℝ) (herror : 0 ≤ error) (hratio : 0 ≤ ratio)
    (hdimension : 1 ≤ dimension) :
    min 1 (directPassingErrorEnvelope
      (pauliBaselinePointError error +
        dimension * pauliBaselineExtendedLineError error ratio) ratio) ≤
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
  have hlarge (h : 1 ≤ Real.rpow error (1 / 512 : ℝ) +
      Real.rpow ratio (1 / 32 : ℝ)) :
      min 1 (directPassingErrorEnvelope
        (pauliBaselinePointError error +
          dimension * pauliBaselineExtendedLineError error ratio) ratio) ≤
        dimension * pauliBaselinePassingError error ratio := by
    refine (min_le_left _ _).trans ?_
    unfold pauliBaselinePassingError
    exact one_le_mul_of_one_le_of_one_le hdimension
      (one_le_mul_of_one_le_of_one_le one_le_pauli_baseline_passing_constant h)
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointBound : pauliBaselinePointError error ≤
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
              Real.sqrt (pauliBaselinePointConstant +
                pauliBaselineExtendedLineConstant) *
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
      refine (min_le_right _ _).trans ?_
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
              dimension * pauliBaselineExtendedLineError error ratio) +
              3 * ratio := by ring
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
    · apply hlarge
      exact (Real.one_le_rpow (le_of_not_ge hratioOne)
        (by norm_num : (0 : ℝ) ≤ 1 / 32)).trans (le_add_of_nonneg_left he)
  · apply hlarge
    exact (Real.one_le_rpow (le_of_not_ge herrorOne)
      (by norm_num : (0 : ℝ) ≤ 1 / 512)).trans (le_add_of_nonneg_right hy)

/-- The global scalar absorption calculation at the displayed baseline
coefficient and pre-rounding power. This is the closed numerical specialization
of the calculation supporting paper `lem:qld-4-7`, lines 1278--1288 and 1402,
for issue #729. -/
theorem pauli_baseline_global_absorption_bound :
    1 < pauliBaselineGlobalAbsorptionConstant ∧
      0 < pauliBaselineGlobalAbsorptionPower ∧
      pauliBaselineGlobalAbsorptionPower < 1 ∧
      ∀ (P : AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (2 *
          (deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
              ((P.m : ℝ) * pauliBaselinePassingError error
                (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) + error)
              P.q (2 * P.m + 2) P.d 1 +
            Real.sqrt (pauliBaselinePointError error) +
              ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))) ≤
          deltaQld pauliBaselineGlobalAbsorptionConstant
            pauliBaselineGlobalAbsorptionPower error P.m P.d P.q := by
  have hpointBound : ∀ error : ℝ, 0 ≤ error →
      0 ≤ pauliBaselinePointError error ∧
        pauliBaselinePointError error ≤
          pauliBaselinePointConstant * error ^ (1 / 8 : ℝ) := by
    intro error herror
    exact ⟨mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg herror _), by
        unfold pauliBaselinePointError
        rfl⟩
  have hpassingBound : ∀ error ratio : ℝ, 0 ≤ error → 0 ≤ ratio →
      0 ≤ pauliBaselinePassingError error ratio ∧
        pauliBaselinePassingError error ratio ≤
          pauliBaselinePassingConstant *
            (error ^ (1 / 512 : ℝ) + ratio ^ (1 / 32 : ℝ)) := by
    intro error ratio herror hratio
    exact ⟨mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_passing_constant)
      (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _)), by
        unfold pauliBaselinePassingError
        rfl⟩
  obtain ⟨hA, hB, hB1, hbound⟩ := global_pair_error_bound_explicit
    pauliBaselinePointError pauliBaselinePointConstant (1 / 8)
    one_le_pauli_baseline_point_constant (by norm_num) hpointBound
    pauliBaselinePassingError pauliBaselinePassingConstant (1 / 512) (1 / 32)
    one_le_pauli_baseline_passing_constant (by norm_num) (by norm_num) hpassingBound
    1 pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower 2
    (by norm_num) (by unfold pauliBaselineLowDegreeConstant; norm_num)
    (by unfold pauliBaselineLowDegreePower; norm_num)
    (by unfold pauliBaselineLowDegreePower; norm_num) (by norm_num)
  have hconstant : globalPairBoundConstant pauliBaselinePointConstant
      pauliBaselinePassingConstant 1 pauliBaselineLowDegreeConstant
      pauliBaselineLowDegreePower (1 / 32) 2 =
        pauliBaselineGlobalAbsorptionConstant := by
    unfold globalPairBoundConstant pauliBaselineGlobalAbsorptionConstant
    simp only [one_mul, Real.rpow_eq_pow]
    ring
  have hpower : globalPairBoundPower (1 / 8) (1 / 512) (1 / 32)
      pauliBaselineLowDegreePower = pauliBaselineGlobalAbsorptionPower := by
    unfold globalPairBoundPower pauliBaselineLowDegreePower
      pauliBaselineGlobalAbsorptionPower
    norm_num
  rw [hconstant] at hA hbound
  rw [hpower] at hB hB1 hbound
  refine ⟨hA, hB, hB1, ?_⟩
  intro P error herror
  simpa only [one_mul] using hbound P error herror

/-- The full direct-game passing envelope, including its positive slack, is
absorbed at the fixed pre-rounding baseline. This specializes the cap argument
supporting paper `lem:qld-4-7`, lines 1278--1288 and 1402, for issue #729. -/
theorem pauli_baseline_direct_global_pair_error_bound
    (P : AdmissibleParams) (error : ℝ) (herror : 0 ≤ error) :
    min 1
        (deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
            (directPassingErrorEnvelope
                (pauliBaselinePointError error + (P.m : ℝ) *
                  pauliBaselineExtendedLineError error
                    (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
                (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) + error)
            P.q (2 * P.m + 2) P.d 1 +
          Real.sqrt (pauliBaselinePointError error) +
            ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) ≤
      deltaQld pauliBaselineGlobalAbsorptionConstant
        pauliBaselineGlobalAbsorptionPower error P.m P.d P.q := by
  obtain ⟨hA, hB, hB1, habs⟩ := pauli_baseline_global_absorption_bound
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
  let passing := directPassingErrorEnvelope
    (pauliBaselinePointError error + (P.m : ℝ) *
      pauliBaselineExtendedLineError error ratio) ratio
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hpass := pauli_baseline_direct_passing_bound error ratio (P.m : ℝ)
    herror hratio hm
  have hbound := habs P error herror
  change min 1 (2 *
    (deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
        ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
        P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pauliBaselinePointError error) + ratio)) ≤ _ at hbound
  change min 1
    (deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
        (passing + error) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pauliBaselinePointError error) + ratio) ≤ _
  by_cases hsmall : passing ≤ 1
  · rw [min_eq_right hsmall] at hpass
    have hld : deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
        (passing + error) P.q (2 * P.m + 2) P.d 1 ≤
        deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
          ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
          P.q (2 * P.m + 2) P.d 1 := by
      unfold deltaLd
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (by unfold pauliBaselineLowDegreeConstant; norm_num)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      refine add_le_add (add_le_add ?_ le_rfl) le_rfl
      exact Real.rpow_le_rpow (add_nonneg hpassing herror)
        (add_le_add hpass le_rfl)
        (by unfold pauliBaselineLowDegreePower; norm_num)
    have hsumNonneg : 0 ≤
        deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
            ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
            P.q (2 * P.m + 2) P.d 1 +
          Real.sqrt (pauliBaselinePointError error) + ratio := by
      have hpassingError : 0 ≤ pauliBaselinePassingError error ratio := by
        unfold pauliBaselinePassingError
        exact mul_nonneg (le_trans zero_le_one one_le_pauli_baseline_passing_constant)
          (add_nonneg (Real.rpow_nonneg herror _) (Real.rpow_nonneg hratio _))
      have hinputNonneg : 0 ≤
          (P.m : ℝ) * pauliBaselinePassingError error ratio + error :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg _) hpassingError) herror
      have hdeltaNonneg : 0 ≤
          deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
            ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
            P.q (2 * P.m + 2) P.d 1 := by
        unfold deltaLd
        exact mul_nonneg
          (mul_nonneg (by unfold pauliBaselineLowDegreeConstant; norm_num)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (add_nonneg (add_nonneg (Real.rpow_nonneg hinputNonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
            (Real.rpow_nonneg (by norm_num) _))
      exact add_nonneg (add_nonneg hdeltaNonneg
        (Real.sqrt_nonneg (pauliBaselinePointError error))) hratio
    refine le_trans (min_le_min_left 1 ?_) hbound
    nlinarith
  · rw [min_eq_left (le_of_not_ge hsmall)] at hpass
    have hinput : 1 ≤ (P.m : ℝ) * pauliBaselinePassingError error ratio + error := by
      linarith
    have hld : 1 ≤ deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
        ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
        P.q (2 * P.m + 2) P.d 1 :=
      one_le_deltaLd_of_one_le_error
        (by unfold pauliBaselineLowDegreeConstant; norm_num)
        (by unfold pauliBaselineLowDegreePower; norm_num) hinput (by omega) P.hd le_rfl
    have hsum : 1 ≤
        deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower
            ((P.m : ℝ) * pauliBaselinePassingError error ratio + error)
            P.q (2 * P.m + 2) P.d 1 +
          Real.sqrt (pauliBaselinePointError error) + ratio := by
      linarith [Real.sqrt_nonneg (pauliBaselinePointError error)]
    rw [min_eq_left (one_le_mul_of_one_le_of_one_le (by norm_num) hsum)] at hbound
    exact (min_le_left _ _).trans hbound

end

end MIPStarRE.QPBT
