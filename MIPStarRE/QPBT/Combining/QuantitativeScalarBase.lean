import MIPStarRE.QPBT.Combining.ActualErrorBounds
import MIPStarRE.QPBT.Combining.ExplicitScalarBounds
import MIPStarRE.QPBT.Combining.QuantitativeDirectScalars

/-!
# Baseline quantitative scalar certificates for QPBT

This module records the three fixed coefficient estimates needed by both the
native-power calculation and the legacy global-pair scalar bounds.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

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

end

end MIPStarRE.QPBT
