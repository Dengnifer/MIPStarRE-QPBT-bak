module

public import MIPStarRE.QPBT.Combining.ActualErrorBounds
public import MIPStarRE.QPBT.Combining.ExplicitScalarBounds
public import MIPStarRE.QPBT.Combining.QuantitativeDirectScalars

/-!
# Baseline quantitative scalar certificates for QPBT

This module records an elementary identity for square roots of real powers and
the three fixed coefficient estimates used in the global-pair scalar bounds.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Elementary real-power identity -/

/-- For a nonnegative base, taking the square root of a real power halves its
exponent. -/
theorem sqrt_rpow_eq {x a : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x a) = Real.rpow x (a / 2) := by
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_mul hx a (1 / 2 : ℝ)).symm.trans (by congr 1; ring)

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
