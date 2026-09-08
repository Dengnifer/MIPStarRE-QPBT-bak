import MIPStarRE.QPBT.Combining.Lines.DiagonalZeroDirectionMass
import MIPStarRE.QPBT.Combining.Lines.ZeroDirectionMass

/-!
# Zero-direction mass for the line-point mixture

This module combines the axis and diagonal zero-direction estimates for the
equal mixture defining the line-point sampler.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`;
the proof-only conditioning context is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:943-963`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Averaging over a convex mixture is linear without requiring the ambient
type to be finite, since each distribution carries an explicit finite support. -/
private theorem avgOver_mix_support {X : Type*} [DecidableEq X]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution X) (f : X → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  have hμ_union :
      (∑ x ∈ μ.support ∪ ν.support, μ.weight x * f x) =
        ∑ x ∈ μ.support, μ.weight x * f x := by
    symm
    exact Finset.sum_subset Finset.subset_union_left fun x _ hx => by
      rw [μ.outsideSupport x hx, zero_mul]
  have hν_union :
      (∑ x ∈ μ.support ∪ ν.support, ν.weight x * f x) =
        ∑ x ∈ ν.support, ν.weight x * f x := by
    symm
    exact Finset.sum_subset Finset.subset_union_right fun x _ hx => by
      rw [ν.outsideSupport x hx, zero_mul]
  simp only [avgOver, Distribution.mix, add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hμ_union, hν_union]

/-- The equal mixture of axis and diagonal line-point laws gives zero directions
mass at most `1 / (2q)`. This formalization-only estimate preserves the source
sampler, including its degenerate fibers. -/
theorem linePointDist_zero_direction_mass_le (L : LdParams) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
  rw [linePointDist, avgOver_mix_support, aLinePointDist_zero_direction_mass]
  have hdiag := dLinePointDist_zero_direction_mass_le L
  calc
    _ = (1 / 2 : ℝ) * avgOver (dLinePointDist L)
        (fun sample => if sample.1.direction = 0 then 1 else 0) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 / Fintype.card (ScalarQ L)) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ = _ := by rw [one_div_mul_one_div]

end

end MIPStarRE.QPBT
