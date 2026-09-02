import MIPStarRE.LDT.Basic.Distribution

/-! # Finite distribution combinators -/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Product of two finite distributions, with multiplicative weights. -/
noncomputable def Distribution.prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) : Distribution (α × β) where
  support := μ.support.product ν.support
  weight p := μ.weight p.1 * ν.weight p.2
  nonnegative p := mul_nonneg (μ.nonnegative p.1) (ν.nonnegative p.2)
  outsideSupport p hp := by
    by_cases hμ : p.1 ∈ μ.support
    · have hν : p.2 ∉ ν.support := by
        intro h
        exact hp (Finset.mem_product.mpr ⟨hμ, h⟩)
      simp [ν.outsideSupport p.2 hν]
    · simp [μ.outsideSupport p.1 hμ]

/-- Convex mixture of two finite distributions. -/
noncomputable def Distribution.mix {α : Type*} [DecidableEq α]
    (t : ℝ) (μ ν : Distribution α) : Distribution α where
  support := μ.support ∪ ν.support
  weight a := |t| * μ.weight a + |1 - t| * ν.weight a
  nonnegative a := by
    exact add_nonneg (mul_nonneg (abs_nonneg _) (μ.nonnegative a))
      (mul_nonneg (abs_nonneg _) (ν.nonnegative a))
  outsideSupport a ha := by
    have hμ : a ∉ μ.support := fun h => ha (Finset.mem_union_left _ h)
    have hν : a ∉ ν.support := fun h => ha (Finset.mem_union_right _ h)
    simp [μ.outsideSupport a hμ, ν.outsideSupport a hν]

/-- A dependent finite bind over a distribution-valued family. -/
noncomputable def Distribution.bind {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) : Distribution β where
  support := μ.support.biUnion (fun a => (ν a).support)
  weight b := ∑ a ∈ μ.support, μ.weight a * (ν a).weight b
  nonnegative b := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonnegative a) ((ν a).nonnegative b)
  outsideSupport b hb := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : b ∉ (ν a).support := by
      intro h
      exact hb (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
    simp [ν a |>.outsideSupport b hnot]

end MIPStarRE.QPBT
