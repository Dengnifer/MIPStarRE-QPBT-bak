import MIPStarRE.LDT.Basic.ParametersBase

/-! # Polynomial error predicates -/

namespace MIPStarRE.QPBT

/-- `IsPolyErr f` means that `f` is a polynomially bounded error function. -/
def IsPolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ ∀ x, |f x| ≤ C * (1 + |x|) ^ r

/-- Two-parameter version of the polynomial error predicate. -/
def IsPolyErr2 (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C r s : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ 0 ≤ s ∧
    ∀ x y, |f x y| ≤ C * (1 + |x|) ^ r * (1 + |y|) ^ s

abbrev IsPolyErr₂ := IsPolyErr2

end MIPStarRE.QPBT
