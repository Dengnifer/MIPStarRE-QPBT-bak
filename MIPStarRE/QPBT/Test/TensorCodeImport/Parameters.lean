import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Auxiliary sampling parameter for the tensor-code import

The printed value `m^3 * d` does not always satisfy the lower bound in the
cited tensor-code theorem. This module verifies scalar estimates for the
proposed maximum of that value and the required lower bound. It does not
change a game or apply an unformalized soundness theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-454`
- Ji et al., arXiv:2111.08131v3, Theorem 4.7 (`thm:main-bipartite`).
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

/-- Candidate auxiliary parameter for Theorem 4.7. This is the least value
at least the printed `m^3 * d` and the required `12 * m * (d + 1)`. Its
adoption in the source import is separate from the scalar facts proved here. -/
def samplingCount (m d : ℕ) : ℕ := max (m ^ 3 * d) (12 * m * (d + 1))

/-- For all positive dimensions and degrees, the candidate satisfies the
tensor-code theorem's precondition, dominates the printed parameter, and
increases it by at most a universal factor of 24. -/
theorem sampling_bounds (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    12 * m * (d + 1) ≤ samplingCount m d ∧
      m ^ 3 * d ≤ samplingCount m d ∧
      samplingCount m d ≤ 24 * m ^ 3 * d := by
  refine ⟨Nat.le_max_right _ _, Nat.le_max_left _ _, max_le ?_ ?_⟩
  · calc
      m ^ 3 * d = 1 * m ^ 3 * d := by ring
      _ ≤ 24 * m ^ 3 * d := Nat.mul_le_mul_right d
        (Nat.mul_le_mul_right (m ^ 3) (by decide))
  · have hm3 : m ≤ m ^ 3 := by
      simpa using pow_le_pow_right' hm (show 1 ≤ (3 : ℕ) by decide)
    calc
      12 * m * (d + 1) ≤ 12 * m * (2 * d) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 24 * m * d := by ring
      _ ≤ 24 * m ^ 3 * d := Nat.mul_le_mul_right d (Nat.mul_le_mul_left 24 hm3)

end MIPStarRE.QPBT.TensorCodeImport
