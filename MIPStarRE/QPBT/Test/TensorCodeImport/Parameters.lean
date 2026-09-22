import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Auxiliary sampling parameter for the tensor-code import

The printed value `m^3 * d` does not always satisfy the lower bound in the
cited tensor-code theorem. This module verifies scalar estimates for the
auxiliary maximum of that value and the required lower bound. It does not
change a game or apply an unformalized soundness theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-454`
- Ji et al., arXiv:2111.08131v3, Theorem 4.7 (`thm:main-bipartite`).
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

/-- Auxiliary parameter for Theorem 4.7. This is the least value
at least the printed `m^3 * d` and the required `12 * m * (d + 1)`. Its
use in a soundness application still requires the cited theorem and its
quantified error estimate, which are separate from these scalar facts. -/
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

/-- The exponential error at the candidate parameter is bounded by the
base-two error in the source statement, uniformly in the small-dimensional
cases as well. This holds for any nonnegative error exponent. -/
theorem sampling_exp_le (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (b : ℝ) (hb : 0 ≤ b) :
    Real.exp (-b * ((samplingCount m d : ℝ) / (m : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ (-b * (m : ℝ) * (d : ℝ)) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hK : (m : ℝ) ^ 3 * (d : ℝ) ≤ (samplingCount m d : ℝ) := by
    exact_mod_cast (sampling_bounds m d hm hd).2.1
  have hdiv : (m : ℝ) * (d : ℝ) ≤ (samplingCount m d : ℝ) / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hmpos)).mpr
    calc
      (m : ℝ) * (d : ℝ) * (m : ℝ) ^ 2 = (m : ℝ) ^ 3 * (d : ℝ) := by ring
      _ ≤ _ := hK
  have hlog : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hdiv hb
  have hlogmul := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ b * (m : ℝ) * (d : ℝ) by positivity)
  nlinarith

end MIPStarRE.QPBT.TensorCodeImport
