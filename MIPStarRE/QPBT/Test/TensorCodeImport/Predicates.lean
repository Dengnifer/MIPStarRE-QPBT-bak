import MIPStarRE.QPBT.Test.TensorCodeImport.Test
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.WinPredicate

/-!
# Acceptance implications for the tensor-code reduction

An accepted source answer has the correct constructor and passes every
parameter evaluation required by its line-point predicate. These implications
include both player roles and retain the source convention on zero directions.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:320-392,443-458`
- Ji et al., arXiv:2111.08131v3, Figures 1--2.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Either role assignment of an accepted source axis-point answer passes
the tensor test after translating the polynomial's affine parameter. Wrong
answer constructors are excluded by the actual source predicate. -/
theorem axis_readout_accepts (D : DirectLdParams) (r : Fin D.k)
    (sample : DirectLdSpace D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (.aline, directLdMap D .aline sample)
        (.point, directLdMap D .point sample) a b = true ∨
      directLdWinPredicate D (.point, directLdMap D .point sample)
        (.aline, directLdMap D .aline sample) b a = true) :
    (axisReadout D r (axisQuestion D sample) a).val (sample.point sample.index) =
      pointReadout D r b := by
  cases a <;> cases b <;>
    simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, if_true, if_false,
      decide_eq_true_eq, or_self] at hwin
  all_goals try contradiction
  rename_i f values
  have hs := directLineRepParameter_spec (coordinateDirection sample.index) sample.point
  have ht := congrFun hs sample.index
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinateDirection,
    Pi.single_eq_same, mul_one] at ht
  have hparameter : sample.point sample.index -
      lineRepMap (coordinateDirection sample.index) sample.point sample.index =
        directLineRepParameter (coordinateDirection sample.index) sample.point := by
    exact sub_eq_iff_eq_add.mpr (by simpa [coordinateDirection, add_comm] using ht)
  change evalCoefficient (f r) (sample.point sample.index -
      lineRepMap (coordinateDirection sample.index) sample.point sample.index) = values r
  rw [hparameter]
  exact hwin _ hs r

end

end MIPStarRE.QPBT.TensorCodeImport
