import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.LDT.Basic.SubMeasurementCore

/-! # Approximating the tensor-product game value

Nonempty answer alphabets give a nonempty set of finite-dimensional strategies.
Every strict lower bound on its supremum is exceeded by one such strategy.
No maximum or common bound on the dimensions of these strategies is asserted.

## References

The supremum is `def:tensor-product-value` in
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:40-57`. The extraction
step is the first sentence of the proof of `lem:symmetric-strat`, lines 101-103.
The distinction from attainment is recorded in
`docs/paper-gaps/qpbt_symmetrization-attainment.tex` (issue #524).
-/

namespace MIPStarRE.QPBT

/-- Nonempty answer alphabets admit a finite-dimensional strategy. This
formalization-only support for `def:tensor-product-value` uses a unit state on
one-dimensional local spaces and returns the specified answers. The witness
establishes nonemptiness only; no lower bound on its value is claimed. -/
theorem Strategy.nonempty_of_answers (G : Game) (a₀ : G.AnswerA) (b₀ : G.AnswerB) :
    Nonempty (Strategy G) := by
  let A := MIPStarRE.LDT.Measurement.trivialDistinguishedOutcome (ι := Unit) a₀
  let B := MIPStarRE.LDT.Measurement.trivialDistinguishedOutcome (ι := Unit) b₀
  exact ⟨{
    ιA := Unit
    ιB := Unit
    ψ := EuclideanSpace.single ((), ()) 1
    ψ_norm := by simp
    A := fun _ => MIPStarRE.Quantum.Measurement.ofSumEqOne A.outcome A.outcome_pos
      (A.sum_eq_total.trans A.total_eq_one)
    B := fun _ => MIPStarRE.Quantum.Measurement.ofSumEqOne B.outcome B.outcome_pos
      (B.sum_eq_total.trans B.total_eq_one)
  }⟩

/-- Every strict lower bound on the game value is exceeded by a strategy when
both answer alphabets are nonempty. This formalization-only lemma supplies the
supremum step in the proof of `lem:symmetric-strat`, paper
`06_nonlocal_games_and_mipstar.tex:101-103`. It uses Mathlib's least-upper-bound
property and does not assert attainment of the game value. -/
theorem Game.exists_strategy_of_lt_value (G : Game)
    [Nonempty G.AnswerA] [Nonempty G.AnswerB] (v : ℝ) (hv : v < G.value) :
    ∃ S : Strategy G, v < S.value := by
  letI := Strategy.nonempty_of_answers G
    (Classical.choice inferInstance) (Classical.choice inferInstance)
  obtain ⟨w, ⟨S, rfl⟩, hw⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty (fun S : Strategy G => S.value)) hv
  exact ⟨S, hw⟩

end MIPStarRE.QPBT
