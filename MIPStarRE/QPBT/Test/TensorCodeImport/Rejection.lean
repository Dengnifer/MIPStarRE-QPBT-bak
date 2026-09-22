import MIPStarRE.QPBT.Test.TensorCodeImport.Strategy

/-!
# Born rejection under finite readout

The tensor-test comparisons use the actual Born probabilities of the
constructed measurements. Finite postprocessing pulls a Boolean predicate
back to the original answer alphabets; thus malformed source answers retain
their full probability mass in a rejection comparison.

## References

- Ji et al., arXiv:2111.08131v3, Figures 1--2 and Definition 4.6.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:320-392,443-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open scoped BigOperators

noncomputable section

/-- The Born probability of failing a Boolean predicate at fixed questions. -/
def measurementRejection {α β ι κ : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ψ : EuclideanSpace ℂ (ι × κ)) (A : Measurement α ι) (B : Measurement β κ)
    (accept : α → β → Bool) : ℝ :=
  ∑ a, ∑ b, if accept a b then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect b))

/-- The rejection of postprocessed measurements is exactly the rejection of
the original measurements under the pulled-back predicate. -/
theorem measurementRejection_postprocess {α β α' β' ι κ : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ψ : EuclideanSpace ℂ (ι × κ)) (A : Measurement α ι) (B : Measurement β κ)
    (f : α → α') (g : β → β') (accept : α' → β' → Bool) :
    measurementRejection ψ (A.postprocess f) (B.postprocess g) accept =
      measurementRejection ψ A B (fun a b => accept (f a) (g b)) := by
  classical
  let loss := fun a b => if accept (f a) (g b) then 0
    else stateQForm ψ (heteroKron (A.effect a) (B.effect b))
  have hterm (a' : α') (b' : β') :
      (if accept a' b' then 0 else stateQForm ψ
        (heteroKron ((A.postprocess f).effect a') ((B.postprocess g).effect b'))) =
      ∑ a ∈ Finset.univ.filter (fun a => f a = a'),
        ∑ b ∈ Finset.univ.filter (fun b => g b = b'), loss a b := by
    rw [Measurement.postprocess_effect, Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum]
    simp_rw [heteroKron_finset_sum_right, stateQForm_finset_sum]
    by_cases h : accept a' b' = true
    · simp only [h, if_true]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b hb
      simp [loss, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, h]
    · simp only [h, Bool.false_eq_true, if_false]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp [loss, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, h]
  unfold measurementRejection
  simp_rw [hterm]
  calc
    _ = ∑ a', ∑ a ∈ Finset.univ.filter (fun a => f a = a'),
        ∑ b', ∑ b ∈ Finset.univ.filter (fun b => g b = b'), loss a b := by
      apply Finset.sum_congr rfl
      intro a' _
      exact Finset.sum_comm
    _ = ∑ a', ∑ a ∈ Finset.univ.filter (fun a => f a = a'), ∑ b, loss a b := by
      simp_rw [Finset.sum_fiberwise Finset.univ g]
    _ = _ := Finset.sum_fiberwise Finset.univ f _

/-- Rejection on the correlated register extension is the average rejection
in matching source blocks, for the actual predicate on both outcomes. -/
theorem measurementRejection_correlated (D : DirectLdParams)
    (S : Strategy (directLdGame D)) {α β : Type*} [Fintype α] [Fintype β]
    (A : PairRegister D → Measurement α S.ιA)
    (B : PairRegister D → Measurement β S.ιB) (accept : α → β → Bool) :
    measurementRejection (correlatedPairState D S)
        (blockDiagonalMeasurement A) (blockDiagonalMeasurement B) accept =
      avgOver (uniformDistribution (PairRegister D))
        (fun register => measurementRejection S.ψ (A register) (B register) accept) := by
  unfold measurementRejection
  simp_rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : accept a b = true
  · simp [h, avgOver_uniform_const]
  · simp only [h, blockDiagonalMeasurement_effect]
    exact correlatedPairState_born D S _ _

end

end MIPStarRE.QPBT.TensorCodeImport
