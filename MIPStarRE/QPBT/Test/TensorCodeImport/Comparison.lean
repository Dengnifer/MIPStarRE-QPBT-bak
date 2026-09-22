import MIPStarRE.QPBT.Test.TensorCodeImport.Predicates

/-!
# Comparison with the actual source branch losses

The comparison sums the Born rejection probabilities of the constructed
tensor strategy. Its only inputs are the source strategy and an answer
coordinate; acceptance implications are proved from the source predicate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:320-392,443-458`
- Ji et al., arXiv:2111.08131v3, Figures 1--2 and Definition 4.6.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

set_option maxHeartbeats 800000 in

/-- Every branch of the constructed tensor strategy is bounded by its
source branch. The endpoint inequalities hold separately for both ordered
positions, as required by Definition 4.6, including coincident endpoints. -/
theorem tensorCodeStrategyOfDirectLd_branch_bounds (D : DirectLdParams)
    (S : Strategy (directLdGame D)) (r : Fin D.k) :
    let T := tensorCodeStrategyOfDirectLd D S r
    let B := directLdBranchRejectionProbability D S
    T.axisRejection ≤ (B (.aline, .point) + B (.point, .aline)) / 2 ∧
    (∀ second, T.endpointRejection second ≤
      (B (.dline, .point) + B (.point, .dline)) / 2) ∧
    T.pointSyncRejection ≤ B (.point, .point) ∧
    T.axisSyncRejection ≤ B (.aline, .aline) ∧
    T.pairSyncRejection ≤ B (.dline, .dline) := by
  classical
  let T := tensorCodeStrategyOfDirectLd D S r
  let Q (t : LdType) (sample : DirectLdSpace D) := (t, directLdMap D t sample)
  let loss (x y : DirectLdQuestion D) :=
    measurementRejection S.ψ (S.A x) (S.B y) (directLdWinPredicate D x y)
  have hread {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (x y : PairRegister D → DirectLdQuestion D)
      (f : PairRegister D → DirectLdAnswer D → α)
      (g : PairRegister D → DirectLdAnswer D → β) (accept : α → β → Bool)
      (hacc : ∀ register a b, directLdWinPredicate D (x register) (y register) a b = true →
        accept (f register a) (g register b) = true) :
      measurementRejection (correlatedPairState D S)
          (blockDiagonalMeasurement fun register => (S.A (x register)).postprocess (f register))
          (blockDiagonalMeasurement fun register => (S.B (y register)).postprocess (g register))
          accept ≤ avgOver (uniformDistribution (PairRegister D))
            (fun register => loss (x register) (y register)) := by
    rw [measurementRejection_correlated]
    apply avgOver_mono
    intro register
    rw [measurementRejection_postprocess]
    exact measurementRejection_mono S.ψ _ _ _ _ (hacc register)
  have hend (pair : PairQuestion D) (register : PairRegister D) (second : Bool) :
      (fun j => endpoint second pair j.rev) =
        (endpointSample D second (register pair).val).point := by
    have h := congrArg (fun p : PairQuestion D => fun j : Fin D.m => endpoint second p j.rev)
      (register pair).property
    funext j
    have hj := congrFun h.symm j
    cases second <;>
      simpa [endpoint, diagonalPair, endpointSample, endpointShiftEquiv] using hj
  have hline (sample : DirectLdSpace D) (second : Bool) :
      Q .dline (endpointSample D second sample) = Q .dline sample := by
    cases second with
    | false => rfl
    | true =>
        dsimp [Q, endpointSample, endpointShiftEquiv, directLdMap]
        congr 2
        simpa only [one_smul] using lineRepMap_add_smul
          (directPrefixProjection sample.index sample.direction) sample.point 1
  have havg (second : Bool) (f : DirectLdSpace D → ℝ) :
      avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f (endpointSample D second sample)) =
      avgOver (uniformDistribution (DirectLdSpace D)) f := by
    cases second with
    | false => rfl
    | true =>
        simpa [endpointSample] using
          (Distribution.avgOver_map (uniformDistribution (DirectLdSpace D))
            (endpointShiftEquiv D) f).symm.trans
              (congrArg (fun μ => avgOver μ f)
                (uniformDistribution_map_equiv (endpointShiftEquiv D)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change avgOver _ _ ≤ _
    change _ ≤ (avgOver (uniformDistribution (DirectLdSpace D))
      (fun sample => loss (Q .aline sample) (Q .point sample)) +
      avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => loss (Q .point sample) (Q .aline sample))) / 2
    rw [← avgOver_add, div_eq_mul_inv, ← avgOver_mul_const]
    apply avgOver_mono
    intro sample
    have hA := hread (fun _ => Q .aline sample) (fun _ => Q .point sample)
      (fun _ => axisReadout D r (axisQuestion D sample)) (fun _ => pointReadout D r)
      (fun word a => decide (word.val (sample.point sample.index) = a))
      (fun _ a b h => by
        simpa using axis_readout_accepts D r sample a b (Or.inl h))
    have hB := hread (fun _ => Q .point sample) (fun _ => Q .aline sample)
      (fun _ => pointReadout D r) (fun _ => axisReadout D r (axisQuestion D sample))
      (fun a word => decide (word.val (sample.point sample.index) = a))
      (fun _ a b h => by
        simpa using axis_readout_accepts D r sample b a (Or.inr h))
    simp only [avgOver_uniform_const] at hA hB
    convert mul_le_mul_of_nonneg_right (add_le_add hA hB)
      (by positivity : (0 : ℝ) ≤ 2⁻¹) using 1
    all_goals
      try simp only [tensorCodeStrategyOfDirectLd, axisMeasurement, pointMeasurement,
        axisQuestion, directALineDescOf, DirectLineDesc.base, DirectLineDesc.index,
        directLdPointQuestionOf, Fin.rev_rev, Q, directLdMap, div_eq_mul_inv]
      rfl
  · intro second
    let F (sample : DirectLdSpace D) :=
      (loss (Q .dline sample) (Q .point (endpointSample D second sample)) +
        loss (Q .point (endpointSample D second sample)) (Q .dline sample)) / 2
    have hbound (pair : PairQuestion D) :
        (measurementRejection T.ψ (T.pairA pair) (T.pointB (endpoint second pair))
            (fun ab a => decide (endpoint second ab = a)) +
          measurementRejection T.ψ (T.pointA (endpoint second pair)) (T.pairB pair)
            (fun a ab => decide (endpoint second ab = a))) / 2 ≤
        avgOver (uniformDistribution (PairRegister D))
          (fun register => F (register pair).val) := by
      let x (register : PairRegister D) := Q .dline (register pair).val
      let y (_ : PairRegister D) :=
        directLdPointQuestionOf D (fun j => endpoint second pair j.rev)
      have hy (register : PairRegister D) :
          y register = Q .point (endpointSample D second (register pair).val) := by
        dsimp [y, Q, directLdPointQuestionOf, directLdMap]
        rw [hend]
      have hA := hread x y (fun register => pairReadout D r (register pair).val)
        (fun _ => pointReadout D r) (fun ab a => decide (endpoint second ab = a))
        (fun register a b h => by
          rw [hy] at h
          simpa using pair_readout_accepts D r (register pair).val second a b (Or.inl h))
      have hB := hread y x (fun _ => pointReadout D r)
        (fun register => pairReadout D r (register pair).val)
        (fun a ab => decide (endpoint second ab = a))
        (fun register a b h => by
          rw [hy] at h
          simpa using pair_readout_accepts D r (register pair).val second b a (Or.inr h))
      have hsum := div_le_div_of_nonneg_right (add_le_add hA hB) (by norm_num : (0 : ℝ) ≤ 2)
      conv at hsum => rhs; simp only [hy]
      convert hsum using 1
      all_goals
        (try simp only [T, tensorCodeStrategyOfDirectLd, pairMeasurement, pointMeasurement,
          x, y, F, div_eq_mul_inv, avgOver_mul_const, avgOver_add]) <;> rfl
    calc
      _ ≤ avgOver (tensorPairDistribution D) (fun pair =>
          avgOver (uniformDistribution (PairRegister D))
            (fun register => F (register pair).val)) := avgOver_mono _ _ _ hbound
      _ = avgOver (uniformDistribution (DirectLdSpace D)) F := pairRegister_average D F
      _ = _ := by
        have hF : F = fun sample =>
            (fun s => (loss (Q .dline s) (Q .point s) +
              loss (Q .point s) (Q .dline s)) / 2) (endpointSample D second sample) := by
          funext sample
          simp only [F, hline]
        rw [hF, havg second (fun s =>
          (loss (Q .dline s) (Q .point s) + loss (Q .point s) (Q .dline s)) / 2)]
        simp only [div_eq_mul_inv, avgOver_mul_const, avgOver_add]
        rfl
  · change avgOver _ _ ≤ avgOver _ _
    apply avgOver_mono
    intro sample
    have h := hread (fun _ => Q .point sample) (fun _ => Q .point sample)
      (fun _ => pointReadout D r) (fun _ => pointReadout D r) (fun a b => decide (a = b))
      (fun _ a b h => by
        rw [directLdAnswer_eq_of_win_self D _ h]
        simp)
    simp only [avgOver_uniform_const] at h
    convert h using 1
    all_goals
      try simp only [tensorCodeStrategyOfDirectLd, pointMeasurement, Fin.rev_rev,
        directLdPointQuestionOf, Q, directLdMap]
      rfl
  · change avgOver _ _ ≤ avgOver _ _
    apply avgOver_mono
    intro sample
    have h := hread (fun _ => Q .aline sample) (fun _ => Q .aline sample)
      (fun _ => axisReadout D r (axisQuestion D sample))
      (fun _ => axisReadout D r (axisQuestion D sample)) (fun a b => decide (a = b))
      (fun _ a b h => by
        rw [directLdAnswer_eq_of_win_self D _ h]
        simp)
    simp only [avgOver_uniform_const] at h
    convert h using 1
    all_goals
      try simp only [tensorCodeStrategyOfDirectLd, axisMeasurement, axisQuestion,
        directALineDescOf, DirectLineDesc.base, DirectLineDesc.index, Q, directLdMap]
      rfl
  · let F (sample : DirectLdSpace D) := loss (Q .dline sample) (Q .dline sample)
    calc
      _ ≤ avgOver (tensorPairDistribution D) (fun pair =>
          avgOver (uniformDistribution (PairRegister D))
            (fun register => F (register pair).val)) := by
        apply avgOver_mono
        intro pair
        exact hread (fun register => Q .dline (register pair).val)
          (fun register => Q .dline (register pair).val)
          (fun register => pairReadout D r (register pair).val)
          (fun register => pairReadout D r (register pair).val) (fun a b => decide (a = b))
          (fun _ a b h => by
            rw [directLdAnswer_eq_of_win_self D _ h]
            simp)
      _ = _ := pairRegister_average D F

end

end MIPStarRE.QPBT.TensorCodeImport
