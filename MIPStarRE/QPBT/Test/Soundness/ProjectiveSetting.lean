import MIPStarRE.QPBT.Extraction.SourceUnitary
import MIPStarRE.QPBT.Test.Soundness.OperatorTransfer

/-!
# Pauli isometry bounds for projective settings

The global polynomial-pair measurement and the extraction unitaries are
constructed before transferring the three soundness estimates to local
isometries. The result is restricted to projective settings and errors in
`[0, 1]`; it does not assert soundness for arbitrary strategies.

## References

Blueprint `thm:pauli-projective-setting-isometry-support`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`
and `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The remaining domain and game-correspondence obligations are recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex` (issue #602).
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- Projective-setting soundness at the closed issue #729 baseline constants.
For every projective setting with `0 ≤ epsilon ≤ 1`, the global polynomial
pair and extraction data are constructed internally, and the state norm and
both complete squared Pauli-family distances are bounded by
`deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower`.

This Lean-only quantitative specialization follows the construction of paper
`lem:qld-unitary` and the final isometry passage at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`.
It has exactly the projective-setting domain of the existing support theorem
and adds no witness hypothesis. -/
theorem projective_setting_isometry_bounds_explicit_baseline
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (S : ProjectiveSetting P epsilon) :
    ∃ t : PauliSoundnessWitness P S.toStrategy,
      ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
        deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q ∧
      (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
        deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q) ∧
      (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
        deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q) := by
  obtain ⟨habsorption, -, -, -⟩ := pauli_baseline_global_absorption_bound
  have hC : 1 ≤ pauliBaselineExtractionConstant := by
    unfold pauliBaselineExtractionConstant
    norm_num
  have ha : 1 < pauliBaselineGlobalPairConstant := by
    unfold pauliBaselineGlobalPairConstant
    nlinarith
  have hb : 0 < pauliBaselineGlobalPairPower := by
    unfold pauliBaselineGlobalPairPower
    norm_num
  have hb1 : pauliBaselineGlobalPairPower < 1 := by
    unfold pauliBaselineGlobalPairPower
    norm_num
  obtain ⟨w, ⟨v⟩⟩ :=
    exists_extraction_witness_explicit P epsilon hepsilon0 hepsilon1 S
  simpa only [pauliBaselineProjectiveConstant, pauliBaselineProjectivePower] using
    pauli_soundness_delta_qld_of_extraction_witness_explicit
      pauliBaselineExtractionConstant pauliBaselineGlobalPairConstant
      pauliBaselineGlobalPairPower hC ha hb hb1 P epsilon hepsilon0 hepsilon1 S w v

/-- **Scope restriction:** For projective Pauli-test settings with
`0 ≤ epsilon ≤ 1`, local isometries and a normalized auxiliary state satisfy
the state norm and both complete Pauli-family bounds at a common `deltaQld`
scale. The universal constants are fixed before the setting. The global-pair
and extraction witnesses are constructed internally, not assumed.

This is a formalization-only support result for blueprint `thm:pauli`, not
the unrestricted theorem of the paper at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The isometry step follows the appendix at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`;
see `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue #602). -/
theorem exists_projective_setting_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ t : PauliSoundnessWitness P S.toStrategy,
            ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
              deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
              deltaQld a b epsilon P.m P.d P.q) ∧
            (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
              deltaQld a b epsilon P.m P.d P.q) := by
  obtain ⟨a, b, C, ha, hb, hb1, hC, hextract⟩ := exists_extractionWitness
  obtain ⟨A, B, hA, hB, hB1, htransfer⟩ :=
    pauli_soundness_deltaQld_ofExtractionWitness C a b hC ha hb hb1
  refine ⟨A, B, hA, hB, hB1, ?_⟩
  intro P epsilon hepsilon0 hepsilon1 S
  obtain ⟨w, ⟨v⟩⟩ := hextract P epsilon hepsilon0 hepsilon1 S
  exact htransfer P epsilon hepsilon0 hepsilon1 S w v

end

end MIPStarRE.QPBT
