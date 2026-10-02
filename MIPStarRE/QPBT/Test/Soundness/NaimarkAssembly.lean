import MIPStarRE.QPBT.Test.Soundness.NaimarkOperatorTransfer
import MIPStarRE.QPBT.Test.Soundness.ProjectiveSetting
import MIPStarRE.QPBT.Test.Soundness.ScalarAbsorption

/-!
# Pauli isometry bounds for arbitrary strategies

The projective-setting isometry bounds are composed with the questionwise
Naimark dilation.  An arbitrary Pauli-test strategy winning with probability at
least `1 - ε` dilates to a projective setting at the same error, the projective
bounds apply there, and the resulting witness is pulled back to the original
spaces.  The state comparison transfers as an equality; both operator families
transfer with the dilation constants of `pauli_naimark_operator_distanceA_le`,
which the enlarged universal prefactor absorbs.  The error domain is still
restricted to `[0, 1]`.

## References

This is a formalization-only support result for blueprint `thm:pauli`, whose
source statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The source performs the projective reduction in one sentence at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`, and the
isometry passage is at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
Blueprint `thm:pauli-arbitrary-strategy-isometry-support`; issue #614.
-/

namespace MIPStarRE.QPBT

noncomputable section

/-- Arbitrary-strategy completed-family bounds at the fixed issue #729
baseline constants. The questionwise Naimark dilation preserves the state
estimate exactly and changes the common projective coefficient `aP` to
`21 * aP ^ 2`, without changing the exponent `bP`.

This Lean-only quantitative specialization follows the projective reduction
at `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`
and the final isometry passage at lines 1862-1876. It assumes exactly the
source winning condition on the substantive domain `0 ≤ epsilon ≤ 1`. -/
theorem arbitrary_strategy_isometry_bounds_explicit_baseline
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (hepsilon1 : epsilon ≤ 1) (S : Strategy (pauliBasisTest P))
    (hwin : 1 - epsilon ≤ S.value) :
    ∃ w : PauliSoundnessWitness P S,
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
        deltaQld (21 * pauliBaselineProjectiveConstant ^ 2)
          pauliBaselineProjectivePower epsilon P.m P.d P.q ∧
      (∀ W : PauliKind, pauliOperatorDistanceA P S w W ≤
        deltaQld (21 * pauliBaselineProjectiveConstant ^ 2)
          pauliBaselineProjectivePower epsilon P.m P.d P.q) ∧
      (∀ W : PauliKind, pauliOperatorDistanceB P S w W ≤
        deltaQld (21 * pauliBaselineProjectiveConstant ^ 2)
          pauliBaselineProjectivePower epsilon P.m P.d P.q) := by
  obtain ⟨habsorption, -, -, -⟩ := pauli_baseline_global_absorption_bound
  have hglobal : 1 ≤ pauliBaselineGlobalPairConstant := by
    unfold pauliBaselineGlobalPairConstant
    nlinarith
  have hextraction : 1 ≤ pauliBaselineExtractionConstant := by
    unfold pauliBaselineExtractionConstant
    norm_num
  have ha : 1 ≤ pauliBaselineProjectiveConstant := by
    have hextractionSq : 1 ≤ pauliBaselineExtractionConstant ^ 2 := by nlinarith
    have hproduct : 1 ≤
        pauliBaselineExtractionConstant ^ 2 * pauliBaselineGlobalPairConstant :=
      one_le_mul_of_one_le_of_one_le hextractionSq hglobal
    unfold pauliBaselineProjectiveConstant
    nlinarith
  have hb : 0 < pauliBaselineProjectivePower := by
    unfold pauliBaselineProjectivePower pauliBaselineGlobalPairPower
    norm_num
  have haa : pauliBaselineProjectiveConstant ≤
      21 * pauliBaselineProjectiveConstant ^ 2 := by nlinarith
  have hprojective :=
    projective_setting_isometry_bounds_explicit_baseline P epsilon hepsilon0
      hepsilon1 (pauliNaimarkSetting P epsilon S hwin)
  simp only [pauliNaimarkSetting] at hprojective
  obtain ⟨t, hstate, hA, hB⟩ := hprojective
  have hmono :
      deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q ≤
        deltaQld (21 * pauliBaselineProjectiveConstant ^ 2)
          pauliBaselineProjectivePower epsilon P.m P.d P.q :=
    deltaQld_mono ha haa le_rfl hb hepsilon0 hepsilon1
  have hstate' :
      ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
        idealState P t.aux‖ ≤
          deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
            epsilon P.m P.d P.q := hstate
  have hsq :
      ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
        idealState P t.aux‖ ^ 2 ≤
          deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
            epsilon P.m P.d P.q ^ 2 := by
    nlinarith [norm_nonneg
      (isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
        idealState P t.aux)]
  have habsorb :
      3 * deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q +
        6 * deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q ^ 2 ≤
        deltaQld (21 * pauliBaselineProjectiveConstant ^ 2)
          pauliBaselineProjectivePower epsilon P.m P.d P.q :=
    three_add_six_sq_deltaQld_le ha hb hepsilon0 hepsilon1
  refine ⟨pauliNaimarkWitness P S t, ?_, ?_, ?_⟩
  · rw [pauli_naimark_witness_state_distance_eq]
    exact hstate'.trans hmono
  · intro W
    have hA' : pauliOperatorDistanceA P (pauliNaimarkStrategy P S) t W ≤
        deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q := hA W
    calc
      pauliOperatorDistanceA P S (pauliNaimarkWitness P S t) W ≤
          3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P S) t W +
            6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
              idealState P t.aux‖ ^ 2 :=
        pauli_naimark_operator_distanceA_le P S t W
      _ ≤ 3 * deltaQld pauliBaselineProjectiveConstant
            pauliBaselineProjectivePower epsilon P.m P.d P.q +
          6 * deltaQld pauliBaselineProjectiveConstant
            pauliBaselineProjectivePower epsilon P.m P.d P.q ^ 2 := by
        linarith
      _ ≤ _ := habsorb
  · intro W
    have hB' : pauliOperatorDistanceB P (pauliNaimarkStrategy P S) t W ≤
        deltaQld pauliBaselineProjectiveConstant pauliBaselineProjectivePower
          epsilon P.m P.d P.q := hB W
    calc
      pauliOperatorDistanceB P S (pauliNaimarkWitness P S t) W ≤
          3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P S) t W +
            6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
              idealState P t.aux‖ ^ 2 :=
        pauli_naimark_operator_distanceB_le P S t W
      _ ≤ 3 * deltaQld pauliBaselineProjectiveConstant
            pauliBaselineProjectivePower epsilon P.m P.d P.q +
          6 * deltaQld pauliBaselineProjectiveConstant
            pauliBaselineProjectivePower epsilon P.m P.d P.q ^ 2 := by
        linarith
      _ ≤ _ := habsorb

/-- **Scope restriction:** the three Pauli soundness estimates for an
*arbitrary* strategy whose value is at least `1 - ε`, still restricted to
`0 ≤ ε ≤ 1`.  The projectivity hypothesis of
`exists_projective_setting_isometry_bounds` is discharged by the Naimark
dilation `pauliNaimarkSetting`, which preserves the value exactly, and the
witness is returned to the original spaces by `pauliNaimarkWitness`.  The
universal prefactor grows from `a` to `21 * a ^ 2`, which absorbs the
`3 * dilated + 6 * stateError ^ 2` transfer constants; the exponent `b` is
unchanged.  No hypothesis beyond the source premises is added.

This is a Lean-only support result, not the unrestricted source theorem at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`;
the remaining `1 < ε` part of the source domain is supplied by
`pauli_isometry_bounds_extend_epsilon`. -/
theorem exists_arbitrary_strategy_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hproj⟩ := exists_projective_setting_isometry_bounds
  have haa : a ≤ 21 * a ^ 2 := by nlinarith
  refine ⟨21 * a ^ 2, b, by nlinarith, hb, hb1, ?_⟩
  intro P ε hε0 hε1 S hwin
  have hprojective := hproj P ε hε0 hε1 (pauliNaimarkSetting P ε S hwin)
  simp only [pauliNaimarkSetting] at hprojective
  obtain ⟨t, hstate, hA, hB⟩ := hprojective
  have hmono : deltaQld a b ε P.m P.d P.q ≤
      deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    deltaQld_mono ha haa le_rfl hb hε0 hε1
  have hstate' : ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
      idealState P t.aux‖ ≤ deltaQld a b ε P.m P.d P.q := hstate
  have hsq : ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
      idealState P t.aux‖ ^ 2 ≤ deltaQld a b ε P.m P.d P.q ^ 2 := by
    nlinarith [norm_nonneg (isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
      idealState P t.aux)]
  have habsorb : 3 * deltaQld a b ε P.m P.d P.q +
      6 * deltaQld a b ε P.m P.d P.q ^ 2 ≤
        deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    three_add_six_sq_deltaQld_le ha hb hε0 hε1
  refine ⟨pauliNaimarkWitness P S t, ?_, ?_, ?_⟩
  · rw [pauli_naimark_witness_state_distance_eq]
    exact hstate'.trans hmono
  · intro W
    have hA' : pauliOperatorDistanceA P (pauliNaimarkStrategy P S) t W ≤
        deltaQld a b ε P.m P.d P.q := hA W
    calc pauliOperatorDistanceA P S (pauliNaimarkWitness P S t) W
        ≤ 3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P S) t W +
            6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
              idealState P t.aux‖ ^ 2 :=
          pauli_naimark_operator_distanceA_le P S t W
      _ ≤ 3 * deltaQld a b ε P.m P.d P.q +
            6 * deltaQld a b ε P.m P.d P.q ^ 2 := by linarith
      _ ≤ deltaQld (21 * a ^ 2) b ε P.m P.d P.q := habsorb
  · intro W
    have hB' : pauliOperatorDistanceB P (pauliNaimarkStrategy P S) t W ≤
        deltaQld a b ε P.m P.d P.q := hB W
    calc pauliOperatorDistanceB P S (pauliNaimarkWitness P S t) W
        ≤ 3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P S) t W +
            6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ -
              idealState P t.aux‖ ^ 2 :=
          pauli_naimark_operator_distanceB_le P S t W
      _ ≤ 3 * deltaQld a b ε P.m P.d P.q +
            6 * deltaQld a b ε P.m P.d P.q ^ 2 := by linarith
      _ ≤ deltaQld (21 * a ^ 2) b ε P.m P.d P.q := habsorb

end

end MIPStarRE.QPBT
