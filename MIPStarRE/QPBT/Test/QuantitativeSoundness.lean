import MIPStarRE.QPBT.Combining.Quantitative
import MIPStarRE.QPBT.Test.Soundness
import MIPStarRE.QPBT.Test.Soundness.ComponentBounds
import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars

/-!
# Quantitative Pauli basis test soundness

This module combines the quantitative global polynomial-pair construction with
the componentwise extraction and raw-effect transfer. The result retains one
common witness for the state estimate and both source-facing Pauli operator
families, first at a degree-four structured error and then at the canonical
`deltaQld 100` error.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Explicit quantitative Pauli soundness with the common error
`min 4 (10^14 * (m*d)^4 * E_b)`, where the source error is clipped to
`e = min epsilon 1`, `b = 1 / 67108864`, and
`E_b = e^b + q^(-b) + 2^(-b*m*d)`.

This is a Lean-only quantitative specialization of blueprint `thm:pauli` and
the paper statement at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The proof constructs the global polynomial-pair and extraction witnesses
internally. It preserves one normalized auxiliary state and the raw prescribed
Pauli-answer effects on both sides. -/
theorem pauli_soundness_quantitative
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          pauliSoundnessQuantitativeError P epsilon ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeError P epsilon) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeError P epsilon := by
  let e := min epsilon 1
  have he : 0 ≤ e := by
    dsimp only [e]
    exact le_min hepsilon zero_le_one
  have he1 : e ≤ 1 := by
    dsimp only [e]
    exact min_le_right _ _
  have hwinE : 1 - e ≤ R.value := by
    by_cases hepsilon1 : epsilon ≤ 1
    · have heq : e = epsilon := by simp only [e, min_eq_left hepsilon1]
      rw [heq]
      exact hwin
    · have heq : e = 1 := by
        simp only [e, min_eq_right (le_of_lt (lt_of_not_ge hepsilon1))]
      rw [heq]
      simpa only [sub_self] using R.value_nonneg
  by_cases hsaturated :
      4 ≤ pauliSoundnessQuantitativeRawError P e
  · obtain ⟨_, _, _, hbaseline⟩ := pauli_soundness_explicit_baseline
    obtain ⟨t, _, _, _⟩ := hbaseline P epsilon hepsilon R hwin
    have herror : pauliSoundnessQuantitativeError P epsilon = 4 := by
      unfold pauliSoundnessQuantitativeError
      change min 4 (pauliSoundnessQuantitativeRawError P e) = 4
      exact min_eq_left hsaturated
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [herror]
      exact (pauli_soundness_state_distance_le_two P R t).trans (by norm_num)
    · intro W
      rw [herror]
      exact raw_pauli_operator_distance_a_le_four P R t W
    · intro W
      rw [herror]
      exact raw_pauli_operator_distance_b_le_four P R t W
  · have hmdNe : P.m * P.d ≠ 1 := by
      intro hmd
      exact hsaturated
        (four_le_pauli_soundness_quantitative_raw_error_of_md_eq_one P e he hmd)
    have hmdTwo : 2 ≤ P.m * P.d := by
      have hmdPos : 0 < P.m * P.d := Nat.mul_pos P.one_le_m P.hd
      omega
    have hratioLt : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) < 1 := by
      by_contra hratio
      have hone : 1 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) :=
        le_of_not_gt hratio
      exact hsaturated
        (four_le_pauli_soundness_quantitative_raw_error_of_one_le_ratio
          P e he hone)
    have hratio : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1 := hratioLt.le
    let S := pauliNaimarkSetting P e R hwinE
    obtain ⟨g, hg0, hgBound, hw⟩ :=
      exists_quantitative_global_pair_witness P e he he1 hratio S
    obtain ⟨w⟩ := hw
    have w' : GlobalPairWitness (pauliNaimarkSetting P e R hwinE) g := by
      simpa only [S] using w
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)
    let x : ℝ := 2800 * (g + Real.sqrt e + r)
    have hr0 : 0 ≤ r := by
      dsimp only [r]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      exact mul_nonneg (by norm_num)
        (add_nonneg (add_nonneg hg0 (Real.sqrt_nonneg e)) hr0)
    have hxBound : x ≤
        100000000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
          quantitativeGlobalPairEnvelope P e := by
      dsimp only [x, r]
      apply quantitative_extraction_scale_le P e g he he1
      simpa only [quantitativeGlobalPairEnvelope] using hgBound
    obtain ⟨t, hstateSq, hA, hB⟩ :=
      exists_pauli_soundness_witness_with_component_bounds
        P e he he1 R hwinE g hg0 w'
    have hstate :
        ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
          4 * Real.sqrt x := by
      have hnorm := norm_nonneg
        (isometryTensor t.φA t.φB R.ψ - idealState P t.aux)
      nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x]
    have hrawLe : pauliSoundnessQuantitativeRawError P e ≤ 4 :=
      (lt_of_not_ge hsaturated).le
    have herror : pauliSoundnessQuantitativeError P epsilon =
        pauliSoundnessQuantitativeRawError P e := by
      unfold pauliSoundnessQuantitativeError
      change min 4 (pauliSoundnessQuantitativeRawError P e) = _
      exact min_eq_right hrawLe
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [herror]
      exact hstate.trans
        (quantitative_state_component_le_raw_error P e x he hx0 hxBound)
    · intro W
      rw [herror]
      exact (hA W).trans
        (quantitative_operator_component_le_raw_error P e x he he1 hx0 hxBound)
    · intro W
      rw [herror]
      exact (hB W).trans
        (quantitative_operator_component_le_raw_error P e x he he1 hx0 hxBound)

/-- Canonical `deltaQld` specialization of `pauli_soundness_quantitative`, with
coefficient `100` and exponent `1 / 67108864`. -/
theorem pauli_soundness_quantitative_canonical :
    1 ≤ (100 : ℝ) ∧
    0 < pauliSoundnessQuantitativePower ∧
    pauliSoundnessQuantitativePower < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ R : Strategy (pauliBasisTest P), 1 - epsilon ≤ R.value →
          ∃ t : PauliSoundnessWitness P R,
            ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ≤
                deltaQld 100 pauliSoundnessQuantitativePower
                  epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q := by
  refine ⟨by norm_num, pauli_soundness_quantitative_power_pos,
    pauli_soundness_quantitative_power_lt_one, ?_⟩
  intro P epsilon hepsilon R hwin
  obtain ⟨t, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative P epsilon hepsilon R hwin
  have hcanonical := pauli_soundness_quantitative_error_le_deltaQld P epsilon hepsilon
  exact ⟨t, hstate.trans hcanonical, fun W => (hA W).trans hcanonical,
    fun W => (hB W).trans hcanonical⟩

end

end MIPStarRE.QPBT
