import MIPStarRE.QPBT.Test.Soundness.RawOperatorTransferCore

/-!
# Final raw Pauli-effect soundness bounds

This module absorbs the completed-to-raw transfer loss into the Pauli
soundness error and exposes the fixed explicit baseline and existential
source-facing bounds. The operator transfer itself is implemented in
`MIPStarRE.QPBT.Test.Soundness.RawOperatorTransferCore`.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Universal scalar used to absorb the completed-to-raw transfer loss. -/
private noncomputable def rawPauliTransferFactor : ℝ :=
  2 + 4 * (Fintype.card PauliEdge : ℝ)

private theorem epsilon_le_deltaQld {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaQld a b ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hmd
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hpref : 1 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd ha0)
  have hεpow : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
  have hq := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpref)
    (add_nonneg (add_nonneg (Real.rpow_nonneg hε0 b) hq) htwo)]

private theorem raw_pauli_error_absorb {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * deltaQld a b ε P.m P.d P.q +
        4 * deltaQld a b ε P.m P.d P.q ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
      deltaQld (rawPauliTransferFactor * (21 * a ^ 2)) b ε P.m P.d P.q := by
  let d := deltaQld a b ε P.m P.d P.q
  let K := rawPauliTransferFactor
  have hd : 0 ≤ d := deltaQld_nonneg (zero_le_one.trans ha) hε0
  have hεd : ε ≤ d := epsilon_le_deltaQld ha hb hb1 hε0 hε1
  have hK : 1 ≤ K := by
    dsimp only [K, rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have hbase : 3 * d + 6 * d ^ 2 ≤
      deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    three_add_six_sq_deltaQld_le ha hb hε0 hε1
  calc
    2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤
        (2 + 4 * (Fintype.card PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard (sub_nonneg.mpr hεd)]
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard hd, mul_nonneg hcard (sq_nonneg d), sq_nonneg d]
    _ ≤ K * deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hK)
    _ ≤ deltaQld (K * (21 * a ^ 2)) b ε P.m P.d P.q := by
      exact scale_deltaQld_le (by nlinarith [sq_nonneg a]) hε0 hK

/-- Raw prescribed-effect bounds at the fixed issue #729 baseline constants.
The completed-family coefficient `21 * aP ^ 2` is transferred with the exact
factor `2 + 4 * 86 = 346`; scalar absorption contributes the remaining factor
`21`, giving `346 * 21 ^ 3 * aP ^ 4`. The exponent is unchanged and simplifies
to `1 / 5242880000`.

This Lean-only quantitative specialization proves the three conclusions of
paper `thm:pauli`, at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
for the raw prescribed answer effects and the full source domain `0 ≤ epsilon`.
-/
theorem arbitrary_strategy_raw_isometry_bounds_explicit_baseline
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ S.value) :
    ∃ w : PauliSoundnessWitness P S,
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
          deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
            epsilon P.m P.d P.q ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P S w W ≤
        deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
          epsilon P.m P.d P.q) ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceB P S w W ≤
        deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
          epsilon P.m P.d P.q) := by
  obtain ⟨habsorption, -, -, -⟩ := pauli_baseline_global_absorption_bound
  have hglobal : 1 ≤ pauliBaselineGlobalPairConstant := by
    unfold pauliBaselineGlobalPairConstant
    nlinarith
  have hextraction : 1 ≤ pauliBaselineExtractionConstant := by
    unfold pauliBaselineExtractionConstant
    norm_num
  have hprojective : 1 ≤ pauliBaselineProjectiveConstant := by
    have hextractionSq : 1 ≤ pauliBaselineExtractionConstant ^ 2 := by nlinarith
    have hproduct : 1 ≤
        pauliBaselineExtractionConstant ^ 2 * pauliBaselineGlobalPairConstant :=
      one_le_mul_of_one_le_of_one_le hextractionSq hglobal
    unfold pauliBaselineProjectiveConstant
    nlinarith
  let a := 21 * pauliBaselineProjectiveConstant ^ 2
  have ha : 1 ≤ a := by
    dsimp only [a]
    nlinarith [sq_nonneg pauliBaselineProjectiveConstant]
  have hb : 0 < pauliBaselineProjectivePower := by
    unfold pauliBaselineProjectivePower pauliBaselineGlobalPairPower
    norm_num
  have hb1 : pauliBaselineProjectivePower < 1 := by
    unfold pauliBaselineProjectivePower pauliBaselineGlobalPairPower
    norm_num
  have hfactor : 1 ≤ rawPauliTransferFactor := by
    dsimp only [rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have haa : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hrawCoefficient : a ≤ rawPauliTransferFactor * (21 * a ^ 2) := by
    have hnonneg : 0 ≤ 21 * a ^ 2 := mul_nonneg (by norm_num) (sq_nonneg a)
    exact haa.trans (le_mul_of_one_le_left hnonneg hfactor)
  have hconstant :
      rawPauliTransferFactor *
          (21 * (21 * pauliBaselineProjectiveConstant ^ 2) ^ 2) =
        pauliSoundnessBaselineConstant := by
    unfold rawPauliTransferFactor pauliSoundnessBaselineConstant
    rw [pauli_edge_card]
    norm_num only [Nat.cast_ofNat]
    ring
  have hpower : pauliBaselineProjectivePower = pauliSoundnessBaselinePower := by
    unfold pauliBaselineProjectivePower pauliBaselineGlobalPairPower
      pauliSoundnessBaselinePower
    norm_num
  have hbaselineConstant : 1 ≤ pauliSoundnessBaselineConstant := by
    have hinner : 1 ≤ 21 * a ^ 2 := by
      have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
      nlinarith
    have hproduct := one_le_mul_of_one_le_of_one_le hfactor hinner
    dsimp only [a] at hproduct
    rw [hconstant] at hproduct
    exact hproduct
  have hbaselinePower : 0 < pauliSoundnessBaselinePower := by
    rw [← hpower]
    exact hb
  have hsmall : ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
      epsilon ≤ 1 → ∀ S : Strategy (pauliBasisTest P), 1 - epsilon ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
                epsilon P.m P.d P.q ∧
          (∀ W : PauliKind, rawPauliOperatorDistanceA P S w W ≤
            deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
              epsilon P.m P.d P.q) ∧
          (∀ W : PauliKind, rawPauliOperatorDistanceB P S w W ≤
            deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
              epsilon P.m P.d P.q) := by
    intro P epsilon hepsilon0 hepsilon1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      arbitrary_strategy_isometry_bounds_explicit_baseline P epsilon hepsilon0
        hepsilon1 S hwin
    let d := deltaQld a pauliBaselineProjectivePower epsilon P.m P.d P.q
    have hstate' :
        ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ d := hstate
    have hcompletedA' : ∀ W : PauliKind,
        pauliOperatorDistanceA P S w W ≤ d := hcompletedA
    have hcompletedB' : ∀ W : PauliKind,
        pauliOperatorDistanceB P S w W ≤ d := hcompletedB
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * epsilon ≤
          deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
            epsilon P.m P.d P.q := by
      dsimp only [d, a]
      rw [← hconstant, ← hpower]
      exact raw_pauli_error_absorb ha hb hb1 hepsilon0 hepsilon1
    have hmono : d ≤
        deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
          epsilon P.m P.d P.q := by
      dsimp only [d, a]
      rw [← hconstant, ← hpower]
      exact deltaQld_mono ha hrawCoefficient le_rfl hb hepsilon0 hepsilon1
    refine ⟨w, hstate'.trans hmono, ?_, ?_⟩
    · intro W
      calc
        rawPauliOperatorDistanceA P S w W ≤
            2 * pauliOperatorDistanceA P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * epsilon :=
          raw_pauli_operator_distanceA_le_completed S hwin w hstate' W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * epsilon := by
          linarith [hcompletedA' W]
        _ ≤ _ := habsorb
    · intro W
      calc
        rawPauliOperatorDistanceB P S w W ≤
            2 * pauliOperatorDistanceB P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * epsilon :=
          raw_pauli_operator_distanceB_le_completed S hwin w hstate' W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * epsilon := by
          linarith [hcompletedB' W]
        _ ≤ _ := habsorb
  rcases le_or_gt epsilon 1 with hepsilon1 | hepsilon1
  · exact hsmall P epsilon hepsilon0 hepsilon1 S hwin
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono :
        deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
            1 P.m P.d P.q ≤
          deltaQld pauliSoundnessBaselineConstant pauliSoundnessBaselinePower
            epsilon P.m P.d P.q :=
      deltaQld_mono_epsilon hbaselineConstant hbaselinePower zero_le_one hepsilon1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩

/-- The arbitrary-strategy soundness estimates for the raw prescribed Pauli
answer effects of `thm:pauli`. The completed-family Naimark estimates remain
internal and their transfer loss is absorbed into the existential prefactor. -/
theorem exists_arbitrary_strategy_raw_isometry_bounds :
    ∃ A b : ℝ, 1 ≤ A ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld A b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
  obtain ⟨a, b, ha, hb, hb1, hcompleted⟩ := exists_arbitrary_strategy_isometry_bounds
  let A := rawPauliTransferFactor * (21 * a ^ 2)
  have hfactor : 1 ≤ rawPauliTransferFactor := by
    dsimp only [rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have h21 : 1 ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ rawPauliTransferFactor * (21 * a ^ 2) :=
        mul_le_mul hfactor h21 zero_le_one (zero_le_one.trans hfactor)
  have ha21 : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have h21A : 21 * a ^ 2 ≤ A := by
    dsimp only [A]
    exact le_mul_of_one_le_left (by positivity) hfactor
  have haA : a ≤ A := ha21.trans h21A
  have hsmall : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld A b ε P.m P.d P.q ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
    intro P ε hε0 hε1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      hcompleted P ε hε0 hε1 S hwin
    let d := deltaQld a b ε P.m P.d P.q
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
          deltaQld A b ε P.m P.d P.q := by
      dsimp only [d, A]
      exact raw_pauli_error_absorb ha hb hb1 hε0 hε1
    have hmono : d ≤ deltaQld A b ε P.m P.d P.q := by
      dsimp only [d]
      exact deltaQld_mono ha haA le_rfl hb hε0 hε1
    refine ⟨w, hstate.trans hmono, ?_, ?_⟩
    · intro W
      calc
        rawPauliOperatorDistanceA P S w W ≤
            2 * pauliOperatorDistanceA P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceA_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedA W]
        _ ≤ _ := habsorb
    · intro W
      calc
        rawPauliOperatorDistanceB P S w W ≤
            2 * pauliOperatorDistanceB P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceB_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedB W]
        _ ≤ _ := habsorb
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact hsmall P ε hε0 hε1 S hwin
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : deltaQld A b 1 P.m P.d P.q ≤
        deltaQld A b ε P.m P.d P.q :=
      deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩

end

end MIPStarRE.QPBT
