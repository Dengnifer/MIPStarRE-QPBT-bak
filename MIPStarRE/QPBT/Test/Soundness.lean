module

public import MIPStarRE.QPBT.Test.SoundnessDefs
public import MIPStarRE.QPBT.Test.Soundness.RangeProjection
public import MIPStarRE.QPBT.Test.Soundness.Ancilla
public import MIPStarRE.QPBT.Test.Soundness.OperatorTransfer
public import MIPStarRE.QPBT.Test.Soundness.ProjectiveSetting
public import MIPStarRE.QPBT.Test.Soundness.NaimarkReduction
public import MIPStarRE.QPBT.Test.Soundness.NaimarkOperatorTransfer
public import MIPStarRE.QPBT.Test.Soundness.NaimarkAssembly
public import MIPStarRE.QPBT.Test.Soundness.EpsReduction
public import MIPStarRE.QPBT.Test.Soundness.RawOperatorTransfer

/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem and provides auxiliary
range-projection estimates, ancilla isometries, and the transfer of supplied
extraction data to the three soundness estimates.
The scalar square-root error bound is in `MIPStarRE.QPBT.Combining.RootErrorBounds`.
The completed-family estimates are supplied by the Naimark reduction. The
final transfer bounds the rejected wrong-form mass and restores the raw Pauli
effects required by the paper before extending the result to the full error
domain.

## References

The main declaration is blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Explicit current-proof baseline for Pauli basis test soundness. The fixed
coefficient is `346 * 21 ^ 3 * aP ^ 4`, where `aP` is the projective-setting
coefficient exposed by the issue #729 quantitative cascade, and the fixed power
is `1 / 5242880000`.

This is a Lean-only quantitative specialization of blueprint `thm:pauli` and
the paper statement at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
It has exactly the source strategy and error domain and concludes the state
estimate and both raw prescribed-answer operator-family estimates for one
common normalized auxiliary state. -/
theorem pauli_soundness_explicit_baseline :
    1 ≤ pauliSoundnessBaselineConstant ∧
    0 < pauliSoundnessBaselinePower ∧
    pauliSoundnessBaselinePower < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : Strategy (pauliBasisTest P), 1 - epsilon ≤ S.value →
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
  have hprojective4 : 1 ≤ pauliBaselineProjectiveConstant ^ 4 :=
    one_le_pow₀ hprojective
  have hcoefficient : (1 : ℝ) ≤ 346 * 21 ^ (3 : ℕ) := by norm_num
  have hconstant : 1 ≤ pauliSoundnessBaselineConstant := by
    unfold pauliSoundnessBaselineConstant
    exact one_le_mul_of_one_le_of_one_le hcoefficient hprojective4
  have hpower : 0 < pauliSoundnessBaselinePower := by
    unfold pauliSoundnessBaselinePower
    norm_num
  have hpower1 : pauliSoundnessBaselinePower < 1 := by
    unfold pauliSoundnessBaselinePower
    norm_num
  refine ⟨hconstant, hpower, hpower1, ?_⟩
  intro P epsilon hepsilon S hwin
  exact arbitrary_strategy_raw_isometry_bounds_explicit_baseline P epsilon hepsilon S hwin

/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`thm:pauli`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
blueprint `def:povm-distance`.
-/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  exact exists_arbitrary_strategy_raw_isometry_bounds

end

end MIPStarRE.QPBT
