module

public import MIPStarRE.QPBT.Test.QuantitativeSoundness
public import MIPStarRE.QPBT.Test.QubitForm

/-!
# Quantitative qubit form of Pauli basis test soundness

The exact binary-coordinate transport carries the structured and canonical
quantitative Pauli soundness bounds to qubit coordinates without changing the
state norm or either summed squared operator-family distance.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1491`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- Exact qubit-coordinate transport of the full-domain mixed component
headline. The squared state bound and both raw summed-squared operator bounds
are unchanged. -/
theorem pauli_soundness_qubit_quantitative_mixed_components
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    let e := min epsilon 1
    ∃ t : QubitSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ^ 2 ≤
          min 4 (16 * pauliSoundnessQuantitativeMixedScale P e) ∧
      (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
        min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)) ∧
      ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
        min 4 (pauliSoundnessQuantitativeMixedOperatorError P e) := by
  let e := min epsilon 1
  change ∃ t : QubitSoundnessWitness P R,
    ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ^ 2 ≤
        min 4 (16 * pauliSoundnessQuantitativeMixedScale P e) ∧
    (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
      min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)) ∧
    ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
      min 4 (pauliSoundnessQuantitativeMixedOperatorError P e)
  obtain ⟨w, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_mixed_components P epsilon hepsilon R hwin
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · rw [qubit_state_error_to_qubit P R w]
    exact hstate
  · intro W
    rw [qubit_operator_distance_a_to_qubit P R w W]
    exact hA W
  · intro W
    rw [qubit_operator_distance_b_to_qubit P R w W]
    exact hB W

/-- Exact qubit-coordinate transport of the fractional-dimensional common
error. The state norm and both raw summed-squared operator distances are
unchanged. -/
theorem pauli_soundness_qubit_quantitative_fractional
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : QubitSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ≤
          pauliSoundnessQuantitativeFractionalError P epsilon ∧
      (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeFractionalError P epsilon) ∧
      ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeFractionalError P epsilon := by
  obtain ⟨w, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_fractional P epsilon hepsilon R hwin
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · exact (qubit_state_error_to_qubit P R w).trans_le hstate
  · intro W
    exact (qubit_operator_distance_a_to_qubit P R w W).trans_le (hA W)
  · intro W
    exact (qubit_operator_distance_b_to_qubit P R w W).trans_le (hB W)

/-- Weakening: exact qubit-coordinate transport of the deferred degree-two
quantitative Pauli soundness bound. The state norm and both raw summed-squared
operator distances are preserved.

Bound: deferred #727. -/
theorem pauli_soundness_qubit_quantitative_degree_two
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : QubitSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ≤
          pauliSoundnessQuantitativeDegreeTwoError P epsilon ∧
      (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeDegreeTwoError P epsilon) ∧
      ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeDegreeTwoError P epsilon := by
  obtain ⟨w, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative_degree_two P epsilon hepsilon R hwin
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · exact (qubit_state_error_to_qubit P R w).trans_le hstate
  · intro W
    exact (qubit_operator_distance_a_to_qubit P R w W).trans_le (hA W)
  · intro W
    exact (qubit_operator_distance_b_to_qubit P R w W).trans_le (hB W)

/-- Exact qubit-coordinate transport of the structured quantitative Pauli
soundness bound. The witness has the same clipped degree-four common error as
`pauli_soundness_quantitative`. -/
theorem pauli_soundness_qubit_quantitative
    (P : AdmissibleParams) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value) :
    ∃ t : QubitSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ≤
          pauliSoundnessQuantitativeError P epsilon ∧
      (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
        pauliSoundnessQuantitativeError P epsilon) ∧
      ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
        pauliSoundnessQuantitativeError P epsilon := by
  obtain ⟨w, hstate, hA, hB⟩ :=
    pauli_soundness_quantitative P epsilon hepsilon R hwin
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · exact (qubit_state_error_to_qubit P R w).trans_le hstate
  · intro W
    exact (qubit_operator_distance_a_to_qubit P R w W).trans_le (hA W)
  · intro W
    exact (qubit_operator_distance_b_to_qubit P R w W).trans_le (hB W)

/-- Exact qubit-coordinate transport of the canonical quantitative Pauli
soundness theorem, with coefficient `100` and exponent `1 / 67108864`. -/
theorem pauli_soundness_qubit_quantitative_canonical :
    1 ≤ (100 : ℝ) ∧
    0 < pauliSoundnessQuantitativePower ∧
    pauliSoundnessQuantitativePower < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ R : Strategy (pauliBasisTest P), 1 - epsilon ≤ R.value →
          ∃ t : QubitSoundnessWitness P R,
            ‖isometryTensor t.φA t.φB R.ψ - idealQubitState P t.aux‖ ≤
                deltaQld 100 pauliSoundnessQuantitativePower
                  epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, qubitOperatorDistanceA P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind, qubitOperatorDistanceB P R t W ≤
              deltaQld 100 pauliSoundnessQuantitativePower
                epsilon P.m P.d P.q := by
  obtain ⟨hcoefficient, hpower, hpower1, hsound⟩ :=
    pauli_soundness_quantitative_canonical
  refine ⟨hcoefficient, hpower, hpower1, ?_⟩
  intro P epsilon hepsilon R hwin
  obtain ⟨w, hstate, hA, hB⟩ := hsound P epsilon hepsilon R hwin
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · exact (qubit_state_error_to_qubit P R w).trans_le hstate
  · intro W
    exact (qubit_operator_distance_a_to_qubit P R w W).trans_le (hA W)
  · intro W
    exact (qubit_operator_distance_b_to_qubit P R w W).trans_le (hB W)

end

end MIPStarRE.QPBT
