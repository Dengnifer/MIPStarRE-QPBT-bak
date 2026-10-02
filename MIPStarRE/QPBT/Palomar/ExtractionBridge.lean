module

public import MIPStarRE.QPBT.Palomar.Bridge
public import MIPStarRE.QPBT.Palomar.Extraction
public import MIPStarRE.QPBT.Test.QubitForm

/-!
# Exact bridges for compact extraction errors

This module converts the existing qudit and qubit soundness witnesses to the
compact extraction witness.  It specializes the generic errors to the raw
prescribed-answer effects and proves exact equality with the established
soundness quantities.  No soundness existence or numerical estimate is added.

The legacy import form is required because the existing soundness modules have
not yet been converted to Lean's module system.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1491`;
`references/qpbt-paper/04_preliminaries.tex:1180-1228`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace PauliSoundnessWitness

/-- Convert a qudit soundness witness to the compact extraction witness. -/
def toPalomar {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P S) :
    Palomar.ExtractionWitness (R := PauliRegister P) (Palomar.Strategy.ofStrategy S) where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- The compact ideal state is exactly the existing qudit ideal state. -/
@[simp] theorem idealExtractionState_toPalomar
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    Palomar.idealExtractionState w.toPalomar = idealState P w.aux := rfl

/-- The compact unsquared state error is exactly the existing qudit state error. -/
@[simp] theorem stateError_toPalomar
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    Palomar.stateError w.toPalomar =
      ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ := rfl

end PauliSoundnessWitness

namespace QubitSoundnessWitness

/-- Convert a qubit soundness witness to the compact extraction witness. -/
def toPalomar {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : QubitSoundnessWitness P S) :
    Palomar.ExtractionWitness (R := QubitRegister P) (Palomar.Strategy.ofStrategy S) where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- The compact ideal state is exactly the existing qubit ideal state. -/
@[simp] theorem idealExtractionState_toPalomar
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) :
    Palomar.idealExtractionState w.toPalomar = idealQubitState P w.aux := rfl

/-- The compact unsquared state error is exactly the existing qubit state error. -/
@[simp] theorem stateError_toPalomar
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) :
    Palomar.stateError w.toPalomar =
      ‖isometryTensor w.φA w.φB S.ψ - idealQubitState P w.aux‖ := rfl

end QubitSoundnessWitness

namespace Palomar

/-- Alice's compact qudit error specialized to raw prescribed-answer effects. -/
def pauliAliceOperatorError (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) : ℝ :=
  aliceOperatorError w.toPalomar
    (fun u => liftedAEffect S w.φA
      ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)))
    (fun u => pauliProjOnA'' P W u)

/-- Bob's compact qudit error specialized to raw prescribed-answer effects. -/
def pauliBobOperatorError (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) : ℝ :=
  bobOperatorError w.toPalomar
    (fun u => liftedBEffect S w.φB
      ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)))
    (fun u => pauliProjOnB'' P W u)

/-- Alice's compact qubit error, still summed over the original field outcomes. -/
def qubitAliceOperatorError (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) : ℝ :=
  aliceOperatorError w.toPalomar
    (fun u => liftedQubitAEffect S w.φA
      ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)))
    (fun u => qubitProjOnA'' P W u)

/-- Bob's compact qubit error, still summed over the original field outcomes. -/
def qubitBobOperatorError (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) : ℝ :=
  bobOperatorError w.toPalomar
    (fun u => liftedQubitBEffect S w.φB
      ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)))
    (fun u => qubitProjOnB'' P W u)

/-- The compact Alice qudit sum equals the source-facing raw Pauli distance. -/
@[simp] theorem pauliAliceOperatorError_eq
    (P : AdmissibleParams) (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    pauliAliceOperatorError P S w W = rawPauliOperatorDistanceA P S w W := rfl

/-- The compact Bob qudit sum equals the source-facing raw Pauli distance. -/
@[simp] theorem pauliBobOperatorError_eq
    (P : AdmissibleParams) (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    pauliBobOperatorError P S w W = rawPauliOperatorDistanceB P S w W := rfl

/-- The compact Alice qubit sum equals the established qubit distance. -/
@[simp] theorem qubitAliceOperatorError_eq
    (P : AdmissibleParams) (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    qubitAliceOperatorError P S w W = qubitOperatorDistanceA P S w W := rfl

/-- The compact Bob qubit sum equals the established qubit distance. -/
@[simp] theorem qubitBobOperatorError_eq
    (P : AdmissibleParams) (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : QubitSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    qubitBobOperatorError P S w W = qubitOperatorDistanceB P S w W := rfl

/-- Fixed-basis qudit-to-qubit transport preserves the compact state error exactly. -/
theorem stateError_toQubit (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    stateError w.toQubit.toPalomar = stateError w.toPalomar := by
  rw [QubitSoundnessWitness.stateError_toPalomar,
    PauliSoundnessWitness.stateError_toPalomar]
  exact qubit_state_error_to_qubit P S w

/-- Fixed-basis transport preserves Alice's compact squared operator sum exactly. -/
theorem pauliAliceOperatorError_toQubit (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    qubitAliceOperatorError P S w.toQubit W = pauliAliceOperatorError P S w W := by
  simpa using qubit_operator_distance_a_to_qubit P S w W

/-- Fixed-basis transport preserves Bob's compact squared operator sum exactly. -/
theorem pauliBobOperatorError_toQubit (P : AdmissibleParams)
    (S : MIPStarRE.QPBT.Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (W : MIPStarRE.QPBT.PauliKind) :
    qubitBobOperatorError P S w.toQubit W = pauliBobOperatorError P S w W := by
  simpa using qubit_operator_distance_b_to_qubit P S w W

end Palomar

end

end MIPStarRE.QPBT
