module

public import MIPStarRE.QPBT.Palomar.ExtractionBridge
public import MIPStarRE.QPBT.Palomar.PauliExtraction
public import MIPStarRE.QPBT.Palomar.PauliGameStrategyBridge

/-!
# Exact bridges for compact Pauli extraction quantities

This module identifies the compact Pauli parameter record, prescribed-answer
effects, ideal projectors, witnesses, and extraction errors with the registered
QPBT definitions.  Every comparison is an equality; no quantitative estimate
or soundness assumption is introduced here.

The legacy import form is required because the registered soundness modules
have not yet been converted to Lean's module system.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

attribute [local instance] compactPauliQuestionDecidableEq

/-- The compact admissibility witness has the registered named proposition. -/
theorem PauliParams.is_admissible_size (P : PauliParams) :
    MIPStarRE.QPBT.IsAdmissibleSize P.q :=
  P.hq

/-- Copy compact numerical parameters into the registered Pauli-test domain. -/
def PauliParams.toAdmissibleParams (P : PauliParams) :
    MIPStarRE.QPBT.AdmissibleParams where
  q := P.q
  m := P.m
  d := P.d
  hd := P.hd
  hq := P.is_admissible_size
  hdvd := P.hdvd

/-- Compact parameters are recovered exactly after conversion to the library record. -/
@[simp] theorem PauliParams.ofAdmissibleParams_toAdmissibleParams (P : PauliParams) :
    PauliParams.ofAdmissibleParams P.toAdmissibleParams = P := by
  cases P
  rfl

/-- Registered parameters are recovered exactly after conversion to the compact record. -/
@[simp] theorem PauliParams.toAdmissibleParams_ofAdmissibleParams
    (P : MIPStarRE.QPBT.AdmissibleParams) :
    (PauliParams.ofAdmissibleParams P).toAdmissibleParams = P := by
  cases P
  rfl

/-- The compact error function is definitionally the registered `deltaQld`. -/
@[simp] theorem deltaQld_eq_library (a b epsilon : ℝ) (m d q : ℕ) :
    deltaQld a b epsilon m d q = MIPStarRE.QPBT.deltaQld a b epsilon m d q :=
  rfl

/-- The compact generalized Pauli projector is the registered projector for
the same fixed trace and basis label. -/
theorem pauliProj_eq_library (P : PauliParams) (W : PauliKind)
    (u : PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) :
    pauliProj
        (MIPStarRE.QPBT.fixedBinTrace
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W u =
      MIPStarRE.QPBT.pauliProj (pauliKindEquiv W) u := by
  cases W <;> rfl

/-- The compact binary projector uses the registered fixed basis coordinates. -/
theorem qubitPauliProj_eq_library (P : PauliParams) (W : PauliKind)
    (u : PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) :
    qubitPauliProj W
        (binaryRegisterLabel
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates u) =
      MIPStarRE.QPBT.qubitPauliProj (pauliKindEquiv W)
        (MIPStarRE.QPBT.kappaVec
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size) u) := by
  cases W <;> rfl

/-- The concrete compact SPCC predicate is exactly the transported symmetric-game predicate. -/
theorem isPauliSPCC_iff_isSPCC (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricPauliStrategy (PauliParams.ofAdmissibleParams P)
      (MIPStarRE.QPBT.PauliScalar P)) :
    S.IsPauliSPCC (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) ↔
      S.IsSPCC (pauliSymmetricGame P) := by
  unfold SymmetricStrategy.IsPauliSPCC SymmetricStrategy.IsSPCC
  have hgame := congrArg Game.μ
    (pauliSymmetricGame_toGame P)
  have hmu : (pauliSymmetricGame P).μ =
      pauliQuestionPMF (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) := by
    simpa only [pauliGame] using hgame
  rw [hmu]

/-- Alice's raw compact effect is unchanged by conversion to the registered game. -/
theorem pauliStrategyToLibrary_alice_pauli_effect (P : PauliParams)
    (S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K)
    (W : PauliKind)
    (u : PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) :
    (((pauliStrategyToLibrary P.toAdmissibleParams S).A
      (MIPStarRE.QPBT.pauliQuestion P.toAdmissibleParams (pauliKindEquiv W))).effect
        (.pauliOutcome u)) =
      (S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u) := by
  cases W <;> rfl

/-- Bob's raw compact effect is unchanged by conversion to the registered game. -/
theorem pauliStrategyToLibrary_bob_pauli_effect (P : PauliParams)
    (S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K)
    (W : PauliKind)
    (u : PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) :
    (((pauliStrategyToLibrary P.toAdmissibleParams S).B
      (MIPStarRE.QPBT.pauliQuestion P.toAdmissibleParams (pauliKindEquiv W))).effect
        (.pauliOutcome u)) =
      (S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u) := by
  cases W <;> rfl

/-- Convert a registered qudit soundness witness to the compact strategy. -/
def ExtractionWitness.ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    ExtractionWitness (R := PauliRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- Convert a registered qubit soundness witness to the compact strategy. -/
def ExtractionWitness.ofQubitSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    ExtractionWitness (R := QubitRegister P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).basisDim) S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA
  φB := w.φB
  aux := w.aux
  aux_norm := w.aux_norm

/-- The compact qudit state error is exactly the registered unsquared state error. -/
@[simp] theorem stateError_ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    stateError (ExtractionWitness.ofPauliSoundnessWitness w) =
      ‖MIPStarRE.QPBT.isometryTensor w.φA w.φB
          (pauliStrategyToLibrary P.toAdmissibleParams S).ψ -
        MIPStarRE.QPBT.idealState P.toAdmissibleParams w.aux‖ :=
  rfl

/-- The compact qubit state error is exactly the registered unsquared state error. -/
@[simp] theorem stateError_ofQubitSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) :
    stateError (ExtractionWitness.ofQubitSoundnessWitness w) =
      ‖MIPStarRE.QPBT.isometryTensor w.φA w.φB
          (pauliStrategyToLibrary P.toAdmissibleParams S).ψ -
        MIPStarRE.QPBT.idealQubitState P.toAdmissibleParams w.aux‖ :=
  rfl

/-- Alice's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliAliceError_ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawPauliAliceError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (MIPStarRE.QPBT.fixedBinTrace
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceA P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliBobError_ofPauliSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawPauliBobError P S (ExtractionWitness.ofPauliSoundnessWitness w)
        (MIPStarRE.QPBT.fixedBinTrace
          (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      MIPStarRE.QPBT.rawPauliOperatorDistanceB P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Alice's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitAliceError_ofQubitSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawQubitAliceError P S (ExtractionWitness.ofQubitSoundnessWitness w)
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      MIPStarRE.QPBT.qubitOperatorDistanceA P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitBobError_ofQubitSoundnessWitness {P : PauliParams}
    {S : PauliStrategy P
      (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (pauliStrategyToLibrary P.toAdmissibleParams S)) (W : PauliKind) :
    rawQubitBobError P S (ExtractionWitness.ofQubitSoundnessWitness w)
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      MIPStarRE.QPBT.qubitOperatorDistanceB P.toAdmissibleParams
        (pauliStrategyToLibrary P.toAdmissibleParams S) w (pauliKindEquiv W) := by
  cases W <;> rfl

end

end MIPStarRE.QPBT.Palomar
