module

public import MIPStarRE.QPBT.Palomar.Extraction
public import MIPStarRE.QPBT.Palomar.PauliGame

/-!
# Compact Pauli extraction quantities

This Mathlib-only module specializes the compact strategy and extraction
vocabulary to the Pauli basis test.  It keeps the prescribed Pauli-outcome
effects raw, defines the qudit and qubit ideal projectors concretely, and keeps
Alice's and Bob's unaveraged squared operator errors separate.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1491`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT.Palomar

/-- A compact strategy on the full Pauli question and answer carriers. -/
abbrev PauliStrategy (P : PauliParams) (K : Type) [Fintype K] :=
  Strategy (PauliQuestion P K) (PauliQuestion P K)
    (PauliAnswer P K) (PauliAnswer P K)

/-- A compact symmetric strategy on the full Pauli carriers. -/
abbrev SymmetricPauliStrategy (P : PauliParams) (K : Type) [Fintype K] :=
  SymmetricStrategy (PauliQuestion P K) (PauliAnswer P K)

/-- The field-valued Boolean-cube register in the Pauli soundness conclusion. -/
abbrev PauliRegister (P : PauliParams) (K : Type) :=
  (Fin P.m → Bool) → K

/-- The binary register obtained by expanding each field coordinate in a fixed basis. -/
abbrev QubitRegister (P : PauliParams) (r : ℕ) :=
  (Fin P.m → Bool) × Fin r → ZMod 2

/-- The prescribed Pauli-basis question with zero ambient seed. -/
def pauliMeasurementQuestion {K : Type} [Zero K]
    (P : PauliParams) (W : PauliKind) : PauliQuestion P K :=
  (.pauli W, 0)

/-- The concrete projective, consistent, support-wise commuting predicate for
the compact Pauli question law. -/
def SymmetricStrategy.IsPauliSPCC {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (encoding : K ≃ Fin P.q)
    (S : SymmetricPauliStrategy P K) : Prop :=
  (∀ x, (S.meas x).IsProjective) ∧ S.IsConsistent ∧
    IsCommutingOn (pauliQuestionPMF P encoding) S.meas S.meas

/-- The error scale in the Pauli soundness and qubit-soundness conclusions. -/
noncomputable def deltaQld (a b epsilon : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow epsilon b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- The sign character used in the characteristic-two Pauli eigenvectors. -/
noncomputable def pauliPhaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

/-- One coordinate of a generalized Pauli eigenvector. -/
noncomputable def singlePauliVec {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (trace : K → ZMod 2) (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * pauliPhaseSign (trace (e * x))

/-- The tensor-product generalized Pauli eigenvector. -/
noncomputable def pauliVec {K I : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] (trace : K → ZMod 2) (W : PauliKind)
    (e x : I → K) : ℂ :=
  ∏ i : I, singlePauliVec trace W (e i) (x i)

/-- The rank-one generalized Pauli projector. -/
noncomputable def pauliProj {K I : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] (trace : K → ZMod 2) (W : PauliKind)
    (e : I → K) : Matrix (I → K) (I → K) ℂ :=
  Matrix.vecMulVec (pauliVec trace W e) (fun x => star (pauliVec trace W e x))

/-- The binary Pauli projector, using the trace of `ZMod 2` over itself. -/
noncomputable abbrev qubitPauliProj {I : Type} [Fintype I]
    (W : PauliKind) (e : I → ZMod 2) : Matrix (I → ZMod 2) (I → ZMod 2) ℂ :=
  pauliProj (Algebra.trace (ZMod 2) (ZMod 2)) W e

/-- Conjugate an operator by a local linear isometry. -/
noncomputable def conjIsometry {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J)
    (M : Matrix I I ℂ) : Matrix J J ℂ :=
  let U : Matrix J I ℂ := Matrix.toEuclideanLin.symm phi.toLinearMap
  U * M * Uᴴ

/-- Lift Alice's conjugated qudit effect to the full extracted target space. -/
noncomputable def liftedPauliAliceEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.2 = q.2 then conjIsometry phi M p.1 q.1 else 0

/-- Lift Bob's conjugated qudit effect to the full extracted target space. -/
noncomputable def liftedPauliBobEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (J' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1 = q.1 then conjIsometry phi M p.2 q.2 else 0

/-- Lift Alice's conjugated qubit effect by tensoring with Bob's identity. -/
noncomputable def liftedQubitAliceEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  Matrix.kronecker (conjIsometry phi M) 1

/-- Lift Bob's conjugated qubit effect by tensoring with Alice's identity. -/
noncomputable def liftedQubitBobEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (J' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  Matrix.kronecker 1 (conjIsometry phi M)

/-- Place a register projector on Alice's target register. -/
noncomputable def idealProjectorAlice {I' J' R : Type}
    [DecidableEq I'] [DecidableEq J'] [DecidableEq R]
    (M : Matrix R R ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1.1 = q.1.1 ∧ p.2 = q.2 then M p.1.2 q.1.2 else 0

/-- Place a register projector on Bob's target register. -/
noncomputable def idealProjectorBob {I' J' R : Type}
    [DecidableEq I'] [DecidableEq J'] [DecidableEq R]
    (M : Matrix R R ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then M p.2.2 q.2.2 else 0

/-- Expand a field-valued register label in fixed binary coordinates. -/
def binaryRegisterLabel {P : PauliParams} {K : Type} {r : ℕ}
    (coordinates : K → Fin r → ZMod 2) (u : PauliRegister P K) :
    QubitRegister P r :=
  fun p => coordinates (u p.1) p.2

/-- Alice's raw prescribed-answer qudit operator error. -/
noncomputable def rawPauliAliceError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := PauliRegister P K) S)
    (trace : K → ZMod 2) (W : PauliKind) : ℝ :=
  aliceOperatorError w
    (fun u => liftedPauliAliceEffect (J' := w.ιB') w.φA
      ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorAlice (J' := w.ιB') (pauliProj trace W u))

/-- Bob's raw prescribed-answer qudit operator error. -/
noncomputable def rawPauliBobError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := PauliRegister P K) S)
    (trace : K → ZMod 2) (W : PauliKind) : ℝ :=
  bobOperatorError w
    (fun u => liftedPauliBobEffect (I' := w.ιA') w.φB
      ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorBob (I' := w.ιA') (pauliProj trace W u))

/-- Alice's raw prescribed-answer qubit operator error, summed over the
original field-valued outcomes. -/
noncomputable def rawQubitAliceError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] {r : ℕ} (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := QubitRegister P r) S)
    (coordinates : K → Fin r → ZMod 2) (W : PauliKind) : ℝ :=
  aliceOperatorError w
    (fun u => liftedQubitAliceEffect (J' := w.ιB') w.φA
      ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorAlice (J' := w.ιB')
      (qubitPauliProj W (binaryRegisterLabel coordinates u)))

/-- Bob's raw prescribed-answer qubit operator error, summed over the
original field-valued outcomes. -/
noncomputable def rawQubitBobError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] {r : ℕ} (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := QubitRegister P r) S)
    (coordinates : K → Fin r → ZMod 2) (W : PauliKind) : ℝ :=
  bobOperatorError w
    (fun u => liftedQubitBobEffect (I' := w.ιA') w.φB
      ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorBob (I' := w.ιA')
      (qubitPauliProj W (binaryRegisterLabel coordinates u)))

end MIPStarRE.QPBT.Palomar
