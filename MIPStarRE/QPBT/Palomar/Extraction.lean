module

public import MIPStarRE.QPBT.Palomar.Foundation

/-!
# Compact extraction witnesses and errors

This Mathlib-only module records the finite auxiliary spaces, local isometries,
and unit auxiliary state in the Pauli basis test conclusions.  It also defines
the normalized EPR factor, the shuffled auxiliary--EPR state, the unsquared
state error, and the separate unaveraged sums of squared operator errors.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1491`;
`references/qpbt-paper/04_preliminaries.tex:1180-1228`;
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-270`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT.Palomar

/-- Auxiliary finite spaces, local extraction isometries, and a unit auxiliary state. -/
structure ExtractionWitness {X Y A B R : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Fintype R] [DecidableEq R]
    (S : Strategy X Y A B) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × R)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × R)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

attribute [instance] ExtractionWitness.ιAFintype ExtractionWitness.ιBFintype
  ExtractionWitness.ιADecidableEq ExtractionWitness.ιBDecidableEq

/-- The normalized maximally entangled vector on a nonempty finite register. -/
noncomputable def normalizedEPRState (R : Type) [Fintype R] [DecidableEq R]
    [Nonempty R] : EuclideanSpace ℂ (R × R) :=
  (EuclideanSpace.equiv (R × R) ℂ).symm fun p =>
    if p.1 = p.2 then (Real.sqrt (Fintype.card R : ℝ) : ℂ)⁻¹ else 0

/-- Apply two local linear isometries to a bipartite Euclidean state. -/
noncomputable def localIsometryTensor {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) : EuclideanSpace ℂ (κA × κB) :=
  (EuclideanSpace.equiv (κA × κB) ℂ).symm fun p =>
    ∑ i : ιA, ∑ j : ιB,
      (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1 *
        (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2 * ψ (i, j)

/-- The auxiliary state tensored with the EPR vector, shuffled into player-local order. -/
noncomputable def idealExtractionState {X Y A B R : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S) :
    EuclideanSpace ℂ ((w.ιA' × R) × (w.ιB' × R)) :=
  (EuclideanSpace.equiv ((w.ιA' × R) × (w.ιB' × R)) ℂ).symm fun p =>
    w.aux (p.1.1, p.2.1) * normalizedEPRState R (p.1.2, p.2.2)

/-- The unsquared norm error between the extracted state and the ideal state. -/
noncomputable def stateError {X Y A B R : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S) : ℝ :=
  ‖localIsometryTensor w.φA w.φB S.ψ - idealExtractionState w‖

/-- Alice's unaveraged sum of squared operator errors on the ideal state. -/
noncomputable def aliceOperatorError {X Y A B R O : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype O]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S)
    (actual ideal : O → Matrix ((w.ιA' × R) × (w.ιB' × R))
      ((w.ιA' × R) × (w.ιB' × R)) ℂ) : ℝ :=
  ∑ o : O, ‖Matrix.toEuclideanLin (actual o - ideal o) (idealExtractionState w)‖ ^ 2

/-- Bob's unaveraged sum of squared operator errors on the ideal state. -/
noncomputable def bobOperatorError {X Y A B R O : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype O]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S)
    (actual ideal : O → Matrix ((w.ιA' × R) × (w.ιB' × R))
      ((w.ιA' × R) × (w.ιB' × R)) ℂ) : ℝ :=
  ∑ o : O, ‖Matrix.toEuclideanLin (actual o - ideal o) (idealExtractionState w)‖ ^ 2

end MIPStarRE.QPBT.Palomar
