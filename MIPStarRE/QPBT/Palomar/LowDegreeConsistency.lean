module

public import MIPStarRE.QPBT.Palomar.LowDegreeGame

/-!
# Compact low-degree consistency defects

This Mathlib-only module states the three consistency quantities in the
conclusion of low-degree soundness.  Deterministic postprocessing is kept at
the level of effects, so no auxiliary POVM proof fields enter the statement.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248` and
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:394-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- A compact strategy for the low-degree question and answer carriers. -/
abbrev LowDegreeStrategy (P : LowDegreeParams) (K : Type) [Fintype K] :=
  Strategy (LowDegreeQuestion P K) (LowDegreeQuestion P K)
    (LowDegreeAnswer P K) (LowDegreeAnswer P K)

/-- A compact POVM indexed by simultaneous bounded polynomial representatives. -/
abbrev LowDegreePolynomialPOVM (P : LowDegreeParams) (K I : Type)
    [CommSemiring K] [Fintype K] [Fintype I] [DecidableEq I] :=
  POVM (LowDegreePolynomialTuple P K) I

/-- The effect obtained by deterministic postprocessing along `f`. -/
def postprocessEffect {A B I : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Fintype I] [DecidableEq I]
    (M : POVM A I) (f : A → B) (b : B) : Matrix I I ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a

/-- Evaluate every polynomial in a simultaneous tuple at the same point. -/
def evalLowDegreePolynomialTuple {P : LowDegreeParams} {K : Type}
    [CommSemiring K] (u : Fin P.m → K) (g : LowDegreePolynomialTuple P K) :
    Fin P.k → K :=
  fun j => MvPolynomial.eval u (g j).1

/-- The compact point question associated with a field point. -/
def lowDegreePointQuestion {K : Type} [Zero K] (P : LowDegreeParams)
    (u : Fin P.m → K) : LowDegreeQuestion P K :=
  (.point, ((u, 0), 0))

/-- Read point values and send both malformed answer forms to the zero tuple. -/
def lowDegreePointValuesOrZero {P : LowDegreeParams} {K : Type} [Zero K] :
    LowDegreeAnswer P K → Fin P.k → K
  | .inl values => values
  | .inr (.inl _) => 0
  | .inr (.inr _) => 0

/-- The exact PMF-averaged off-diagonal Born weight of two local effect families. -/
def consistencyDefect {X O I J : Type*} [Fintype X] [Fintype O]
    [DecidableEq O] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : PMF X) (A : X → O → Matrix I I ℂ) (B : X → O → Matrix J J ℂ)
    (ψ : EuclideanSpace ℂ (I × J)) : ℝ :=
  ∑ x, (μ x).toReal * ∑ a, ∑ b, if a = b then 0 else
    (inner ℂ ψ ((EuclideanSpace.equiv (I × J) ℂ).symm
      ((Matrix.kronecker (A x a) (1 : Matrix J J ℂ) *
        Matrix.kronecker (1 : Matrix I I ℂ) (B x b)).mulVec ψ))).re

/-- Alice's point answers compared with evaluations of Bob's polynomial POVM. -/
def ldPointPolynomialDefect {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : LowDegreeParams) (S : LowDegreeStrategy P K)
    (GB : LowDegreePolynomialPOVM P K S.ιB) : ℝ :=
  consistencyDefect (PMF.uniformOfFintype (Fin P.m → K))
    (fun (u : Fin P.m → K) (a : Fin P.k → K) =>
      postprocessEffect (S.alice (lowDegreePointQuestion P u))
        (lowDegreePointValuesOrZero (P := P) (K := K)) a)
    (fun (u : Fin P.m → K) (a : Fin P.k → K) =>
      postprocessEffect GB (evalLowDegreePolynomialTuple u) a) S.ψ

/-- Evaluations of Alice's polynomial POVM compared with Bob's point answers. -/
def ldPolynomialPointDefect {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : LowDegreeParams) (S : LowDegreeStrategy P K)
    (GA : LowDegreePolynomialPOVM P K S.ιA) : ℝ :=
  consistencyDefect (PMF.uniformOfFintype (Fin P.m → K))
    (fun (u : Fin P.m → K) (a : Fin P.k → K) =>
      postprocessEffect GA (evalLowDegreePolynomialTuple u) a)
    (fun (u : Fin P.m → K) (a : Fin P.k → K) =>
      postprocessEffect (S.bob (lowDegreePointQuestion P u))
        (lowDegreePointValuesOrZero (P := P) (K := K)) a) S.ψ

/-- Alice's and Bob's complete polynomial tuples compared with no question law. -/
def ldPolynomialPolynomialDefect {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : LowDegreeParams) (S : LowDegreeStrategy P K)
    (GA : LowDegreePolynomialPOVM P K S.ιA)
    (GB : LowDegreePolynomialPOVM P K S.ιB) : ℝ :=
  consistencyDefect (PMF.uniformOfFintype Unit)
    (fun (_ : Unit) (g : LowDegreePolynomialTuple P K) => GA.effect g)
    (fun (_ : Unit) (g : LowDegreePolynomialTuple P K) => GB.effect g) S.ψ

/-- The error function of low-degree soundness, in argument order `(a,b,ε,q,m,d,k)`. -/
def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

end

end MIPStarRE.QPBT.Palomar
