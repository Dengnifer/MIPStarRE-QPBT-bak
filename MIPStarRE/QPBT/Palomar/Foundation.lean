module

public import Mathlib

/-!
# Compact finite games and strategies

This Mathlib-only module gives the finite game, POVM, pure-state strategy, and
SPCC vocabulary used by the Palomar statement surface.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57,68-180`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

namespace MIPStarRE.QPBT.Palomar

/-- A finite two-player one-round game with a Mathlib probability mass function. -/
structure Game (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] where
  μ : PMF (X × Y)
  decide : X → Y → A → B → Bool

/-- A finite POVM, represented by positive semidefinite effects summing to the identity. -/
structure POVM (A I : Type*) [Fintype A] [Fintype I] [DecidableEq I] where
  effect : A → Matrix I I ℂ
  pos : ∀ a, (effect a).PosSemidef
  sum_eq_one : ∑ a, effect a = 1

/-- A finite-dimensional pure unit-state tensor-product strategy. -/
structure Strategy (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    where
  ιA : Type
  ιB : Type
  [ιAFintype : Fintype ιA]
  [ιBFintype : Fintype ιB]
  [ιADecidableEq : DecidableEq ιA]
  [ιBDecidableEq : DecidableEq ιB]
  ψ : EuclideanSpace ℂ (ιA × ιB)
  ψ_norm : ‖ψ‖ = 1
  alice : X → POVM A ιA
  bob : Y → POVM B ιB

attribute [instance] Strategy.ιAFintype Strategy.ιBFintype
  Strategy.ιADecidableEq Strategy.ιBDecidableEq

/-- Reindex a finite Euclidean state along an equivalence of coordinates. -/
noncomputable def reindexState {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J)
    (ψ : EuclideanSpace ℂ I) : EuclideanSpace ℂ J :=
  (EuclideanSpace.equiv J ℂ).symm (fun j => (EuclideanSpace.equiv I ℂ ψ) (e.symm j))

/-- A symmetric finite game. -/
structure SymmetricGame (X A : Type) [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] extends Game X X A A where
  μ_symm : ∀ x y, μ (x, y) = μ (y, x)
  decide_symm : ∀ x y a b, decide x y a b = decide y x b a

/-- A swap-invariant strategy using one local space and one measurement family. -/
structure SymmetricStrategy (X A : Type) [Fintype X] [Fintype A] where
  ι : Type
  [ιFintype : Fintype ι]
  [ιDecidableEq : DecidableEq ι]
  ψ : EuclideanSpace ℂ (ι × ι)
  ψ_norm : ‖ψ‖ = 1
  ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ
  meas : X → POVM A ι

attribute [instance] SymmetricStrategy.ιFintype SymmetricStrategy.ιDecidableEq

/-- Regard a symmetric strategy as a general tensor-product strategy. -/
def SymmetricStrategy.toStrategy {X A : Type} [Fintype X] [Fintype A]
    (S : SymmetricStrategy X A) : Strategy X X A A where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := S.meas
  bob := S.meas

/-- The Born weight of a fixed question and answer tuple. -/
noncomputable def Strategy.outcomeWeight {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (inner ℂ S.ψ (Matrix.toEuclideanLin
    (Matrix.kronecker ((S.alice x).effect a) ((S.bob y).effect b)) S.ψ)).re

/-- The tensor-product Born value of a strategy in a finite game. -/
noncomputable def Strategy.value {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y]
    [DecidableEq A] [DecidableEq B] (S : Strategy X Y A B) (G : Game X Y A B) : ℝ :=
  ∑ xy, (G.μ xy).toReal * ∑ a, ∑ b,
    if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0

/-- Every effect of a projective POVM is a self-adjoint idempotent. -/
def POVM.IsProjective {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : POVM A I) : Prop :=
  ∀ a, IsStarProjection (M.effect a)

/-- Projectivity of both measurement families of a strategy. -/
def Strategy.IsProjective {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (S : Strategy X Y A B) : Prop :=
  (∀ x, (S.alice x).IsProjective) ∧ ∀ y, (S.bob y).IsProjective

/-- State-dependent consistency of one POVM with itself across the two tensor factors. -/
def POVM.IsConsistentOn {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]
    (M : POVM A I) (ψ : EuclideanSpace ℂ (I × I)) : Prop :=
  ∀ a, (Matrix.kronecker (M.effect a) 1).mulVec ψ =
    (Matrix.kronecker 1 (M.effect a)).mulVec ψ

/-- Consistency of every measurement in a symmetric strategy. -/
def SymmetricStrategy.IsConsistent {X A : Type} [Fintype X] [Fintype A] [DecidableEq A]
    (S : SymmetricStrategy X A) : Prop :=
  ∀ x, (S.meas x).IsConsistentOn S.ψ

/-- Commutation on question pairs of strictly positive probability. -/
def IsCommutingOn {X Y A B I : Type*} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]
    (μ : PMF (X × Y)) (alice : X → POVM A I) (bob : Y → POVM B I) : Prop :=
  ∀ x y, 0 < μ (x, y) → ∀ a b, Commute ((alice x).effect a) ((bob y).effect b)

/-- Symmetric, projective, consistent, and support-wise commuting strategy. -/
def SymmetricStrategy.IsSPCC {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (S : SymmetricStrategy X A)
    (G : SymmetricGame X A) : Prop :=
  (∀ x, (S.meas x).IsProjective) ∧ S.IsConsistent ∧ IsCommutingOn G.μ S.meas S.meas

end MIPStarRE.QPBT.Palomar
