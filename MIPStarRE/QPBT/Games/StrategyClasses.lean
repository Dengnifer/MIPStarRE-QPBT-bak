import MIPStarRE.QPBT.Games.Defs
import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.State

/-! # Strategy classes and symmetric games

This module defines projective, commuting, consistent, PCC, and SPCC strategy
predicates from `blueprint/src/chapter/ch12_qpbt_games.tex:90-170`, with source
definitions in `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:58-218`.
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- A tensor-product strategy is projective when both answer measurements are. -/
def Strategy.IsProjective {G : Game} (S : Strategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.A x)) ∧
    ∀ y, MIPStarRE.QPBT.Measurement.IsProjective (S.B y)

/-- A symmetric game has one question and answer alphabet and symmetric data. -/
structure SymmetricGame where
  Question : Type
  Answer : Type
  [questionFintype : Fintype Question]
  [answerFintype : Fintype Answer]
  [questionDecidableEq : DecidableEq Question]
  [answerDecidableEq : DecidableEq Answer]
  μ : Distribution (Question × Question)
  μ_prob : μ.IsProbability
  μ_symm : ∀ x y, μ.weight (x, y) = μ.weight (y, x)
  decide : Question → Question → Answer → Answer → Bool
  decide_symm : ∀ x y a b, decide x y a b = decide y x b a

attribute [instance] SymmetricGame.questionFintype SymmetricGame.answerFintype
  SymmetricGame.questionDecidableEq SymmetricGame.answerDecidableEq

/-- Forget symmetry and view a symmetric game as a general game. -/
def SymmetricGame.toGame (G : SymmetricGame) : Game where
  QuestionA := G.Question
  QuestionB := G.Question
  AnswerA := G.Answer
  AnswerB := G.Answer
  μ := G.μ
  μ_prob := G.μ_prob
  decide := G.decide

/-- A strategy for a symmetric game uses one local space and one measurement family. -/
structure SymmetricStrategy (G : SymmetricGame) where
  ι : Type
  [ιFintype : Fintype ι]
  [ιDecidableEq : DecidableEq ι]
  ψ : EuclideanSpace ℂ (ι × ι)
  ψ_norm : ‖ψ‖ = 1
  ψ_swap : reindexState (Equiv.prodComm ι ι) ψ = ψ
  M : G.Question → Measurement G.Answer ι

attribute [instance] SymmetricStrategy.ιFintype SymmetricStrategy.ιDecidableEq

/-- Forget the symmetry witness and obtain a general tensor-product strategy. -/
def SymmetricStrategy.toStrategy {G : SymmetricGame} (S : SymmetricStrategy G) :
    Strategy G.toGame where
  ιA := S.ι
  ιB := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A := S.M
  B := S.M

/-- Commutation of two measurement families on a common local space. -/
def IsCommutingOn {X α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → α → Op ι) (B : X → β → Op ι) : Prop :=
  ∀ x, 0 < μ.weight x → ∀ a b, Commute (A x a) (B x b)

/-- A strategy is commuting when its local spaces can be identified and the
transported measurement families commute on the support. -/
def Strategy.IsCommuting {G : Game} (S : Strategy G) : Prop :=
  ∃ e : S.ιA ≃ S.ιB,
    IsCommutingOn G.μ
      (fun xy a => (S.A xy.1).effect a)
      (fun xy b => reindexOp e ((S.B xy.2).effect b))

/-- Consistency of one measurement on a bipartite state. -/
def Measurement.IsConsistentOn {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  ∀ a, (heteroKron (M.effect a) 1).mulVec ψ =
    (heteroKron 1 (M.effect a)).mulVec ψ

/-- Consistency of both families of a general strategy on a common state. -/
def IsConsistentStrategyOn {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (A : α → Measurement β ι) (B : α → Measurement β ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (A x) ψ) ∧
    ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (B x) ψ

/-- Consistency for a symmetric strategy. -/
def SymmetricStrategy.IsConsistent {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  ∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ

/-- Projective, consistent, commuting strategy predicate on a common space. -/
def Strategy.IsPCC {G : Game} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (G.QuestionA × G.QuestionB))
    (A : G.QuestionA → Measurement G.AnswerA ι)
    (B : G.QuestionB → Measurement G.AnswerB ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) ∧
    (∀ y, MIPStarRE.QPBT.Measurement.IsProjective (B y)) ∧
    (∀ x, MIPStarRE.QPBT.Measurement.IsConsistentOn (A x) ψ) ∧
    (∀ y, MIPStarRE.QPBT.Measurement.IsConsistentOn (B y) ψ) ∧
      IsCommutingOn μ (fun xy a => (A xy.1).effect a)
        (fun xy b => (B xy.2).effect b)

/-- Symmetric projective, consistent, commuting predicate. -/
def SymmetricStrategy.IsSPCC {G : SymmetricGame}
    (S : SymmetricStrategy G) : Prop :=
  (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧ S.IsConsistent ∧
    IsCommutingOn G.μ (fun xy a => (S.M xy.1).effect a)
      (fun xy b => (S.M xy.2).effect b)

/-- Source symmetrization statement; attainment remains a proof obligation. -/
theorem exists_symmetric_projective_strategy (G : SymmetricGame) (ε : ℝ)
    (hε : 0 ≤ ε) (h : G.toGame.value = 1 - ε) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε ≤ S.toStrategy.value := by
  sorry

/-- Established symmetrization from a concrete strategy, used by downstream proofs. -/
theorem exists_symmetric_projective_strategy_of_strategy (G : SymmetricGame)
    (ε : ℝ) (S₀ : Strategy G.toGame) (h : 1 - ε ≤ S₀.value) :
    ∃ S : SymmetricStrategy G, S.toStrategy.IsProjective ∧
      1 - ε ≤ S.toStrategy.value := by
  sorry

end MIPStarRE.QPBT
