import MIPStarRE.QPBT.Games.Distance
import MIPStarRE.QPBT.Games.DistributionAux
import MIPStarRE.QPBT.State

/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of `def:consistency` and
`def:strategy-distance` in `blueprint/src/chapter/ch12_qpbt_games.tex:180-220`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-271`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- Off-diagonal consistency defect for two operator families on a state. -/
noncomputable def consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  avgOver μ (fun x =>
    ∑ a : α, ∑ b : α,
      if a = b then 0 else
        (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm
          ((A x a * B x b).mulVec ψ))).re)

/-- The relation `A ≃_δ B` from `def:consistency`. -/
def IsConsistentWithin {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ) : Prop :=
  consistencyDefect μ A B ψ ≤ δ

/-- Operator distance with a unit answer alphabet, used for sums of effects. -/
noncomputable def opDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) : ℝ :=
  opFamilyDistSq μ (fun x (_ : Unit) => M x) (fun x (_ : Unit) => N x) ψ

theorem opDistSq_eq_opFamilyDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ M N ψ = opFamilyDistSq μ (fun x (_ : Unit) => M x)
      (fun x (_ : Unit) => N x) ψ := rfl

/-- Explicit transports and quantitative bounds for close bundled strategies. -/
structure AreCloseStrategies (G : Game)
    {ιA ιB ιA' ιB' : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (ψ' : EuclideanSpace ℂ (ιA' × ιB'))
    (A : G.QuestionA → Measurement G.AnswerA ιA)
    (A' : G.QuestionA → Measurement G.AnswerA ιA')
    (B : G.QuestionB → Measurement G.AnswerB ιB)
    (B' : G.QuestionB → Measurement G.AnswerB ιB') (δ : ℝ) where
  transportA : ιA ≃ ιA'
  transportB : ιB ≃ ιB'
  state : stateDistSq ψ (reindexState
      (Equiv.prodCongr transportA.symm transportB.symm) ψ') ≤ δ
  alice : opFamilyDistSq (G.μ.map Prod.fst)
      (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron (reindexOp transportA ((A' x).effect a)) 1) ψ ≤ δ
  bob : opFamilyDistSq (G.μ.map Prod.snd)
      (fun y b => heteroKron 1 ((B y).effect b))
      (fun y b => heteroKron 1 (reindexOp transportB ((B' y).effect b))) ψ ≤ δ

end MIPStarRE.QPBT
