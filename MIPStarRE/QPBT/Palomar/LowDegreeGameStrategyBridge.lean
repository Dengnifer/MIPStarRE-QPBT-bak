module

public import MIPStarRE.QPBT.Palomar.LowDegreeGameBridge

/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

namespace POVM

/-- Relabel the outcomes of a compact POVM along an equivalence. -/
def relabel {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [DecidableEq I] (e : A ≃ B) (M : POVM A I) : POVM B I where
  effect := fun b => M.effect (e.symm b)
  pos := fun b => M.pos (e.symm b)
  sum_eq_one := by
    calc
      ∑ b : B, M.effect (e.symm b) = ∑ a : A, M.effect a :=
        Equiv.sum_comp e.symm M.effect
      _ = 1 := M.sum_eq_one

/-- Outcome relabeling preserves every POVM effect. -/
@[simp] theorem relabel_effect {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : POVM A I) (b : B) :
    (relabel e M).effect b = M.effect (e.symm b) :=
  rfl

/-- Outcome relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : POVM A I) :
    (relabel e M).IsProjective ↔ M.IsProjective := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    exact h (e.symm b)

end POVM

namespace Game

/-- Two compact games on fixed carriers are equal when their data fields agree. -/
theorem ext {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    {G H : Game X Y A B} (hμ : G.μ = H.μ) (hdecide : G.decide = H.decide) :
    G = H := by
  cases G
  cases H
  simp_all

/-- Relabel all question and answer carriers of a compact game. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : Game X' Y' A' B' where
  μ := G.μ.map (Equiv.prodCongr eX eY)
  decide := fun x y a b =>
    G.decide (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b)

end Game

namespace Strategy

/-- Relabel the questions and outcomes of a compact strategy. -/
def relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') : Strategy X' Y' A' B' where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  alice := fun x => POVM.relabel eA (S.alice (eX.symm x))
  bob := fun y => POVM.relabel eB (S.bob (eY.symm y))

/-- Relabeling preserves each Born weight after pulling back all four labels. -/
@[simp] theorem outcomeWeight_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') (x : X') (y : Y') (a : A') (b : B') :
    (relabel S eX eY eA eB).outcomeWeight x y a b =
      S.outcomeWeight (eX.symm x) (eY.symm y) (eA.symm a) (eB.symm b) :=
  rfl

/-- Relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : Strategy X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') :
    (relabel S eX eY eA eB).IsProjective ↔ S.IsProjective := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      have hx := hA (eX x)
      change (POVM.relabel eA (S.alice (eX.symm (eX x)))).IsProjective at hx
      rw [eX.symm_apply_apply] at hx
      exact (POVM.relabel_isProjective_iff eA (S.alice x)).mp hx
    · intro y
      have hy := hB (eY y)
      change (POVM.relabel eB (S.bob (eY.symm (eY y)))).IsProjective at hy
      rw [eY.symm_apply_apply] at hy
      exact (POVM.relabel_isProjective_iff eB (S.bob y)).mp hy
  · rintro ⟨hA, hB⟩
    constructor
    · intro x
      exact (POVM.relabel_isProjective_iff eA (S.alice (eX.symm x))).mpr
        (hA (eX.symm x))
    · intro y
      exact (POVM.relabel_isProjective_iff eB (S.bob (eY.symm y))).mpr
        (hB (eY.symm y))

/-- A double finite sum is invariant under equivalences of both indices. -/
private theorem sum_equiv₂ {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (eA : A ≃ A') (eB : B ≃ B')
    (f : A → B → ℝ) :
    (∑ a : A', ∑ b : B', f (eA.symm a) (eB.symm b)) =
      ∑ a : A, ∑ b : B, f a b := by
  calc
    (∑ a : A', ∑ b : B', f (eA.symm a) (eB.symm b)) =
        ∑ a : A, ∑ b : B', f a (eB.symm b) :=
      Equiv.sum_comp eA.symm (fun a => ∑ b : B', f a (eB.symm b))
    _ = ∑ a : A, ∑ b : B, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eB.symm (f a)

/-- Simultaneous relabeling of a compact game and strategy preserves value exactly. -/
theorem value_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (S : Strategy X Y A B)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    (relabel S eX eY eA eB).value (Game.relabel G eX eY eA eB) =
      S.value G := by
  unfold Strategy.value
  change PMF.realWeightedSum (G.μ.map (Equiv.prodCongr eX eY)) _ =
    PMF.realWeightedSum G.μ _
  rw [PMF.realWeightedSum_map]
  apply congrArg (PMF.realWeightedSum G.μ)
  funext xy
  simp only [Game.relabel, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    outcomeWeight_relabel, Equiv.symm_apply_apply]
  exact sum_equiv₂ eA eB (fun a b =>
    if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0)

end Strategy

/-- Relabeling the concrete compact game gives the original registered game. -/
theorem lowDegreeGame_relabel_eq (P : MIPStarRE.QPBT.LdParams) :
    Game.relabel
        (lowDegreeGame (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model))
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P) =
      Game.ofGame (MIPStarRE.QPBT.ldGame P) := by
  apply Game.ext
  · exact lowDegreeQuestionPMF_map P
  · funext x y a b
    change lowDegreeWin (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        ((lowDegreeQuestionEquiv P).symm x) ((lowDegreeQuestionEquiv P).symm y)
        ((lowDegreeAnswerEquiv P).symm a) ((lowDegreeAnswerEquiv P).symm b) =
      MIPStarRE.QPBT.ldWinPredicate P x y a b
    simpa using lowDegreeWin_equiv P
      ((lowDegreeQuestionEquiv P).symm x) ((lowDegreeQuestionEquiv P).symm y)
      ((lowDegreeAnswerEquiv P).symm a) ((lowDegreeAnswerEquiv P).symm b)

/-- Convert a compact low-degree strategy into a strategy for the registered game. -/
def lowDegreeStrategyToLibrary (P : MIPStarRE.QPBT.LdParams)
    (S : Strategy
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))) :
    MIPStarRE.QPBT.Strategy (MIPStarRE.QPBT.ldGame P) :=
  Strategy.toStrategy (G := MIPStarRE.QPBT.ldGame P)
    (Strategy.relabel S
      (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
      (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P))

/-- Conversion to the registered low-degree game preserves the strategy value exactly. -/
theorem lowDegreeStrategyToLibrary_value (P : MIPStarRE.QPBT.LdParams)
    (S : Strategy
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))) :
    (lowDegreeStrategyToLibrary P S).value =
      S.value (lowDegreeGame (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)) := by
  let S' := Strategy.relabel S
    (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
    (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P)
  calc
    (lowDegreeStrategyToLibrary P S).value =
        (Strategy.ofStrategy (lowDegreeStrategyToLibrary P S)).value
          (Game.ofGame (MIPStarRE.QPBT.ldGame P)) :=
      (Strategy.value_ofStrategy (lowDegreeStrategyToLibrary P S)).symm
    _ = S'.value (Game.ofGame (MIPStarRE.QPBT.ldGame P)) := by
      simp [lowDegreeStrategyToLibrary, S']
      rfl
    _ = S'.value (Game.relabel
        (lowDegreeGame (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model))
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P)) := by
      rw [lowDegreeGame_relabel_eq]
      rfl
    _ = S.value (lowDegreeGame (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)) :=
      Strategy.value_relabel _ _ _ _ _ _

/-- Conversion to the registered low-degree game preserves projectivity exactly. -/
theorem lowDegreeStrategyToLibrary_isProjective_iff (P : MIPStarRE.QPBT.LdParams)
    (S : Strategy
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))
      (LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P))) :
    (lowDegreeStrategyToLibrary P S).IsProjective ↔ S.IsProjective := by
  change (Strategy.toStrategy (G := MIPStarRE.QPBT.ldGame P)
      (Strategy.relabel S
        (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)
        (lowDegreeAnswerEquiv P) (lowDegreeAnswerEquiv P))).IsProjective ↔
    S.IsProjective
  rw [Strategy.isProjective_toStrategy_iff]
  exact Strategy.relabel_isProjective_iff _ _ _ _ _

end

end MIPStarRE.QPBT.Palomar
