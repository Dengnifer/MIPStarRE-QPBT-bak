module

public import MIPStarRE.QPBT.Palomar.PauliGameBridge
public import MIPStarRE.QPBT.Palomar.LowDegreeGameStrategyBridge
public import MIPStarRE.QPBT.Test.Completeness

/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

local instance compactPauliQuestionDecidableEq
    (P : MIPStarRE.QPBT.AdmissibleParams) :
    DecidableEq
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :=
  instDecidableEqPauliQuestion

namespace PMF

/-- Pushing a PMF through an equivalence preserves its mass at corresponding points. -/
@[simp] theorem map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (x : X) :
    (p.map e) (e x) = p x := by
  classical
  simp [PMF.map_apply, e.injective.eq_iff]

/-- A PMF pushed through an equivalence is evaluated by pulling the point back. -/
theorem map_equiv_apply' {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  simpa only [e.apply_symm_apply] using map_equiv_apply p e (e.symm y)

end PMF

namespace POVM

/-- Outcome relabeling preserves state-dependent consistency exactly. -/
theorem relabel_isConsistentOn_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (e : A ≃ B) (M : POVM A I) (ψ : EuclideanSpace ℂ (I × I)) :
    (relabel e M).IsConsistentOn ψ ↔ M.IsConsistentOn ψ := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    exact h (e.symm b)

end POVM

/-- Positive-support commutation is invariant under exact question and outcome relabeling. -/
theorem isCommutingOn_relabel_iff
    {X Y A B X' Y' A' B' I : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [Fintype I] [DecidableEq I]
    (μ : PMF (X × Y)) (alice : X → POVM A I) (bob : Y → POVM B I)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    IsCommutingOn (μ.map (Equiv.prodCongr eX eY))
        (fun x => POVM.relabel eA (alice (eX.symm x)))
        (fun y => POVM.relabel eB (bob (eY.symm y))) ↔
      IsCommutingOn μ alice bob := by
  constructor
  · intro h x y hxy a b
    have hxy' : 0 < (μ.map (Equiv.prodCongr eX eY)) (eX x, eY y) := by
      rw [show (eX x, eY y) = (Equiv.prodCongr eX eY) (x, y) by rfl]
      simpa only [PMF.map_equiv_apply] using hxy
    simpa using h (eX x) (eY y) hxy' (eA a) (eB b)
  · intro h x y hxy a b
    have hxy' : 0 < μ (eX.symm x, eY.symm y) := by
      rw [PMF.map_equiv_apply'] at hxy
      simpa using hxy
    simpa using h (eX.symm x) (eY.symm y) hxy' (eA.symm a) (eB.symm b)

namespace Game

/-- Relabeling a compact game and then relabeling by the inverse equivalences is exact. -/
theorem relabel_symm_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y')
    (eA : A ≃ A') (eB : B ≃ B') :
    Game.relabel (Game.relabel G eX eY eA eB)
        eX.symm eY.symm eA.symm eB.symm = G := by
  apply Game.ext
  · ext xy
    change ((G.μ.map (Equiv.prodCongr eX eY)).map
      (Equiv.prodCongr eX.symm eY.symm)) xy = G.μ xy
    rw [PMF.map_equiv_apply']
    change (G.μ.map (Equiv.prodCongr eX eY))
      ((Equiv.prodCongr eX eY) xy) = G.μ xy
    exact PMF.map_equiv_apply G.μ (Equiv.prodCongr eX eY) xy
  · funext x y a b
    simp [Game.relabel]

end Game

namespace SymmetricGame

/-- Relabel the questions and answers of a compact symmetric game. -/
def relabel {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq X] [DecidableEq A] [DecidableEq X'] [DecidableEq A']
    (G : SymmetricGame X A) (eX : X ≃ X') (eA : A ≃ A') :
    SymmetricGame X' A' where
  toGame := Game.relabel G.toGame eX eX eA eA
  μ_symm := by
    intro x y
    change (G.μ.map (Equiv.prodCongr eX eX)) (x, y) =
      (G.μ.map (Equiv.prodCongr eX eX)) (y, x)
    rw [PMF.map_equiv_apply', PMF.map_equiv_apply']
    exact G.μ_symm (eX.symm x) (eX.symm y)
  decide_symm := by
    intro x y a b
    exact G.decide_symm (eX.symm x) (eX.symm y) (eA.symm a) (eA.symm b)

end SymmetricGame

namespace SymmetricStrategy

/-- Relabel the questions and outcomes of a compact symmetric strategy. -/
def relabel {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    SymmetricStrategy X' A' where
  ι := S.ι
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  ψ_swap := S.ψ_swap
  meas := fun x => POVM.relabel eA (S.meas (eX.symm x))

/-- Symmetric relabeling agrees with relabeling the underlying general strategy. -/
@[simp] theorem relabel_toStrategy {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (relabel S eX eA).toStrategy =
      Strategy.relabel S.toStrategy eX eX eA eA :=
  rfl

/-- Symmetric relabeling preserves projectivity of the measurement family exactly. -/
theorem relabel_isProjective_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (∀ x, ((relabel S eX eA).meas x).IsProjective) ↔
      ∀ x, (S.meas x).IsProjective := by
  constructor
  · intro h x
    have hx := h (eX x)
    change (POVM.relabel eA (S.meas (eX.symm (eX x)))).IsProjective at hx
    rw [eX.symm_apply_apply] at hx
    exact (POVM.relabel_isProjective_iff eA (S.meas x)).mp hx
  · intro h x
    exact (POVM.relabel_isProjective_iff eA (S.meas (eX.symm x))).mpr
      (h (eX.symm x))

/-- Symmetric relabeling preserves consistency exactly. -/
theorem relabel_isConsistent_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq A] [DecidableEq A']
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (relabel S eX eA).IsConsistent ↔ S.IsConsistent := by
  constructor
  · intro h x
    have hx := h (eX x)
    change (POVM.relabel eA (S.meas (eX.symm (eX x)))).IsConsistentOn S.ψ at hx
    rw [eX.symm_apply_apply] at hx
    exact (POVM.relabel_isConsistentOn_iff eA (S.meas x) S.ψ).mp hx
  · intro h x
    exact (POVM.relabel_isConsistentOn_iff eA (S.meas (eX.symm x)) S.ψ).mpr
      (h (eX.symm x))

/-- Symmetric relabeling preserves the SPCC predicate under the exact PMF push-forward. -/
theorem relabel_isSPCC_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq X] [DecidableEq A] [DecidableEq X'] [DecidableEq A']
    (G : SymmetricGame X A) (G' : SymmetricGame X' A')
    (S : SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A')
    (hμ : G.μ.map (Equiv.prodCongr eX eX) = G'.μ) :
    (relabel S eX eA).IsSPCC G' ↔ S.IsSPCC G := by
  rw [SymmetricStrategy.IsSPCC, SymmetricStrategy.IsSPCC, ← hμ]
  constructor
  · rintro ⟨hproj, hcons, hcomm⟩
    exact ⟨(relabel_isProjective_iff S eX eA).mp hproj,
      (relabel_isConsistent_iff S eX eA).mp hcons,
      (isCommutingOn_relabel_iff G.μ S.meas S.meas eX eX eA eA).mp hcomm⟩
  · rintro ⟨hproj, hcons, hcomm⟩
    exact ⟨(relabel_isProjective_iff S eX eA).mpr hproj,
      (relabel_isConsistent_iff S eX eA).mpr hcons,
      (isCommutingOn_relabel_iff G.μ S.meas S.meas eX eX eA eA).mpr hcomm⟩

end SymmetricStrategy

/-- Relabeling the concrete compact Pauli game gives the registered game exactly. -/
theorem pauliGame_relabel_eq (P : MIPStarRE.QPBT.AdmissibleParams) :
    Game.relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P) =
      Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P) := by
  apply Game.ext
  · exact pauliQuestionPMF_map P
  · funext x y a b
    change pauliWin (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model)
        ((pauliQuestionEquiv P).symm x) ((pauliQuestionEquiv P).symm y)
        ((pauliAnswerEquivCompact P).symm a) ((pauliAnswerEquivCompact P).symm b) =
      MIPStarRE.QPBT.pauliWinPredicate P x y a b
    simpa using pauliWin_equiv P
      ((pauliQuestionEquiv P).symm x) ((pauliQuestionEquiv P).symm y)
      ((pauliAnswerEquivCompact P).symm a) ((pauliAnswerEquivCompact P).symm b)

/-- Convert a compact Pauli strategy into a strategy for the registered game. -/
def pauliStrategyToLibrary (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : Strategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    MIPStarRE.QPBT.Strategy (MIPStarRE.QPBT.pauliBasisTest P) :=
  Strategy.toStrategy (G := MIPStarRE.QPBT.pauliBasisTest P)
    (Strategy.relabel S
      (pauliQuestionEquiv P) (pauliQuestionEquiv P)
      (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P))

/-- Conversion to the registered Pauli game preserves strategy value exactly. -/
theorem pauliStrategyToLibrary_value (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : Strategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    (pauliStrategyToLibrary P S).value =
      S.value (pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model)) := by
  let S' := Strategy.relabel S
    (pauliQuestionEquiv P) (pauliQuestionEquiv P)
    (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)
  calc
    (pauliStrategyToLibrary P S).value =
        (Strategy.ofStrategy (pauliStrategyToLibrary P S)).value
          (Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P)) :=
      (Strategy.value_ofStrategy (pauliStrategyToLibrary P S)).symm
    _ = S'.value (Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P)) := by
      simp [pauliStrategyToLibrary, S']
    _ = S'.value (Game.relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)) := by
      rw [pauliGame_relabel_eq]
    _ = S.value (pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model)) :=
      Strategy.value_relabel _ _ _ _ _ _

/-- Conversion to the registered Pauli game preserves projectivity exactly. -/
theorem pauliStrategyToLibrary_isProjective_iff
    (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : Strategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    (pauliStrategyToLibrary P S).IsProjective ↔ S.IsProjective := by
  change (Strategy.toStrategy (G := MIPStarRE.QPBT.pauliBasisTest P)
      (Strategy.relabel S
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P))).IsProjective ↔
    S.IsProjective
  rw [Strategy.isProjective_toStrategy_iff]
  exact Strategy.relabel_isProjective_iff _ _ _ _ _

/-- The compact Pauli game has the exact symmetric presentation transported from the source. -/
noncomputable def pauliSymmetricGame (P : MIPStarRE.QPBT.AdmissibleParams) :
    SymmetricGame
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :=
  SymmetricGame.relabel
    (SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm P))
    (pauliQuestionEquiv P).symm (pauliAnswerEquivCompact P).symm

/-- The symmetric compact presentation has the compact Pauli game as its underlying game. -/
@[simp] theorem pauliSymmetricGame_toGame (P : MIPStarRE.QPBT.AdmissibleParams) :
    (pauliSymmetricGame P).toGame =
      pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model) := by
  calc
    (pauliSymmetricGame P).toGame =
        Game.relabel (Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P))
          (pauliQuestionEquiv P).symm (pauliQuestionEquiv P).symm
          (pauliAnswerEquivCompact P).symm (pauliAnswerEquivCompact P).symm := rfl
    _ = Game.relabel (Game.relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P))
          (pauliQuestionEquiv P).symm (pauliQuestionEquiv P).symm
          (pauliAnswerEquivCompact P).symm
          (pauliAnswerEquivCompact P).symm := by
      rw [pauliGame_relabel_eq]
    _ = pauliGame (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model) :=
      Game.relabel_symm_relabel _ _ _ _ _

/-- Convert a compact symmetric Pauli strategy into a registered symmetric strategy. -/
def pauliSymmetricStrategyToLibrary (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricStrategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    MIPStarRE.QPBT.SymmetricStrategy (MIPStarRE.QPBT.pauliBasisTestSymm P) :=
  SymmetricStrategy.toSymmetricStrategy
    (SymmetricStrategy.relabel S (pauliQuestionEquiv P) (pauliAnswerEquivCompact P))

/-- Symmetric conversion is exactly the relabeled compact symmetric strategy. -/
@[simp] theorem of_pauliSymmetricStrategyToLibrary
    (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricStrategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    SymmetricStrategy.ofSymmetricStrategy (pauliSymmetricStrategyToLibrary P S) =
      SymmetricStrategy.relabel S (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) := by
  simp [pauliSymmetricStrategyToLibrary]
  rfl

/-- Symmetric conversion preserves the strategy value exactly. -/
theorem pauliSymmetricStrategyToLibrary_value
    (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricStrategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    (pauliSymmetricStrategyToLibrary P S).toStrategy.value =
      S.toStrategy.value (pauliSymmetricGame P).toGame := by
  let T := pauliSymmetricStrategyToLibrary P S
  let S' := SymmetricStrategy.relabel S (pauliQuestionEquiv P)
    (pauliAnswerEquivCompact P)
  calc
    T.toStrategy.value =
        (SymmetricStrategy.ofSymmetricStrategy T).toStrategy.value
          (SymmetricGame.ofSymmetricGame
            (MIPStarRE.QPBT.pauliBasisTestSymm P)).toGame :=
      (SymmetricStrategy.value_ofSymmetricStrategy T).symm
    _ = S'.toStrategy.value (Game.ofGame (MIPStarRE.QPBT.pauliBasisTest P)) := by
      rw [show SymmetricStrategy.ofSymmetricStrategy T = S' by
        simp [T, S']
        rfl]
      rfl
    _ = S'.toStrategy.value (Game.relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)) := by
      rw [pauliGame_relabel_eq]
    _ = S.toStrategy.value (pauliSymmetricGame P).toGame := by
      rw [pauliSymmetricGame_toGame]
      change (Strategy.relabel S.toStrategy
          (pauliQuestionEquiv P) (pauliQuestionEquiv P)
          (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)).value
          (Game.relabel
            (pauliGame (PauliParams.ofAdmissibleParams P)
              (MIPStarRE.QPBT.binaryRepresentation P.model)
              (MIPStarRE.QPBT.fixedBinTrace P.model))
            (pauliQuestionEquiv P) (pauliQuestionEquiv P)
            (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)) =
        S.toStrategy.value
          (pauliGame (PauliParams.ofAdmissibleParams P)
            (MIPStarRE.QPBT.binaryRepresentation P.model)
            (MIPStarRE.QPBT.fixedBinTrace P.model))
      exact Strategy.value_relabel
        (pauliGame (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          (MIPStarRE.QPBT.fixedBinTrace P.model))
        S.toStrategy (pauliQuestionEquiv P) (pauliQuestionEquiv P)
        (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)

/-- Symmetric conversion preserves projectivity, consistency, and support commutation exactly. -/
theorem pauliSymmetricStrategyToLibrary_isSPCC_iff
    (P : MIPStarRE.QPBT.AdmissibleParams)
    (S : SymmetricStrategy
      (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))
      (PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P))) :
    (pauliSymmetricStrategyToLibrary P S).IsSPCC ↔
      S.IsSPCC (pauliSymmetricGame P) := by
  rw [← SymmetricStrategy.isSPCC_ofSymmetricStrategy_iff
    (pauliSymmetricStrategyToLibrary P S)]
  change (SymmetricStrategy.relabel S (pauliQuestionEquiv P)
      (pauliAnswerEquivCompact P)).IsSPCC
        (SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm P)) ↔
    S.IsSPCC (pauliSymmetricGame P)
  apply SymmetricStrategy.relabel_isSPCC_iff
  rw [pauliSymmetricGame_toGame]
  exact pauliQuestionPMF_map P

end

end MIPStarRE.QPBT.Palomar
