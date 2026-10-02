module

public import MIPStarRE.QPBT.Palomar.LowDegreeGame
public import MIPStarRE.QPBT.Palomar.Bridge
public import MIPStarRE.QPBT.Test.LowDegreeGameMeasurements

/-!
# Exact bridge for the compact low individual degree game

This module identifies the compact product-space game with the existing
low-degree game.  The bridge is by explicit equivalences of question
coordinates and answer summands.  It preserves the question PMF, every branch
of the Boolean verifier, and the value of every compact strategy exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT

/-- Copy the original numerical parameter record into the compact domain. -/
@[reducible] def LowDegreeParams.ofLdParams
    (P : MIPStarRE.QPBT.LdParams) : LowDegreeParams where
  q := P.q
  m := P.m
  d := P.d
  k := P.k
  hm := P.hm
  hd := P.hd
  hk := P.hk
  hq := P.hq
  hdvd := P.hdvd

/-- The compact and original three-element question-type carriers are equivalent. -/
def lowDegreeTypeEquiv : LowDegreeType ≃ MIPStarRE.QPBT.LdType where
  toFun
    | .point => .point
    | .aline => .aline
    | .dline => .dline
  invFun
    | .point => .point
    | .aline => .aline
    | .dline => .dline
  left_inv t := by cases t <;> rfl
  right_inv t := by cases t <;> rfl

/-- Split-function coordinates identify the complete compact and original spaces. -/
def lowDegreeSpaceEquiv (P : MIPStarRE.QPBT.LdParams) :
    LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P) ≃
      MIPStarRE.QPBT.LdSpace P :=
  (MIPStarRE.QPBT.ldSpaceSplit P).symm

/-- Typed questions are equivalent by the explicit type and coordinate maps. -/
def lowDegreeQuestionEquiv (P : MIPStarRE.QPBT.LdParams) :
    LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P) ≃
      MIPStarRE.QPBT.LdQuestion P :=
  Equiv.prodCongr lowDegreeTypeEquiv (lowDegreeSpaceEquiv P)

/-- The three answer summands are exactly the original answer constructors. -/
@[reducible] noncomputable def lowDegreeAnswerEquiv (P : MIPStarRE.QPBT.LdParams) :
    LowDegreeAnswer (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P) ≃
      MIPStarRE.QPBT.LdAnswer P :=
  (MIPStarRE.QPBT.ldAnswerEquiv P).symm

/-- The complete common-source spaces are equivalent coordinate by coordinate. -/
def lowDegreeSourceEquiv (P : MIPStarRE.QPBT.LdParams) :
    ((LowDegreeType × LowDegreeType) ×
        LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) ≃
      ((MIPStarRE.QPBT.LdType × MIPStarRE.QPBT.LdType) ×
        MIPStarRE.QPBT.LdSpace P) :=
  Equiv.prodCongr (Equiv.prodCongr lowDegreeTypeEquiv lowDegreeTypeEquiv)
    (lowDegreeSpaceEquiv P)

/-- Equivalence of the two ordered question-pair carriers. -/
def lowDegreeQuestionPairEquiv (P : MIPStarRE.QPBT.LdParams) :
    (LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P) ×
        LowDegreeQuestion (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) ≃
      (MIPStarRE.QPBT.LdQuestion P × MIPStarRE.QPBT.LdQuestion P) :=
  Equiv.prodCongr (lowDegreeQuestionEquiv P) (lowDegreeQuestionEquiv P)

/-- The compact seed-index map is the original `chiIndex`. -/
@[simp] theorem lowDegreeChiIndex_eq (P : MIPStarRE.QPBT.LdParams)
    (s : MIPStarRE.QPBT.ScalarQ P) :
    lowDegreeChiIndex (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) s =
      MIPStarRE.QPBT.chiIndex P s := by
  rfl

/-- The compact prefix projection is the original prefix projection. -/
@[simp] theorem lowDegreePrefix_eq (P : MIPStarRE.QPBT.LdParams)
    (i : Fin P.m) (v : Fin P.m → MIPStarRE.QPBT.ScalarQ P) :
    lowDegreePrefix i v = MIPStarRE.QPBT.prefixProjection i v :=
  rfl

/-- The compact least nonzero coordinate is the one used by the published formula. -/
theorem lowDegreePivot_eq_linePivotIndex {K : Type} [Field K] [DecidableEq K]
    {m : ℕ} (v : Fin m → K) (hv : v ≠ 0) :
    lowDegreePivot v hv = MIPStarRE.QPBT.linePivotIndex v hv := by
  have hpivot_ne : v (lowDegreePivot v hv) ≠ 0 := by
    unfold lowDegreePivot
    change v ((Finset.univ.filter fun j : Fin m => v j ≠ 0).min' _) ≠ 0
    exact (Finset.mem_filter.mp (Finset.min'_mem
      (Finset.univ.filter fun j : Fin m => v j ≠ 0) _)).2
  have hpivot_le (i : Fin m) (hi : v i ≠ 0) : lowDegreePivot v hv ≤ i := by
    unfold lowDegreePivot
    change (Finset.univ.filter fun j : Fin m => v j ≠ 0).min' _ ≤ i
    exact Finset.min'_le _ i (by simp [hi])
  apply le_antisymm
  · exact hpivot_le _ (MIPStarRE.QPBT.linePivotIndex_ne_zero v hv)
  · apply le_of_not_gt
    intro hlt
    exact hpivot_ne (MIPStarRE.QPBT.linePivotIndex_zero_before v hv _ hlt)

/-- The compact elementary representative is exactly the canonical representative. -/
theorem lowDegreeLineRep_eq_lineRepMap {K : Type} [Field K] [DecidableEq K]
    {m : ℕ} (u v : Fin m → K) :
    lowDegreeLineRep u v = MIPStarRE.QPBT.lineRepMap v u := by
  rw [MIPStarRE.QPBT.lineRepMap_apply_eq_explicitLineRep]
  simp only [lowDegreeLineRep, MIPStarRE.QPBT.explicitLineRep]
  split_ifs with hv
  · rfl
  · rw [lowDegreePivot_eq_linePivotIndex v hv]

/-- The compact point map agrees with the original point map. -/
theorem lowDegreeMap_point_equiv (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    lowDegreeSpaceEquiv P
        (lowDegreeMap (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          .point z) =
      MIPStarRE.QPBT.ldPointCL P (lowDegreeSpaceEquiv P z) := by
  rfl

/-- The compact axis-line map agrees with the original axis-line map. -/
theorem lowDegreeMap_aline_equiv (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    lowDegreeSpaceEquiv P
        (lowDegreeMap (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          .aline z) =
      MIPStarRE.QPBT.ldALineCL P (lowDegreeSpaceEquiv P z) := by
  funext i
  rcases i with (j | u) | j
  · change lowDegreeLineRep z.1.1
        (Pi.single (MIPStarRE.QPBT.chiIndex P z.1.2) 1) j =
      MIPStarRE.QPBT.lineRepMap
        (MIPStarRE.QPBT.coordinateDirection (MIPStarRE.QPBT.chiIndex P z.1.2))
        z.1.1 j
    rw [lowDegreeLineRep_eq_lineRepMap]
    rfl
  · cases u
    rfl
  · rfl

/-- The compact diagonal-line map agrees with the original diagonal-line map. -/
theorem lowDegreeMap_dline_equiv (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    lowDegreeSpaceEquiv P
        (lowDegreeMap (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model)
          .dline z) =
      MIPStarRE.QPBT.ldDLineCL P (lowDegreeSpaceEquiv P z) := by
  funext i
  rcases i with (j | u) | j
  · change lowDegreeLineRep z.1.1
        (MIPStarRE.QPBT.prefixProjection
          (MIPStarRE.QPBT.chiIndex P z.1.2) z.2) j =
      MIPStarRE.QPBT.lineRepMap
        (MIPStarRE.QPBT.prefixProjection
          (MIPStarRE.QPBT.chiIndex P z.1.2) z.2) z.1.1 j
    rw [lowDegreeLineRep_eq_lineRepMap]
  · cases u
    rfl
  · rfl

/-- All three compact question maps commute with the coordinate equivalence. -/
theorem lowDegreeMap_equiv (P : MIPStarRE.QPBT.LdParams)
    (t : LowDegreeType)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    lowDegreeSpaceEquiv P
        (lowDegreeMap (LowDegreeParams.ofLdParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model) t z) =
      MIPStarRE.QPBT.ldCL P (lowDegreeTypeEquiv t) (lowDegreeSpaceEquiv P z) := by
  cases t with
  | point => exact lowDegreeMap_point_equiv P z
  | aline => exact lowDegreeMap_aline_equiv P z
  | dline => exact lowDegreeMap_dline_equiv P z

/-- The compact question PMF is exactly the original question distribution. -/
theorem lowDegreeQuestionPMF_map (P : MIPStarRE.QPBT.LdParams) :
    (lowDegreeQuestionPMF (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)).map
        (lowDegreeQuestionPairEquiv P) =
      (MIPStarRE.QPBT.ldGame P).μ.toPMF (MIPStarRE.QPBT.ldGame P).μ_prob := by
  let compactMap := fun z :
      (LowDegreeType × LowDegreeType) ×
        LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P) =>
    ((z.1.1, lowDegreeMap (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) z.1.1 z.2),
      (z.1.2, lowDegreeMap (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) z.1.2 z.2))
  let originalMap := fun z :
      (MIPStarRE.QPBT.LdType × MIPStarRE.QPBT.LdType) ×
        MIPStarRE.QPBT.LdSpace P =>
    ((z.1.1, MIPStarRE.QPBT.ldCL P z.1.1 z.2),
      (z.1.2, MIPStarRE.QPBT.ldCL P z.1.2 z.2))
  have hcomm : lowDegreeQuestionPairEquiv P ∘ compactMap =
      originalMap ∘ lowDegreeSourceEquiv P := by
    funext z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact lowDegreeMap_equiv P z.1.1 z.2
    · apply Prod.ext
      · rfl
      · exact lowDegreeMap_equiv P z.1.2 z.2
  rw [show lowDegreeQuestionPMF (LowDegreeParams.ofLdParams P)
      (MIPStarRE.QPBT.binaryRepresentation P.model) =
        (PMF.uniformOfFintype _).map compactMap by rfl]
  rw [PMF.map_comp, hcomm, ← PMF.map_comp]
  rw [PMF.uniformOfFintype_map_equiv (lowDegreeSourceEquiv P)]
  have hmap :=
    (MIPStarRE.LDT.Distribution.toPMF_map
      (MIPStarRE.LDT.uniformDistribution
        ((MIPStarRE.QPBT.LdType × MIPStarRE.QPBT.LdType) ×
          MIPStarRE.QPBT.LdSpace P))
      (MIPStarRE.LDT.uniformDistribution_isProbability
        ((MIPStarRE.QPBT.LdType × MIPStarRE.QPBT.LdType) ×
          MIPStarRE.QPBT.LdSpace P)) originalMap).symm
  rw [MIPStarRE.LDT.uniformDistribution_toPMF] at hmap
  simpa only [MIPStarRE.QPBT.ldGame, MIPStarRE.QPBT.ldQuestionDistribution] using hmap

/-- Polynomial coefficient evaluation is unchanged by the compact presentation. -/
@[simp] theorem lowDegreeEval_eq_evalCoefficient {K : Type} [Semiring K]
    {n : ℕ} (c : Fin n → K) (t : K) :
    lowDegreeEval c t = MIPStarRE.QPBT.evalCoefficient c t :=
  rfl

/-- The point block of the transported ambient vector is unchanged. -/
@[simp] theorem lowDegreeSpaceEquiv_point (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    MIPStarRE.QPBT.LdSpace.point (lowDegreeSpaceEquiv P z) = z.1.1 := by
  rfl

/-- The scalar seed of the transported ambient vector is unchanged. -/
@[simp] theorem lowDegreeSpaceEquiv_seed (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    MIPStarRE.QPBT.LdSpace.seed (lowDegreeSpaceEquiv P z) = z.1.2 := by
  rfl

/-- The direction block of the transported ambient vector is unchanged. -/
@[simp] theorem lowDegreeSpaceEquiv_direction (P : MIPStarRE.QPBT.LdParams)
    (z : LowDegreeSpace (LowDegreeParams.ofLdParams P) (MIPStarRE.QPBT.ScalarQ P)) :
    MIPStarRE.QPBT.LdSpace.direction (lowDegreeSpaceEquiv P z) = z.2 := by
  rfl

/-- Point-value answers map to the original point-value constructor. -/
@[simp] theorem lowDegreeAnswerEquiv_point (P : MIPStarRE.QPBT.LdParams)
    (a : Fin P.k → MIPStarRE.QPBT.ScalarQ P) :
    lowDegreeAnswerEquiv P (.inl a) = .pointVals a := by
  rfl

/-- Axis-line answers map to the original axis-line constructor. -/
@[simp] theorem lowDegreeAnswerEquiv_aline (P : MIPStarRE.QPBT.LdParams)
    (a : Fin P.k → Fin (P.d + 1) → MIPStarRE.QPBT.ScalarQ P) :
    lowDegreeAnswerEquiv P (.inr (.inl a)) = .alinePolys a := by
  rfl

/-- Diagonal-line answers map to the original diagonal-line constructor. -/
@[simp] theorem lowDegreeAnswerEquiv_dline (P : MIPStarRE.QPBT.LdParams)
    (a : Fin P.k → Fin (P.m * P.d + 1) → MIPStarRE.QPBT.ScalarQ P) :
    lowDegreeAnswerEquiv P (.inr (.inr a)) = .dlinePolys a := by
  rfl

/-- The compact Boolean verifier is exactly the original verifier after relabeling. -/
theorem lowDegreeWin_equiv (P : MIPStarRE.QPBT.LdParams)
    (x y : LowDegreeQuestion (LowDegreeParams.ofLdParams P)
      (MIPStarRE.QPBT.ScalarQ P))
    (a b : LowDegreeAnswer (LowDegreeParams.ofLdParams P)
      (MIPStarRE.QPBT.ScalarQ P)) :
    lowDegreeWin (LowDegreeParams.ofLdParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) x y a b =
      MIPStarRE.QPBT.ldWinPredicate P (lowDegreeQuestionEquiv P x)
        (lowDegreeQuestionEquiv P y) (lowDegreeAnswerEquiv P a)
        (lowDegreeAnswerEquiv P b) := by
  rcases x with ⟨tA, xA⟩
  rcases y with ⟨tB, xB⟩
  rcases a with a | (a | a) <;>
    rcases b with b | (b | b) <;>
      cases tA <;> cases tB <;>
        simp [lowDegreeWin, validLowDegreeAnswer, MIPStarRE.QPBT.ldWinPredicate,
          MIPStarRE.QPBT.validLdAnswer, lowDegreeQuestionEquiv,
          lowDegreeAnswerEquiv, MIPStarRE.QPBT.ldAnswerEquiv,
          lowDegreeTypeEquiv, MIPStarRE.QPBT.alinePointCondition,
          MIPStarRE.QPBT.dlinePointCondition, MIPStarRE.QPBT.coordinateDirection] <;>
        rfl

end MIPStarRE.QPBT.Palomar
