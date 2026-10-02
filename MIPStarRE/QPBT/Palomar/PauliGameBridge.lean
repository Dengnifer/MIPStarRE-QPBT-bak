module

public import MIPStarRE.QPBT.Palomar.PauliGame
public import MIPStarRE.QPBT.Palomar.LowDegreeGameBridge
public import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Exact bridge for the compact Pauli basis game

This module identifies the compact product-space presentation with the
registered Pauli basis test.  The bridge preserves the fixed field model, all
ordered edges, the full ambient seed, every answer constructor, the question
PMF, and every branch of the Boolean verifier.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- Copy the registered Pauli parameters into the compact numerical domain. -/
@[reducible] def PauliParams.ofAdmissibleParams
    (P : MIPStarRE.QPBT.AdmissibleParams) : PauliParams where
  q := P.q
  m := P.m
  d := P.d
  hm := P.one_le_m
  hd := P.hd
  hq := P.hq
  hdvd := P.hdvd

/-- The compact and registered Pauli-basis labels are equivalent. -/
def pauliKindEquiv : PauliKind ≃ MIPStarRE.QPBT.PauliKind where
  toFun
    | .X => .X
    | .Z => .Z
  invFun
    | .X => .X
    | .Z => .Z
  left_inv W := by cases W <;> rfl
  right_inv W := by cases W <;> rfl

/-- The compact 26-element type carrier is the registered Pauli type carrier. -/
def pauliTypeEquiv : PauliType ≃ MIPStarRE.QPBT.PauliType where
  toFun
    | .point W => .point (pauliKindEquiv W)
    | .aline W => .aline (pauliKindEquiv W)
    | .dline W => .dline (pauliKindEquiv W)
    | .pauli W => .pauli (pauliKindEquiv W)
    | .pairW W => .pairW (pauliKindEquiv W)
    | .pair => .pair
    | .constraint i => .ms (.constraint i)
    | .variable j => .ms (.var j)
  invFun
    | .point W => .point (pauliKindEquiv.symm W)
    | .aline W => .aline (pauliKindEquiv.symm W)
    | .dline W => .dline (pauliKindEquiv.symm W)
    | .pauli W => .pauli (pauliKindEquiv.symm W)
    | .pairW W => .pairW (pauliKindEquiv.symm W)
    | .pair => .pair
    | .ms (.constraint i) => .constraint i
    | .ms (.var j) => .variable j
  left_inv
    | .point W => by cases W <;> rfl
    | .aline W => by cases W <;> rfl
    | .dline W => by cases W <;> rfl
    | .pauli W => by cases W <;> rfl
    | .pairW W => by cases W <;> rfl
    | .pair => rfl
    | .constraint _ => rfl
    | .variable _ => rfl
  right_inv
    | .point W => by cases W <;> rfl
    | .aline W => by cases W <;> rfl
    | .dline W => by cases W <;> rfl
    | .pauli W => by cases W <;> rfl
    | .pairW W => by cases W <;> rfl
    | .pair => rfl
    | .ms t => by cases t <;> rfl

/-- Product coordinates identify the full compact and registered ambient spaces. -/
def pauliSpaceEquiv (P : MIPStarRE.QPBT.AdmissibleParams) :
    PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P) ≃
      MIPStarRE.QPBT.PauliSpace P where
  toFun z
    | .inl (.inl (.inl (.inl (.inl i)))) => z.1 i
    | .inl (.inl (.inl (.inl (.inr i)))) => z.2.1 i
    | .inl (.inl (.inl (.inr _))) => z.2.2.1
    | .inl (.inl (.inr i)) => z.2.2.2.1 i
    | .inl (.inr _) => z.2.2.2.2.1
    | .inr _ => z.2.2.2.2.2
  invFun z :=
    (MIPStarRE.QPBT.pauliXBlock z, MIPStarRE.QPBT.pauliZBlock z,
      MIPStarRE.QPBT.pauliScalarBlock z, MIPStarRE.QPBT.pauliDirectionBlock z,
      MIPStarRE.QPBT.pauliRXBlock z, MIPStarRE.QPBT.pauliRZBlock z)
  left_inv z := by
    rcases z with ⟨uX, uZ, s, v, rX, rZ⟩
    rfl
  right_inv z := by
    funext i
    rcases i with ((((i | i) | u) | i) | u) | u <;> rfl

/-- Typed compact questions are equivalent to registered Pauli questions. -/
def pauliQuestionEquiv (P : MIPStarRE.QPBT.AdmissibleParams) :
    PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P) ≃
      MIPStarRE.QPBT.PauliQuestion P :=
  Equiv.prodCongr pauliTypeEquiv (pauliSpaceEquiv P)

/-- All seven compact answer constructors map to their registered counterparts. -/
def pauliAnswerEquivCompact (P : MIPStarRE.QPBT.AdmissibleParams) :
    PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P) ≃
      MIPStarRE.QPBT.PauliAnswer P where
  toFun
    | .value a => .value a
    | .alinePoly a => .alinePoly a
    | .dlinePoly a => .dlinePoly a
    | .pairBits a => .pairBits a
    | .bit a => .bit a
    | .msTriple a => .msTriple a
    | .pauliOutcome a => .pauliOutcome a
  invFun
    | .value a => .value a
    | .alinePoly a => .alinePoly a
    | .dlinePoly a => .dlinePoly a
    | .pairBits a => .pairBits a
    | .bit a => .bit a
    | .msTriple a => .msTriple a
    | .pauliOutcome a => .pauliOutcome a
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- The compact and registered Magic Square incidence maps coincide. -/
@[simp] theorem magicVariable_eq_msConstraintVars (i : Fin 6) (j : Fin 3) :
    magicVariable i j = MIPStarRE.QPBT.msConstraintVars i j :=
  rfl

/-- The registered filtered Magic Square carrier is its direct 18-edge image. -/
theorem registeredMagicEdges_eq :
    ((Finset.univ : Finset (MIPStarRE.QPBT.MsType × MIPStarRE.QPBT.MsType)).filter
          (fun xy => Sym2.mk xy.1 xy.2 ∈ MIPStarRE.QPBT.msEdges) |>.image
        (fun xy => Sym2.mk (MIPStarRE.QPBT.PauliType.ms xy.1)
          (MIPStarRE.QPBT.PauliType.ms xy.2))) =
      (Finset.univ : Finset (Fin 6 × Fin 3)).image (fun ij =>
        Sym2.mk
          (MIPStarRE.QPBT.PauliType.ms (MIPStarRE.QPBT.MsType.constraint ij.1))
          (MIPStarRE.QPBT.PauliType.ms
            (MIPStarRE.QPBT.MsType.var
              (MIPStarRE.QPBT.msConstraintVars ij.1 ij.2)))) := by
  ext e
  simp only [MIPStarRE.QPBT.msEdges, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists, Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, hab, he⟩
    rcases hab with ⟨a', b', hab⟩
    rcases hab with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨a', b', he⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨a', b', Sym2.eq_swap.trans he⟩
  · rintro ⟨a, b, he⟩
    exact ⟨MIPStarRE.QPBT.MsType.constraint a,
      MIPStarRE.QPBT.MsType.var (MIPStarRE.QPBT.msConstraintVars a b),
      ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩, he⟩

/-- The registered graph written with the direct Magic Square edge image. -/
def registeredPauliEdgesDirect : Finset (Sym2 MIPStarRE.QPBT.PauliType) :=
  let loops := Finset.univ.image fun t : MIPStarRE.QPBT.PauliType => Sym2.mk t t
  let lines := (Finset.univ : Finset MIPStarRE.QPBT.PauliKind).image (fun W =>
      Sym2.mk (.point W) (.aline W)) ∪
    (Finset.univ : Finset MIPStarRE.QPBT.PauliKind).image (fun W =>
      Sym2.mk (.point W) (.dline W)) ∪
    (Finset.univ : Finset MIPStarRE.QPBT.PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pauli W))
  let basis := (Finset.univ : Finset MIPStarRE.QPBT.PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pairW W)) ∪
    ({Sym2.mk (.point .X) (.ms (.var 0)),
      Sym2.mk (.point .Z) (.ms (.var 4))} : Finset (Sym2 MIPStarRE.QPBT.PauliType))
  let pairs := (Finset.univ : Finset MIPStarRE.QPBT.PauliKind).image fun W =>
    Sym2.mk (.pairW W) .pair
  let magic := (Finset.univ : Finset (Fin 6 × Fin 3)).image fun ij =>
    Sym2.mk (.ms (.constraint ij.1))
      (.ms (.var (MIPStarRE.QPBT.msConstraintVars ij.1 ij.2)))
  loops ∪ lines ∪ basis ∪ pairs ∪ magic

/-- The direct-component presentation is exactly the registered graph. -/
theorem registeredPauliEdgesDirect_eq :
    MIPStarRE.QPBT.pauliEdges = registeredPauliEdgesDirect := by
  unfold MIPStarRE.QPBT.pauliEdges registeredPauliEdgesDirect
  rw [registeredMagicEdges_eq]
  simp

/-- Every compact edge maps to a registered edge. -/
theorem pauliEdges_map_mem {s : Sym2 PauliType} (h : s ∈ pauliEdges) :
    Sym2.map pauliTypeEquiv s ∈ MIPStarRE.QPBT.pauliEdges := by
  rw [registeredPauliEdgesDirect_eq]
  simp only [pauliEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ((((hloop | hlines) | hbasis) | hpairs) | hmagic)
  · rcases hloop with ⟨t, rfl⟩
    simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
  · rcases hlines with (h | h) | h
    · rcases h with ⟨W, rfl⟩
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with ⟨W, rfl⟩
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with ⟨W, rfl⟩
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
  · rcases hbasis with h | h | h
    · rcases h with ⟨W, rfl⟩
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with rfl
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with rfl
      simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
  · rcases hpairs with ⟨W, rfl⟩
    simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]
  · rcases hmagic with ⟨i, j, rfl⟩
    simp [registeredPauliEdgesDirect, pauliTypeEquiv, pauliKindEquiv]

/-- Every registered edge maps back to a compact edge. -/
theorem registeredPauliEdges_map_mem {s : Sym2 MIPStarRE.QPBT.PauliType}
    (h : s ∈ MIPStarRE.QPBT.pauliEdges) :
    Sym2.map pauliTypeEquiv.symm s ∈ pauliEdges := by
  rw [registeredPauliEdgesDirect_eq] at h
  simp only [registeredPauliEdgesDirect, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ((((hloop | hlines) | hbasis) | hpairs) | hmagic)
  · rcases hloop with ⟨t, rfl⟩
    simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
  · rcases hlines with (h | h) | h
    · rcases h with ⟨W, rfl⟩
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with ⟨W, rfl⟩
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with ⟨W, rfl⟩
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
  · rcases hbasis with h | h | h
    · rcases h with ⟨W, rfl⟩
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with rfl
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
    · rcases h with rfl
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
  · rcases hpairs with ⟨W, rfl⟩
    simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]
  · rcases hmagic with ⟨i, j, rfl⟩
    simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv]

/-- The compact type map preserves the complete undirected edge set. -/
theorem pauliEdges_mem_equiv (e : PauliType × PauliType) :
    Sym2.mk e.1 e.2 ∈ pauliEdges ↔
      Sym2.mk (pauliTypeEquiv e.1) (pauliTypeEquiv e.2) ∈
        MIPStarRE.QPBT.pauliEdges := by
  constructor
  · intro h
    simpa using pauliEdges_map_mem h
  · intro h
    have h' := registeredPauliEdges_map_mem h
    simpa using h'

/-- The compact and registered ordered-edge carriers are equivalent. -/
def pauliEdgeEquiv : PauliEdge ≃ MIPStarRE.QPBT.PauliEdge :=
  (Equiv.prodCongr pauliTypeEquiv pauliTypeEquiv).subtypeEquiv pauliEdges_mem_equiv

/-- The complete common-source spaces are equivalent coordinate by coordinate. -/
def pauliSourceEquiv (P : MIPStarRE.QPBT.AdmissibleParams) :
    (PauliEdge ×
        PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) ≃
      (MIPStarRE.QPBT.PauliEdge × MIPStarRE.QPBT.PauliSpace P) :=
  Equiv.prodCongr pauliEdgeEquiv (pauliSpaceEquiv P)

/-- Equivalence of the two ordered question-pair carriers. -/
def pauliQuestionPairEquiv (P : MIPStarRE.QPBT.AdmissibleParams) :
    (PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P) ×
        PauliQuestion (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) ≃
      (MIPStarRE.QPBT.PauliQuestion P × MIPStarRE.QPBT.PauliQuestion P) :=
  Equiv.prodCongr (pauliQuestionEquiv P) (pauliQuestionEquiv P)

/-- The compact Pauli parameters select exactly the registered low-degree tuple. -/
theorem pauliLowDegreeParams_eq (P : MIPStarRE.QPBT.AdmissibleParams) :
    (PauliParams.ofAdmissibleParams P).toLowDegreeParams =
      LowDegreeParams.ofLdParams P.toLdParams := by
  rfl

/-- The published low-degree map bridge specialized to the Pauli parameters. -/
theorem pauliLowDegreeMap_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (t : LowDegreeType)
    (z : LowDegreeSpace (PauliParams.ofAdmissibleParams P).toLowDegreeParams
      (MIPStarRE.QPBT.PauliScalar P)) :
    lowDegreeSpaceEquiv P.toLdParams
        (lowDegreeMap (PauliParams.ofAdmissibleParams P).toLowDegreeParams
          (MIPStarRE.QPBT.binaryRepresentation P.model) t z) =
      MIPStarRE.QPBT.ldCL P.toLdParams (lowDegreeTypeEquiv t)
        (lowDegreeSpaceEquiv P.toLdParams z) := by
  cases pauliLowDegreeParams_eq P
  exact lowDegreeMap_equiv P.toLdParams t z

/-- Reading the selected compact point block commutes with the space equivalence. -/
@[simp] theorem pauliSpaceEquiv_pointBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (W : PauliKind)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliPointBlock (pauliKindEquiv W) (pauliSpaceEquiv P z) =
      pauliPointBlock W z := by
  cases W <;> rfl

/-- Restriction to one low-degree block commutes with the coordinate equivalence. -/
theorem pauliLowDegreeSpace_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (W : PauliKind)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    lowDegreeSpaceEquiv P.toLdParams (pauliLowDegreeSpace W z) =
      MIPStarRE.QPBT.pauliToLd P (pauliKindEquiv W) (pauliSpaceEquiv P z) := by
  funext i
  rcases i with (i | u) | i <;> cases W <;> rfl

/-- Embedding one low-degree block commutes with the coordinate equivalence. -/
theorem pauliEmbedLowDegree_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (W : PauliKind)
    (z : LowDegreeSpace (PauliParams.ofAdmissibleParams P).toLowDegreeParams
      (MIPStarRE.QPBT.PauliScalar P)) :
    pauliSpaceEquiv P (pauliEmbedLowDegree W z) =
      MIPStarRE.QPBT.embedLd P (pauliKindEquiv W)
        (lowDegreeSpaceEquiv P.toLdParams z) := by
  funext i
  rcases i with ((((i | i) | u) | i) | u) | u <;> cases W <;> rfl

/-- A basis-selected compact low-degree map commutes with ambient embedding. -/
theorem pauliEmbeddedLowDegreeMap_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (W : PauliKind) (t : LowDegreeType)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    pauliSpaceEquiv P (pauliEmbedLowDegree W
        (lowDegreeMap (PauliParams.ofAdmissibleParams P).toLowDegreeParams
          (MIPStarRE.QPBT.binaryRepresentation P.model) t (pauliLowDegreeSpace W z))) =
      MIPStarRE.QPBT.embedLd P (pauliKindEquiv W)
        (MIPStarRE.QPBT.ldCL P.toLdParams (lowDegreeTypeEquiv t)
          (MIPStarRE.QPBT.pauliToLd P (pauliKindEquiv W) (pauliSpaceEquiv P z))) := by
  rw [pauliEmbedLowDegree_equiv]
  apply congrArg (MIPStarRE.QPBT.embedLd P (pauliKindEquiv W))
  calc
    lowDegreeSpaceEquiv P.toLdParams
        (lowDegreeMap (PauliParams.ofAdmissibleParams P).toLowDegreeParams
          (MIPStarRE.QPBT.binaryRepresentation P.model) t (pauliLowDegreeSpace W z)) =
      MIPStarRE.QPBT.ldCL P.toLdParams (lowDegreeTypeEquiv t)
        (lowDegreeSpaceEquiv P.toLdParams (pauliLowDegreeSpace W z)) :=
      pauliLowDegreeMap_equiv P t (pauliLowDegreeSpace W z)
    _ = MIPStarRE.QPBT.ldCL P.toLdParams (lowDegreeTypeEquiv t)
        (MIPStarRE.QPBT.pauliToLd P (pauliKindEquiv W) (pauliSpaceEquiv P z)) := by
      rw [pauliLowDegreeSpace_equiv]

/-- The shared four-register projection commutes with the space equivalence. -/
theorem pauliSharedProjection_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    pauliSpaceEquiv P (z.1, z.2.1, 0, 0, z.2.2.2.2.1, z.2.2.2.2.2) =
      MIPStarRE.QPBT.pauliSharedProjection (pauliSpaceEquiv P z) := by
  funext i
  rcases i with ((((i | i) | u) | i) | u) | u <;> rfl

/-- Every compact Pauli question map is the registered map in product coordinates. -/
theorem pauliMap_equiv (P : MIPStarRE.QPBT.AdmissibleParams) (t : PauliType)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    pauliSpaceEquiv P
        (pauliMap (PauliParams.ofAdmissibleParams P)
          (MIPStarRE.QPBT.binaryRepresentation P.model) t z) =
      MIPStarRE.QPBT.pauliCL P (pauliTypeEquiv t) (pauliSpaceEquiv P z) := by
  cases t with
  | point W =>
      simpa [pauliMap, MIPStarRE.QPBT.pauliCL, pauliTypeEquiv,
        lowDegreeTypeEquiv, MIPStarRE.QPBT.ldCL] using
        pauliEmbeddedLowDegreeMap_equiv P W .point z
  | aline W =>
      simpa [pauliMap, MIPStarRE.QPBT.pauliCL, pauliTypeEquiv,
        lowDegreeTypeEquiv, MIPStarRE.QPBT.ldCL] using
        pauliEmbeddedLowDegreeMap_equiv P W .aline z
  | dline W =>
      simpa [pauliMap, MIPStarRE.QPBT.pauliCL, pauliTypeEquiv,
        lowDegreeTypeEquiv, MIPStarRE.QPBT.ldCL] using
        pauliEmbeddedLowDegreeMap_equiv P W .dline z
  | pauli W =>
      funext i
      rcases i with ((((i | i) | u) | i) | u) | u <;> rfl
  | pairW W | pair | constraint _ | _ =>
      exact pauliSharedProjection_equiv P z

/-- The compact question PMF is exactly the registered question distribution. -/
theorem pauliQuestionPMF_map (P : MIPStarRE.QPBT.AdmissibleParams) :
    (pauliQuestionPMF (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)).map (pauliQuestionPairEquiv P) =
      (MIPStarRE.QPBT.pauliBasisTest P).μ.toPMF
        (MIPStarRE.QPBT.pauliBasisTest P).μ_prob := by
  classical
  letI : Nonempty MIPStarRE.QPBT.PauliEdge := MIPStarRE.QPBT.pauliEdge_nonempty
  let compactMap := fun s : PauliEdge ×
      PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P) =>
    ((s.1.1.1, pauliMap (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) s.1.1.1 s.2),
      (s.1.1.2, pauliMap (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) s.1.1.2 s.2))
  let originalMap := fun s :
      MIPStarRE.QPBT.PauliEdge × MIPStarRE.QPBT.PauliSpace P =>
    ((s.1.1.1, MIPStarRE.QPBT.pauliCL P s.1.1.1 s.2),
      (s.1.1.2, MIPStarRE.QPBT.pauliCL P s.1.1.2 s.2))
  have hcomm : pauliQuestionPairEquiv P ∘ compactMap =
      originalMap ∘ pauliSourceEquiv P := by
    funext s
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact pauliMap_equiv P s.1.1.1 s.2
    · apply Prod.ext
      · rfl
      · exact pauliMap_equiv P s.1.1.2 s.2
  rw [show pauliQuestionPMF (PauliParams.ofAdmissibleParams P)
      (MIPStarRE.QPBT.binaryRepresentation P.model) =
        (PMF.uniformOfFintype _).map compactMap by rfl]
  rw [PMF.map_comp, hcomm, ← PMF.map_comp]
  rw [PMF.uniformOfFintype_map_equiv (pauliSourceEquiv P)]
  have hmap :=
    (MIPStarRE.LDT.Distribution.toPMF_map
      (MIPStarRE.LDT.uniformDistribution
        (MIPStarRE.QPBT.PauliEdge × MIPStarRE.QPBT.PauliSpace P))
      (MIPStarRE.LDT.uniformDistribution_isProbability
        (MIPStarRE.QPBT.PauliEdge × MIPStarRE.QPBT.PauliSpace P)) originalMap).symm
  rw [MIPStarRE.LDT.uniformDistribution_toPMF] at hmap
  simpa only [MIPStarRE.QPBT.pauliBasisTest,
    MIPStarRE.QPBT.pauliQuestionDistribution] using hmap

/-- The six registered block projections recover the compact product coordinates. -/
@[simp] theorem pauliSpaceEquiv_xBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliXBlock (pauliSpaceEquiv P z) = z.1 :=
  rfl

@[simp] theorem pauliSpaceEquiv_zBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliZBlock (pauliSpaceEquiv P z) = z.2.1 :=
  rfl

@[simp] theorem pauliSpaceEquiv_scalarBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliScalarBlock (pauliSpaceEquiv P z) = z.2.2.1 :=
  rfl

@[simp] theorem pauliSpaceEquiv_directionBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliDirectionBlock (pauliSpaceEquiv P z) = z.2.2.2.1 :=
  rfl

@[simp] theorem pauliSpaceEquiv_rxBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliRXBlock (pauliSpaceEquiv P z) = z.2.2.2.2.1 :=
  rfl

@[simp] theorem pauliSpaceEquiv_rzBlock (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    MIPStarRE.QPBT.pauliRZBlock (pauliSpaceEquiv P z) = z.2.2.2.2.2 :=
  rfl

/-- The compact balanced coordinate map is the registered `chiIndex`. -/
@[simp] theorem pauliChiIndex_eq (P : MIPStarRE.QPBT.AdmissibleParams)
    (s : MIPStarRE.QPBT.PauliScalar P) :
    pauliChiIndex (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model) s =
      MIPStarRE.QPBT.chiIndex P.toLdParams s := by
  rfl

/-- Compact indicator entries are the registered Boolean-cube indicators. -/
@[simp] theorem pauliIndicator_eq_indicatorVec (P : MIPStarRE.QPBT.AdmissibleParams)
    (x : Fin P.m → MIPStarRE.QPBT.PauliScalar P) (y : Fin P.m → Bool) :
    pauliIndicator (P := PauliParams.ofAdmissibleParams P) x y =
      MIPStarRE.QPBT.indicatorVec x y :=
  (MIPStarRE.QPBT.indicatorVec_apply_eq_prod x y).symm

/-- The complete compact indicator vector is the registered indicator vector. -/
@[simp] theorem pauliIndicator_fun_eq_indicatorVec
    (P : MIPStarRE.QPBT.AdmissibleParams)
    (x : Fin P.m → MIPStarRE.QPBT.PauliScalar P) :
    pauliIndicator (P := PauliParams.ofAdmissibleParams P) x =
      MIPStarRE.QPBT.indicatorVec x := by
  funext y
  exact pauliIndicator_eq_indicatorVec P x y

/-- The compact multilinear encoding is the registered low-degree encoding. -/
@[simp] theorem pauliEncoded_eq_lowDegreeEnc (P : MIPStarRE.QPBT.AdmissibleParams)
    (h : (Fin P.m → Bool) → MIPStarRE.QPBT.PauliScalar P)
    (x : Fin P.m → MIPStarRE.QPBT.PauliScalar P) :
    pauliEncoded (P := PauliParams.ofAdmissibleParams P) h x =
      MIPStarRE.QPBT.lowDegreeEnc h x := by
  rw [MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct]
  simp [pauliEncoded, pauliIndicator_fun_eq_indicatorVec]

/-- The compact phase gate is exactly the registered Pauli pair gamma bit. -/
@[simp] theorem pauliGamma_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (z : PauliSpace (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    pauliGamma (MIPStarRE.QPBT.fixedBinTrace P.model) z =
      MIPStarRE.QPBT.pauliPairGamma P (pauliSpaceEquiv P z) := by
  simp only [pauliGamma, MIPStarRE.QPBT.pauliPairGamma, MIPStarRE.QPBT.gammaValue,
    pauliSpaceEquiv_rxBlock, pauliSpaceEquiv_rzBlock, pauliSpaceEquiv_xBlock,
    pauliSpaceEquiv_zBlock]
  rw [pauliIndicator_fun_eq_indicatorVec P z.1,
    pauliIndicator_fun_eq_indicatorVec P z.2.1]

/-- The compact and registered exceptional Magic Square parities coincide. -/
@[simp] theorem magicParity_eq_msParity (i : Fin 6) :
    magicParity i = MIPStarRE.QPBT.msParity i :=
  rfl

/-- Answer-shape rejection is unchanged by the constructor equivalence. -/
theorem validPauliAnswer_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (t : PauliType)
    (a : PauliAnswer (PauliParams.ofAdmissibleParams P) (MIPStarRE.QPBT.PauliScalar P)) :
    validPauliAnswer t a =
      MIPStarRE.QPBT.validPauliAnswer (pauliTypeEquiv t) (pauliAnswerEquivCompact P a) := by
  cases t <;> cases a <;>
    simp [validPauliAnswer, MIPStarRE.QPBT.validPauliAnswer, pauliTypeEquiv,
      pauliAnswerEquivCompact]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The proof checks all well-formed question/answer constructor pairs explicitly.
/-- The compact Boolean verifier is exactly the registered verifier after relabeling. -/
theorem pauliWin_equiv (P : MIPStarRE.QPBT.AdmissibleParams)
    (x y : PauliQuestion (PauliParams.ofAdmissibleParams P)
      (MIPStarRE.QPBT.PauliScalar P))
    (a b : PauliAnswer (PauliParams.ofAdmissibleParams P)
      (MIPStarRE.QPBT.PauliScalar P)) :
    pauliWin (PauliParams.ofAdmissibleParams P)
        (MIPStarRE.QPBT.binaryRepresentation P.model)
        (MIPStarRE.QPBT.fixedBinTrace P.model) x y a b =
      MIPStarRE.QPBT.pauliWinPredicate P (pauliQuestionEquiv P x)
        (pauliQuestionEquiv P y) (pauliAnswerEquivCompact P a)
        (pauliAnswerEquivCompact P b) := by
  rcases x with ⟨tA, xA⟩
  rcases y with ⟨tB, xB⟩
  unfold pauliWin MIPStarRE.QPBT.pauliWinPredicate
  simp only [pauliQuestionEquiv, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [← validPauliAnswer_equiv P tA a, ← validPauliAnswer_equiv P tB b]
  by_cases hv : (validPauliAnswer tA a && validPauliAnswer tB b) = true
  · rw [if_pos hv, if_pos hv]
    by_cases ht : tA = tB
    · have ht' : pauliTypeEquiv tA = pauliTypeEquiv tB := congrArg pauliTypeEquiv ht
      rw [if_pos ht, if_pos ht']
      apply decide_eq_decide.mpr
      constructor
      · exact fun h => congrArg (pauliAnswerEquivCompact P) h
      · exact fun h => (pauliAnswerEquivCompact P).injective h
    · have ht' : pauliTypeEquiv tA ≠ pauliTypeEquiv tB :=
        fun h => ht (pauliTypeEquiv.injective h)
      rw [if_neg ht, if_neg ht']
      obtain ⟨hvA, hvB⟩ := Bool.and_eq_true_iff.mp hv
      rcases tA with (_ | _) | (_ | _) | (_ | _) | (_ | _) | (_ | _) | _ | i | j <;>
        rcases a with uA | fA | gA | bitsA | bitA | tripleA | outcomeA <;>
        (try exact Bool.noConfusion hvA) <;>
        rcases tB with (_ | _) | (_ | _) | (_ | _) | (_ | _) | (_ | _) | _ | i' | j' <;>
        rcases b with uB | fB | gB | bitsB | bitB | tripleB | outcomeB <;>
        (try exact Bool.noConfusion hvB) <;>
        simp [pauliTypeEquiv, pauliKindEquiv, pauliAnswerEquivCompact,
          MIPStarRE.QPBT.pauliAlinePointCondition,
          MIPStarRE.QPBT.pauliDlinePointCondition,
          MIPStarRE.QPBT.pauliPointPauliCondition,
          MIPStarRE.QPBT.pauliPairCondition,
          MIPStarRE.QPBT.pauliPointPairCondition,
          MIPStarRE.QPBT.pauliPointVariableCondition,
          MIPStarRE.QPBT.msWinPredicate, MIPStarRE.QPBT.coordinateDirection,
          lowDegreeEval_eq_evalCoefficient, magicVariable_eq_msConstraintVars,
          magicParity_eq_msParity] <;>
        rfl
  · rw [if_neg hv, if_neg hv]

end

end MIPStarRE.QPBT.Palomar
