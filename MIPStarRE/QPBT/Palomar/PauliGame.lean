module

public import MIPStarRE.QPBT.Palomar.LowDegreeGame

/-!
# Compact Pauli basis game

This Mathlib-only module gives the product-space presentation of the Pauli
basis game.  It retains the full ambient seed, the ordered-edge law, all seven
answer constructors, malformed answers, and every gate of the Boolean verifier.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

/-- The numerical domain of the Pauli basis game. -/
structure PauliParams where
  q : ℕ
  m : ℕ
  d : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hq : ∃ r : ℕ, Odd r ∧ q = 2 ^ r
  hdvd : m ∣ q

/-- The positive dimension supplies the modulus used by `pauliChiIndex`. -/
instance PauliParams.instNeZeroM (P : PauliParams) : NeZero P.m :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩

/-- The classical low-degree parameters used by each Pauli basis. -/
def PauliParams.toLowDegreeParams (P : PauliParams) : LowDegreeParams where
  q := P.q
  m := P.m
  d := P.d
  k := 1
  hm := P.hm
  hd := P.hd
  hk := by decide
  hq := P.hq
  hdvd := P.hdvd

/-- The two generalized Pauli bases. -/
inductive PauliKind where
  | X
  | Z
  deriving DecidableEq, Fintype, Inhabited

/-- The complete 26-element Pauli question-type carrier. -/
inductive PauliType where
  | point (W : PauliKind)
  | aline (W : PauliKind)
  | dline (W : PauliKind)
  | pauli (W : PauliKind)
  | pairW (W : PauliKind)
  | pair
  | constraint (i : Fin 6)
  | variable (j : Fin 9)
  deriving DecidableEq, Fintype, Inhabited

/-- The full coordinates `(uX,uZ,s,v,rX,rZ)` of a Pauli question seed. -/
abbrev PauliSpace (P : PauliParams) (K : Type) :=
  (Fin P.m → K) × (Fin P.m → K) × K × (Fin P.m → K) × K × K

/-- Select the point block belonging to one Pauli basis. -/
def pauliPointBlock {P : PauliParams} {K : Type}
    (W : PauliKind) (z : PauliSpace P K) : Fin P.m → K :=
  match W with
  | .X => z.1
  | .Z => z.2.1

/-- Read the low-degree point, seed, and direction coordinates. -/
def pauliLowDegreeSpace {P : PauliParams} {K : Type}
    (W : PauliKind) (z : PauliSpace P K) : LowDegreeSpace P.toLowDegreeParams K :=
  ((pauliPointBlock W z, z.2.2.1), z.2.2.2.1)

/-- The balanced seed-to-coordinate map in the Pauli parameter presentation. -/
noncomputable def pauliChiIndex {K : Type} (P : PauliParams)
    (encoding : K ≃ Fin P.q) (s : K) : Fin P.m :=
  Fin.ofNat P.m ((encoding s).val / (P.q / P.m))

/-- Embed low-degree coordinates into one basis block and clear all others. -/
def pauliEmbedLowDegree {P : PauliParams} {K : Type} [Zero K]
    (W : PauliKind) (z : LowDegreeSpace P.toLowDegreeParams K) : PauliSpace P K :=
  match W with
  | .X => (z.1.1, 0, z.1.2, z.2, 0, 0)
  | .Z => (0, z.1.1, z.1.2, z.2, 0, 0)

/-- The concrete question map for every Pauli question type. -/
noncomputable def pauliMap {K : Type} [Field K] [DecidableEq K]
    (P : PauliParams) (encoding : K ≃ Fin P.q) :
    PauliType → PauliSpace P K → PauliSpace P K
  | .point W, z => pauliEmbedLowDegree W
      (lowDegreeMap P.toLowDegreeParams encoding .point (pauliLowDegreeSpace W z))
  | .aline W, z => pauliEmbedLowDegree W
      (lowDegreeMap P.toLowDegreeParams encoding .aline (pauliLowDegreeSpace W z))
  | .dline W, z => pauliEmbedLowDegree W
      (lowDegreeMap P.toLowDegreeParams encoding .dline (pauliLowDegreeSpace W z))
  | .pauli _, _ => 0
  | .pairW _, z | .pair, z | .constraint _, z | .variable _, z =>
      (z.1, z.2.1, 0, 0, z.2.2.2.2.1, z.2.2.2.2.2)

/-- The Magic Square variable at one position of a constraint. -/
def magicVariable (i : Fin 6) (j : Fin 3) : Fin 9 :=
  ⟨if i.val < 3 then i.val * 3 + j.val else i.val - 3 + j.val * 3, by
    by_cases h : i.val < 3 <;> simp [h] <;> omega⟩

/-- The exceptional parity of the final Magic Square constraint. -/
def magicParity (i : Fin 6) : ZMod 2 := if i.val = 5 then 1 else 0

/-- The undirected Pauli type graph, including every self-loop. -/
def pauliEdges : Finset (Sym2 PauliType) :=
  let loops := Finset.univ.image fun t : PauliType => Sym2.mk t t
  let lines := (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.aline W)) ∪
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.dline W)) ∪
    (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pauli W))
  let basis := (Finset.univ : Finset PauliKind).image (fun W =>
      Sym2.mk (.point W) (.pairW W)) ∪
    ({Sym2.mk (.point .X) (.variable 0),
      Sym2.mk (.point .Z) (.variable 4)} : Finset (Sym2 PauliType))
  let pairs := (Finset.univ : Finset PauliKind).image fun W =>
    Sym2.mk (.pairW W) .pair
  let magic := (Finset.univ : Finset (Fin 6 × Fin 3)).image fun ij =>
    Sym2.mk (.constraint ij.1) (.variable (magicVariable ij.1 ij.2))
  loops ∪ lines ∪ basis ∪ pairs ∪ magic

/-- The ordered carrier of the Pauli type graph. -/
abbrev PauliEdge :=
  {e : PauliType × PauliType // Sym2.mk e.1 e.2 ∈ pauliEdges}

/-- A loop supplies the nonempty ordered-edge carrier. -/
instance : Nonempty PauliEdge :=
  ⟨⟨(.point .X, .point .X), by simp [pauliEdges]⟩⟩

/-- A typed Pauli question, retaining every ambient coordinate. -/
abbrev PauliQuestion (P : PauliParams) (K : Type) := PauliType × PauliSpace P K

/-- Full finite question coordinates have decidable equality. -/
noncomputable instance {P : PauliParams} {K : Type} [DecidableEq K] :
    DecidableEq (PauliQuestion P K) := Classical.decEq _

/-- The question law is uniform on all ordered edges and the full seed space. -/
noncomputable def pauliQuestionPMF {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (encoding : K ≃ Fin P.q) :
    PMF (PauliQuestion P K × PauliQuestion P K) :=
  (PMF.uniformOfFintype (PauliEdge × PauliSpace P K)).map fun s =>
    ((s.1.1.1, pauliMap P encoding s.1.1.1 s.2),
      (s.1.1.2, pauliMap P encoding s.1.1.2 s.2))

/-- The seven answer forms, including malformed answers at every question. -/
inductive PauliAnswer (P : PauliParams) (K : Type) where
  | value (a : K)
  | alinePoly (a : Fin (P.d + 1) → K)
  | dlinePoly (a : Fin (P.m * P.d + 1) → K)
  | pairBits (a : ZMod 2 × ZMod 2)
  | bit (a : ZMod 2)
  | msTriple (a : Fin 3 → ZMod 2)
  | pauliOutcome (a : (Fin P.m → Bool) → K)
  deriving DecidableEq, Fintype

/-- Whether an answer constructor is prescribed by its question type. -/
def validPauliAnswer {P : PauliParams} {K : Type} :
    PauliType → PauliAnswer P K → Bool
  | .point _, .value _ | .aline _, .alinePoly _ | .dline _, .dlinePoly _ => true
  | .pauli _, .pauliOutcome _ | .pairW _, .bit _ | .pair, .pairBits _ => true
  | .constraint _, .msTriple _ | .variable _, .bit _ => true
  | _, _ => false

/-- One entry of the Boolean-cube indicator vector. -/
def pauliIndicator {P : PauliParams} {K : Type} [CommRing K]
    (x : Fin P.m → K) (y : Fin P.m → Bool) : K :=
  ∏ i : Fin P.m, if y i then x i else 1 - x i

/-- Evaluate the multilinear low-degree encoding of a Pauli outcome. -/
def pauliEncoded {P : PauliParams} {K : Type} [CommRing K]
    (h : (Fin P.m → Bool) → K) (x : Fin P.m → K) : K :=
  dotProduct h (pauliIndicator x)

/-- The phase bit computed from the shared tuple coordinates. -/
def pauliGamma {P : PauliParams} {K : Type} [CommRing K]
    (trace : K → ZMod 2) (z : PauliSpace P K) : ZMod 2 :=
  trace (dotProduct (z.2.2.2.2.1 • pauliIndicator z.1)
    (z.2.2.2.2.2 • pauliIndicator z.2.1))

/-- The complete Pauli verifier, including gamma gates and off-edge defaults. -/
noncomputable def pauliWin {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : PauliParams) (encoding : K ≃ Fin P.q) (trace : K → ZMod 2) :
    PauliQuestion P K → PauliQuestion P K → PauliAnswer P K → PauliAnswer P K → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validPauliAnswer tA a && validPauliAnswer tB b then
      if tA = tB then decide (a = b) else
      match tA, tB, a, b with
      | .aline W, .point W', .alinePoly f, .value u => if W = W' then decide (∀ t,
          pauliPointBlock W xB = pauliPointBlock W xA +
            t • Pi.single (pauliChiIndex P encoding xA.2.2.1) 1 →
          lowDegreeEval f t = u) else true
      | .point W, .aline W', .value u, .alinePoly f => if W = W' then decide (∀ t,
          pauliPointBlock W xA = pauliPointBlock W xB +
            t • Pi.single (pauliChiIndex P encoding xB.2.2.1) 1 →
          lowDegreeEval f t = u) else true
      | .dline W, .point W', .dlinePoly f, .value u => if W = W' then decide (∀ t,
          pauliPointBlock W xB = pauliPointBlock W xA + t • xA.2.2.2.1 →
          lowDegreeEval f t = u) else true
      | .point W, .dline W', .value u, .dlinePoly f => if W = W' then decide (∀ t,
          pauliPointBlock W xA = pauliPointBlock W xB + t • xB.2.2.2.1 →
          lowDegreeEval f t = u) else true
      | .point W, .pauli W', .value u, .pauliOutcome h =>
          if W = W' then decide (pauliEncoded h (pauliPointBlock W xA) = u) else true
      | .pauli W, .point W', .pauliOutcome h, .value u =>
          if W = W' then decide (pauliEncoded h (pauliPointBlock W xB) = u) else true
      | .pairW W, .pair, .bit β, .pairBits bits => decide (pauliGamma trace xA ≠ 0 ∨
          match W with | .X => bits.1 = β | .Z => bits.2 = β)
      | .pair, .pairW W, .pairBits bits, .bit β => decide (pauliGamma trace xB ≠ 0 ∨
          match W with | .X => bits.1 = β | .Z => bits.2 = β)
      | .point W, .pairW W', .value u, .bit β => if W = W' then decide
          (pauliGamma trace xB ≠ 0 ∨ trace (u * if W = .X then xB.2.2.2.2.1
            else xB.2.2.2.2.2) = β) else true
      | .pairW W, .point W', .bit β, .value u => if W = W' then decide
          (pauliGamma trace xA ≠ 0 ∨ trace (u * if W = .X then xA.2.2.2.2.1
            else xA.2.2.2.2.2) = β) else true
      | .constraint i, .variable j, .msTriple bits, .bit β =>
          if ∃ k, magicVariable i k = j then decide (pauliGamma trace xA = 0 ∨
            (∑ k, bits k) = magicParity i ∧ ∃ k, magicVariable i k = j ∧ bits k = β)
          else true
      | .variable j, .constraint i, .bit β, .msTriple bits =>
          if ∃ k, magicVariable i k = j then decide (pauliGamma trace xB = 0 ∨
            (∑ k, bits k) = magicParity i ∧ ∃ k, magicVariable i k = j ∧ bits k = β)
          else true
      | .point W, .variable j, .value u, .bit β => decide (pauliGamma trace xB = 0 ∨
          (j = 0 ∧ W = .X ∧ trace (u * xB.2.2.2.2.1) = β) ∨
          (j = 4 ∧ W = .Z ∧ trace (u * xB.2.2.2.2.2) = β))
      | .variable j, .point W, .bit β, .value u => decide (pauliGamma trace xA = 0 ∨
          (j = 0 ∧ W = .X ∧ trace (u * xA.2.2.2.2.1) = β) ∨
          (j = 4 ∧ W = .Z ∧ trace (u * xA.2.2.2.2.2) = β))
      | _, _, _, _ => true
    else false

/-- The compact Pauli basis game. -/
noncomputable def pauliGame {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : PauliParams) (encoding : K ≃ Fin P.q) (trace : K → ZMod 2) :
    Game (PauliQuestion P K) (PauliQuestion P K) (PauliAnswer P K) (PauliAnswer P K) := by
  classical
  exact { μ := pauliQuestionPMF P encoding, decide := pauliWin P encoding trace }

end MIPStarRE.QPBT.Palomar
