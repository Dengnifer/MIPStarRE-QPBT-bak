module

public import MIPStarRE.QPBT.Palomar.Foundation

/-!
# Compact classical low individual degree game

This Mathlib-only module gives the concrete product-space presentation of the
classical low individual degree game used by the Palomar statement surface.
It keeps the complete ambient question carrier and the three answer summands,
including malformed answers that the verifier rejects.

The final statement module instantiates `K` with the carrier of the existing
`MIPStarRE.QPBT.fixedFieldModel`.  Its copied dependency contract consists of
`MIPStarRE.LDT.FieldModel`, `MIPStarRE.QPBT.IsAdmissibleSize`,
`MIPStarRE.QPBT.FixedFieldModel`, and that single registered selector.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

/-- The numerical domain of the classical low individual degree game. -/
structure LowDegreeParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : ∃ r : ℕ, Odd r ∧ q = 2 ^ r
  hdvd : m ∣ q

/-- The positive dimension supplies the nonzero modulus used by `chiIndex`. -/
instance LowDegreeParams.instNeZeroM (P : LowDegreeParams) : NeZero P.m :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one P.hm)⟩

/-- The three question types of the classical low individual degree game. -/
inductive LowDegreeType where
  | point
  | aline
  | dline
  deriving DecidableEq, Fintype, Inhabited

/-- The full point, seed, and direction space sampled by the verifier. -/
abbrev LowDegreeSpace (P : LowDegreeParams) (K : Type) :=
  ((Fin P.m → K) × K) × (Fin P.m → K)

/-- A typed low-degree question, retaining every ambient coordinate. -/
abbrev LowDegreeQuestion (P : LowDegreeParams) (K : Type) :=
  LowDegreeType × LowDegreeSpace P K

/-- The full three-summand answer alphabet, including malformed answers. -/
abbrev LowDegreeAnswer (P : LowDegreeParams) (K : Type) :=
  (Fin P.k → K) ⊕
    ((Fin P.k → Fin (P.d + 1) → K) ⊕
      (Fin P.k → Fin (P.m * P.d + 1) → K))

/-- Simultaneous bounded polynomial representatives used by low-degree soundness. -/
noncomputable abbrev LowDegreePolynomialTuple (P : LowDegreeParams) (K : Type)
    [CommSemiring K] :=
  Fin P.k → ↥(MvPolynomial.restrictDegree (Fin P.m) K P.d)

/-- Restricted-degree polynomials over a finite semiring form a finite type. -/
noncomputable instance restrictedDegreeFintype (m d : ℕ) (K : Type)
    [CommSemiring K] [Fintype K] :
    Fintype ↥(MvPolynomial.restrictDegree (Fin m) K d) := by
  letI : Finite ↥(MvPolynomial.restrictDegree (Fin m) K d) :=
    Module.finite_of_finite K
  exact Fintype.ofFinite _

/-- The least coordinate at which a nonzero direction is nonzero. -/
noncomputable def lowDegreePivot {K : Type} [Zero K] [DecidableEq K] {m : ℕ}
    (v : Fin m → K) (hv : v ≠ 0) : Fin m := by
  let support := Finset.univ.filter fun j => v j ≠ 0
  have hsupport : support.Nonempty := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    apply h
    refine ⟨j, ?_⟩
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hj
  exact support.min' hsupport

/-- The elementary least-pivot representative, with identity at zero direction. -/
noncomputable def lowDegreeLineRep {K : Type} [Field K] [DecidableEq K] {m : ℕ}
    (u v : Fin m → K) : Fin m → K :=
  if hv : v = 0 then u
  else
    let j := lowDegreePivot v hv
    u - (u j / v j) • v

/-- The paper's balanced seed-to-coordinate map. -/
noncomputable def lowDegreeChiIndex {K : Type} (P : LowDegreeParams)
    (encoding : K ≃ Fin P.q) (s : K) : Fin P.m :=
  Fin.ofNat P.m ((encoding s).val / (P.q / P.m))

/-- Zero the direction coordinates preceding `i`. -/
def lowDegreePrefix {K : Type} [Zero K] {m : ℕ} (i : Fin m) (v : Fin m → K) :
    Fin m → K :=
  fun j => if j.val < i.val then 0 else v j

/-- The concrete question map for each of the three question types. -/
noncomputable def lowDegreeMap {K : Type} [Field K] [DecidableEq K]
    (P : LowDegreeParams) (encoding : K ≃ Fin P.q) :
    LowDegreeType → LowDegreeSpace P K → LowDegreeSpace P K
  | .point, z => ((z.1.1, 0), 0)
  | .aline, z =>
      let direction := Pi.single (lowDegreeChiIndex P encoding z.1.2) 1
      ((lowDegreeLineRep z.1.1 direction, z.1.2), 0)
  | .dline, z =>
      let direction := lowDegreePrefix (lowDegreeChiIndex P encoding z.1.2) z.2
      ((lowDegreeLineRep z.1.1 direction, z.1.2), direction)

/-- The uniform law on all nine ordered type pairs and the entire ambient space. -/
noncomputable def lowDegreeQuestionPMF {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : LowDegreeParams) (encoding : K ≃ Fin P.q) :
    PMF (LowDegreeQuestion P K × LowDegreeQuestion P K) :=
  (PMF.uniformOfFintype ((LowDegreeType × LowDegreeType) × LowDegreeSpace P K)).map
    fun z => ((z.1.1, lowDegreeMap P encoding z.1.1 z.2),
      (z.1.2, lowDegreeMap P encoding z.1.2 z.2))

/-- Evaluate a bounded coefficient list at a field element. -/
def lowDegreeEval {K : Type} [Semiring K] {n : ℕ} (c : Fin n → K) (t : K) : K :=
  ∑ i : Fin n, c i * t ^ i.val

/-- Whether an answer lies in the summand prescribed by its question type. -/
def validLowDegreeAnswer {P : LowDegreeParams} {K : Type} :
    LowDegreeType → LowDegreeAnswer P K → Bool
  | .point, .inl _ => true
  | .aline, .inr (.inl _) => true
  | .dline, .inr (.inr _) => true
  | _, _ => false

/-- The complete low-degree verifier, including universal zero-direction tests. -/
noncomputable def lowDegreeWin {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : LowDegreeParams) (encoding : K ≃ Fin P.q) :
    LowDegreeQuestion P K → LowDegreeQuestion P K →
      LowDegreeAnswer P K → LowDegreeAnswer P K → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validLowDegreeAnswer tA a && validLowDegreeAnswer tB b then
      match tA, tB, a, b with
      | .point, .point, .inl u, .inl v => decide (u = v)
      | .aline, .point, .inr (.inl f), .inl u => decide (∀ t,
          xB.1.1 = xA.1.1 + t • Pi.single (lowDegreeChiIndex P encoding xA.1.2) 1 →
            ∀ j, lowDegreeEval (f j) t = u j)
      | .point, .aline, .inl u, .inr (.inl f) => decide (∀ t,
          xA.1.1 = xB.1.1 + t • Pi.single (lowDegreeChiIndex P encoding xB.1.2) 1 →
            ∀ j, lowDegreeEval (f j) t = u j)
      | .dline, .point, .inr (.inr f), .inl u => decide (∀ t,
          xB.1.1 = xA.1.1 + t • xA.2 → ∀ j, lowDegreeEval (f j) t = u j)
      | .point, .dline, .inl u, .inr (.inr f) => decide (∀ t,
          xA.1.1 = xB.1.1 + t • xB.2 → ∀ j, lowDegreeEval (f j) t = u j)
      | .aline, .aline, .inr (.inl f), .inr (.inl g) => decide (f = g)
      | .dline, .dline, .inr (.inr f), .inr (.inr g) => decide (f = g)
      | _, _, _, _ => true
    else false

/-- The compact classical low individual degree game. -/
noncomputable def lowDegreeGame {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (P : LowDegreeParams) (encoding : K ≃ Fin P.q) :
    Game (LowDegreeQuestion P K) (LowDegreeQuestion P K)
      (LowDegreeAnswer P K) (LowDegreeAnswer P K) where
  μ := lowDegreeQuestionPMF P encoding
  decide := lowDegreeWin P encoding

end MIPStarRE.QPBT.Palomar
