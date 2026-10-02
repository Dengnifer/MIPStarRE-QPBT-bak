module

public import Mathlib

/-!
# Compact Palomar statement definitions

This Mathlib-only module is the single elaboration unit for the compact game,
strategy, consistency, and extraction definitions used by the four Palomar
headline aliases.  Keeping the complete statement surface in one module makes
the generated standalone challenge reproduce Lean-generated declaration names.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-270`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-1491`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder Matrix

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
  deriving DecidableEq, Inhabited

instance instFintypeLowDegreeType : Fintype LowDegreeType :=
  ⟨{.point, .aline, .dline}, by intro x; cases x <;> simp⟩

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


/-- Auxiliary finite spaces, local extraction isometries, and a unit auxiliary state. -/
structure ExtractionWitness {X Y A B R : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Fintype R] [DecidableEq R]
    (S : Strategy X Y A B) where
  ιA' : Type
  ιB' : Type
  [ιAFintype : Fintype ιA']
  [ιBFintype : Fintype ιB']
  [ιADecidableEq : DecidableEq ιA']
  [ιBDecidableEq : DecidableEq ιB']
  φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × R)
  φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × R)
  aux : EuclideanSpace ℂ (ιA' × ιB')
  aux_norm : ‖aux‖ = 1

attribute [instance] ExtractionWitness.ιAFintype ExtractionWitness.ιBFintype
  ExtractionWitness.ιADecidableEq ExtractionWitness.ιBDecidableEq

/-- The normalized maximally entangled vector on a nonempty finite register. -/
noncomputable def normalizedEPRState (R : Type) [Fintype R] [DecidableEq R]
    [Nonempty R] : EuclideanSpace ℂ (R × R) :=
  (EuclideanSpace.equiv (R × R) ℂ).symm fun p =>
    if p.1 = p.2 then (Real.sqrt (Fintype.card R : ℝ) : ℂ)⁻¹ else 0

/-- Apply two local linear isometries to a bipartite Euclidean state. -/
noncomputable def localIsometryTensor {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) : EuclideanSpace ℂ (κA × κB) :=
  (EuclideanSpace.equiv (κA × κB) ℂ).symm fun p =>
    ∑ i : ιA, ∑ j : ιB,
      (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) p.1 *
        (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) p.2 * ψ (i, j)

/-- The auxiliary state tensored with the EPR vector, shuffled into player-local order. -/
noncomputable def idealExtractionState {X Y A B R : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S) :
    EuclideanSpace ℂ ((w.ιA' × R) × (w.ιB' × R)) :=
  (EuclideanSpace.equiv ((w.ιA' × R) × (w.ιB' × R)) ℂ).symm fun p =>
    w.aux (p.1.1, p.2.1) * normalizedEPRState R (p.1.2, p.2.2)

/-- The unsquared norm error between the extracted state and the ideal state. -/
noncomputable def stateError {X Y A B R : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S) : ℝ :=
  ‖localIsometryTensor w.φA w.φB S.ψ - idealExtractionState w‖

/-- Alice's unaveraged sum of squared operator errors on the ideal state. -/
noncomputable def aliceOperatorError {X Y A B R O : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype O]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S)
    (actual ideal : O → Matrix ((w.ιA' × R) × (w.ιB' × R))
      ((w.ιA' × R) × (w.ιB' × R)) ℂ) : ℝ :=
  ∑ o : O, ‖Matrix.toEuclideanLin (actual o - ideal o) (idealExtractionState w)‖ ^ 2

/-- Bob's unaveraged sum of squared operator errors on the ideal state. -/
noncomputable def bobOperatorError {X Y A B R O : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype O]
    [Fintype R] [DecidableEq R] [Nonempty R] {S : Strategy X Y A B}
    (w : ExtractionWitness (R := R) S)
    (actual ideal : O → Matrix ((w.ιA' × R) × (w.ιB' × R))
      ((w.ιA' × R) × (w.ιB' × R)) ℂ) : ℝ :=
  ∑ o : O, ‖Matrix.toEuclideanLin (actual o - ideal o) (idealExtractionState w)‖ ^ 2


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
  deriving DecidableEq, Inhabited

instance instFintypePauliKind : Fintype PauliKind :=
  ⟨{.X, .Z}, by intro x; cases x <;> simp⟩

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
    split
    · rename_i h
      exact Nat.lt_succ_of_le (Nat.add_le_add
        (Nat.mul_le_mul_right 3 (Nat.le_of_lt_succ h)) (Nat.le_of_lt_succ j.isLt))
    · exact Nat.lt_succ_of_le (Nat.add_le_add
        (Nat.sub_le_sub_right (Nat.le_of_lt_succ i.isLt) 3)
        (Nat.mul_le_mul_right 3 (Nat.le_of_lt_succ j.isLt)))⟩

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


/-- A compact strategy on the full Pauli question and answer carriers. -/
abbrev PauliStrategy (P : PauliParams) (K : Type) [Fintype K] :=
  Strategy (PauliQuestion P K) (PauliQuestion P K)
    (PauliAnswer P K) (PauliAnswer P K)

/-- A compact symmetric strategy on the full Pauli carriers. -/
abbrev SymmetricPauliStrategy (P : PauliParams) (K : Type) [Fintype K] :=
  SymmetricStrategy (PauliQuestion P K) (PauliAnswer P K)

/-- The field-valued Boolean-cube register in the Pauli soundness conclusion. -/
abbrev PauliRegister (P : PauliParams) (K : Type) :=
  (Fin P.m → Bool) → K

/-- The binary register obtained by expanding each field coordinate in a fixed basis. -/
abbrev QubitRegister (P : PauliParams) (r : ℕ) :=
  (Fin P.m → Bool) × Fin r → ZMod 2

/-- The prescribed Pauli-basis question with zero ambient seed. -/
def pauliMeasurementQuestion {K : Type} [Zero K]
    (P : PauliParams) (W : PauliKind) : PauliQuestion P K :=
  (.pauli W, 0)

/-- The concrete projective, consistent, support-wise commuting predicate for
the compact Pauli question law. -/
def SymmetricStrategy.IsPauliSPCC {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (encoding : K ≃ Fin P.q)
    (S : SymmetricPauliStrategy P K) : Prop :=
  (∀ x, (S.meas x).IsProjective) ∧ S.IsConsistent ∧
    IsCommutingOn (pauliQuestionPMF P encoding) S.meas S.meas

/-- The error scale in the Pauli soundness and qubit-soundness conclusions. -/
noncomputable def deltaQld (a b epsilon : ℝ) (m d q : ℕ) : ℝ :=
  a * Real.rpow ((m * d : ℕ) : ℝ) a *
    (Real.rpow epsilon b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

/-- The sign character used in the characteristic-two Pauli eigenvectors. -/
noncomputable def pauliPhaseSign (t : ZMod 2) : ℂ :=
  if t = 0 then 1 else -1

/-- One coordinate of a generalized Pauli eigenvector. -/
noncomputable def singlePauliVec {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (trace : K → ZMod 2) (W : PauliKind) (e x : K) : ℂ :=
  match W with
  | .Z => if x = e then 1 else 0
  | .X =>
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ * pauliPhaseSign (trace (e * x))

/-- The tensor-product generalized Pauli eigenvector. -/
noncomputable def pauliVec {K I : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] (trace : K → ZMod 2) (W : PauliKind)
    (e x : I → K) : ℂ :=
  ∏ i : I, singlePauliVec trace W (e i) (x i)

/-- The rank-one generalized Pauli projector. -/
noncomputable def pauliProj {K I : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] (trace : K → ZMod 2) (W : PauliKind)
    (e : I → K) : Matrix (I → K) (I → K) ℂ :=
  Matrix.vecMulVec (pauliVec trace W e) (fun x => star (pauliVec trace W e x))

/-- The binary Pauli projector, using the trace of `ZMod 2` over itself. -/
noncomputable abbrev qubitPauliProj {I : Type} [Fintype I]
    (W : PauliKind) (e : I → ZMod 2) : Matrix (I → ZMod 2) (I → ZMod 2) ℂ :=
  pauliProj (Algebra.trace (ZMod 2) (ZMod 2)) W e

/-- Conjugate an operator by a local linear isometry. -/
noncomputable def conjIsometry {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J)
    (M : Matrix I I ℂ) : Matrix J J ℂ :=
  let U : Matrix J I ℂ := Matrix.toEuclideanLin.symm phi.toLinearMap
  U * M * Uᴴ

/-- Lift Alice's conjugated qudit effect to the full extracted target space. -/
noncomputable def liftedPauliAliceEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.2 = q.2 then conjIsometry phi M p.1 q.1 else 0

/-- Lift Bob's conjugated qudit effect to the full extracted target space. -/
noncomputable def liftedPauliBobEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (J' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1 = q.1 then conjIsometry phi M p.2 q.2 else 0

/-- Lift Alice's conjugated qubit effect by tensoring with Bob's identity. -/
noncomputable def liftedQubitAliceEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  Matrix.kronecker (conjIsometry phi M) 1

/-- Lift Bob's conjugated qubit effect by tensoring with Alice's identity. -/
noncomputable def liftedQubitBobEffect
    {I I' J' R : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    [Fintype R] [DecidableEq R]
    (phi : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (J' × R))
    (M : Matrix I I ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  Matrix.kronecker 1 (conjIsometry phi M)

/-- Place a register projector on Alice's target register. -/
noncomputable def idealProjectorAlice {I' J' R : Type}
    [DecidableEq I'] [DecidableEq J'] [DecidableEq R]
    (M : Matrix R R ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1.1 = q.1.1 ∧ p.2 = q.2 then M p.1.2 q.1.2 else 0

/-- Place a register projector on Bob's target register. -/
noncomputable def idealProjectorBob {I' J' R : Type}
    [DecidableEq I'] [DecidableEq J'] [DecidableEq R]
    (M : Matrix R R ℂ) :
    Matrix ((I' × R) × (J' × R)) ((I' × R) × (J' × R)) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then M p.2.2 q.2.2 else 0

/-- Expand a field-valued register label in fixed binary coordinates. -/
def binaryRegisterLabel {P : PauliParams} {K : Type} {r : ℕ}
    (coordinates : K → Fin r → ZMod 2) (u : PauliRegister P K) :
    QubitRegister P r :=
  fun p => coordinates (u p.1) p.2

/-- Alice's raw prescribed-answer qudit operator error. -/
noncomputable def rawPauliAliceError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := PauliRegister P K) S)
    (trace : K → ZMod 2) (W : PauliKind) : ℝ :=
  aliceOperatorError w
    (fun u => liftedPauliAliceEffect (J' := w.ιB') w.φA
      ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorAlice (J' := w.ιB') (pauliProj trace W u))

/-- Bob's raw prescribed-answer qudit operator error. -/
noncomputable def rawPauliBobError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := PauliRegister P K) S)
    (trace : K → ZMod 2) (W : PauliKind) : ℝ :=
  bobOperatorError w
    (fun u => liftedPauliBobEffect (I' := w.ιA') w.φB
      ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorBob (I' := w.ιA') (pauliProj trace W u))

/-- Alice's raw prescribed-answer qubit operator error, summed over the
original field-valued outcomes. -/
noncomputable def rawQubitAliceError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] {r : ℕ} (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := QubitRegister P r) S)
    (coordinates : K → Fin r → ZMod 2) (W : PauliKind) : ℝ :=
  aliceOperatorError w
    (fun u => liftedQubitAliceEffect (J' := w.ιB') w.φA
      ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorAlice (J' := w.ιB')
      (qubitPauliProj W (binaryRegisterLabel coordinates u)))

/-- Bob's raw prescribed-answer qubit operator error, summed over the
original field-valued outcomes. -/
noncomputable def rawQubitBobError {K : Type} [Field K] [Fintype K]
    [DecidableEq K] {r : ℕ} (P : PauliParams) (S : PauliStrategy P K)
    (w : ExtractionWitness (R := QubitRegister P r) S)
    (coordinates : K → Fin r → ZMod 2) (W : PauliKind) : ℝ :=
  bobOperatorError w
    (fun u => liftedQubitBobEffect (I' := w.ιA') w.φB
      ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)))
    (fun u => idealProjectorBob (I' := w.ιA')
      (qubitPauliProj W (binaryRegisterLabel coordinates u)))


end MIPStarRE.QPBT.Palomar
