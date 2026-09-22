import MIPStarRE.QPBT.Combining.LinePolynomial

/-!
# Polynomial functions on geometric lines

The line part of the combining map acts on functions on the geometric point
sets. A bounded polynomial represents the pullback along a parameterization;
it is not part of the function's data. Thus different formal representatives
of the same function are equal as outcomes in this carrier. Singleton lines
are included. The coefficient answer carriers of the existing games are
unchanged; their comparison with this carrier requires descent on parameter
fibers and is a separate algebraic construction.

## References

- Blueprint `def:combine-map` and `rem:combine-map-function-domain`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`,
  especially `eq:combine-lines`.
- `references/qpbt-paper/04_preliminaries.tex:835-845` for polynomial functions.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`
  for lines, including zero directions.
- Issue #698 and `audits/2026-09-22_combining-map-source-domain.md`.
-/

namespace MIPStarRE.QPBT

variable {K : Type*} [Field K] {m c : ℕ}

/-- Polynomial functions of degree at most `c` on the geometric line
`linePoints u v`. The existential polynomial is a bounded representative of
the pullback, not a chosen outcome. This realizes the function domain of
`eq:combine-lines`, including singleton lines. -/
abbrev LinePolynomialFunction (u v : Fin m → K) (c : ℕ) :=
  {f : ↥(linePoints u v) → K // ∃ p : Polynomial K, p.natDegree ≤ c ∧
    ∀ t : K, p.eval t = f ⟨u + t • v, ⟨t, rfl⟩⟩}

noncomputable instance {u v : Fin m → K} [Fintype K] :
    Fintype (LinePolynomialFunction u v c) := by
  classical
  unfold LinePolynomialFunction
  infer_instance

namespace LinePolynomialFunction

/-- Equality on all parameterized points is equality of polynomial functions,
even when the parameterization is not injective. -/
@[ext] theorem ext {u v : Fin m → K} {f g : LinePolynomialFunction u v c}
    (h : ∀ t : K, f.1 ⟨u + t • v, ⟨t, rfl⟩⟩ =
      g.1 ⟨u + t • v, ⟨t, rfl⟩⟩) : f = g := by
  apply Subtype.ext
  funext x
  rcases x with ⟨x, t, rfl⟩
  exact h t

/-- Every bounded polynomial function has a bounded coefficient representative
of its pullback. This permits reuse of the coefficient combining polynomial
without choosing representatives as part of the function carrier. -/
theorem exists_coefficients {u v : Fin m → K} (f : LinePolynomialFunction u v c) :
    ∃ p : Fin (c + 1) → K,
      ∀ t : K, evalCoefficient p t = f.1 ⟨u + t • v, ⟨t, rfl⟩⟩ := by
  classical
  obtain ⟨p, hp, hf⟩ := f.2
  refine ⟨Polynomial.toFn (c + 1) p, fun t => ?_⟩
  rw [← polynomial_ofFn_eval_eq_evalCoefficient,
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hp)]
  exact hf t

/-- Over a finite field the pullback has a reduced representative, of degree
less than the field size, without increasing the given bound. This connects
the existential pullback convention with the polynomial-function convention
of `references/qpbt-paper/04_preliminaries.tex:835-845`. -/
theorem exists_reduced_representative [Fintype K] {u v : Fin m → K}
    (f : LinePolynomialFunction u v c) :
    ∃ p : Polynomial K, p.natDegree ≤ c ∧ p.natDegree < Fintype.card K ∧
      ∀ t : K, p.eval t = f.1 ⟨u + t • v, ⟨t, rfl⟩⟩ := by
  obtain ⟨p, hp, hf⟩ := f.2
  let z : Polynomial K := Polynomial.X ^ Fintype.card K - Polynomial.X
  have hz : z.Monic := Polynomial.monic_X_pow_sub (by
    rw [Polynomial.degree_X]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card K))
  have hdegree : z.natDegree = Fintype.card K :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
  have hne : z ≠ 1 := by
    intro h
    have hzdeg := congrArg Polynomial.natDegree h
    rw [hdegree, Polynomial.natDegree_one] at hzdeg
    exact (Fintype.card_pos (α := K)).ne' hzdeg
  refine ⟨p %ₘ z, Polynomial.natDegree_modByMonic_le_left.trans hp, ?_, ?_⟩
  · simpa only [hdegree] using Polynomial.natDegree_modByMonic_lt p hz hne
  · intro t
    change (p %ₘ z).eval₂ (RingHom.id K) t = _
    rw [Polynomial.eval₂_modByMonic_eq_self_of_root (by simp [z, FiniteField.pow_card])]
    exact hf t

/-- Restrict a polynomial function to a contained geometric line, preserving
its degree bound. Applied to equal point sets in both directions, this shows
that the carrier is independent of the chosen line presentation, including
singleton presentations. The affine parameters are supplied by line inclusion. -/
noncomputable def restrictToLine {u v u' v' : Fin m → K}
    (h : linePoints u v ⊆ linePoints u' v') (f : LinePolynomialFunction u' v' c) :
    LinePolynomialFunction u v c := by
  refine ⟨fun x => f.1 ⟨x.1, h x.2⟩, ?_⟩
  obtain ⟨p, hp, hf⟩ := f.2
  obtain ⟨a, b, hu, hv⟩ := exists_affine_parameters_of_linePoints_subset u v u' v' h
  refine ⟨p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X), ?_, ?_⟩
  · refine Polynomial.natDegree_comp_le.trans ?_
    have haff : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_C_add]
      exact (Polynomial.natDegree_C_mul_le b Polynomial.X).trans Polynomial.natDegree_X_le
    simpa using Nat.mul_le_mul hp haff
  · intro t
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, hf]
    apply congrArg f.1
    apply Subtype.ext
    dsimp
    rw [hu, hv]
    module

/-- Restriction preserves the value at every geometric point. In particular,
transport between equal line point sets is independent of affine parameters. -/
theorem restrictToLine_apply {u v u' v' : Fin m → K}
    (h : linePoints u v ⊆ linePoints u' v') (f : LinePolynomialFunction u' v' c)
    (x : ↥(linePoints u v)) : (restrictToLine h f).1 x = f.1 ⟨x.1, h x.2⟩ := rfl

/-- Descend a coefficient answer to a geometric polynomial function when its
evaluation is constant on parameter fibers. Mathlib's inverse of the
surjective parameterization selects a parameter; the fiber condition makes
the value independent of that selection. This adapter is separate from the
source combining construction and changes no game or measurement. -/
noncomputable def ofCoefficients (u v : Fin m → K) (p : Fin (c + 1) → K)
    (h : Function.FactorsThrough (evalCoefficient p) (fun t : K => u + t • v)) :
    LinePolynomialFunction u v c := by
  let param : K → ↥(linePoints u v) := fun t => ⟨u + t • v, ⟨t, rfl⟩⟩
  have hsurj : Function.Surjective param := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  refine ⟨fun x => evalCoefficient p (Function.surjInv hsurj x),
    linePolynomialOfCoefficients p, linePolynomialOfCoefficients_natDegree_le p, ?_⟩
  intro t
  rw [linePolynomialOfCoefficients_eval]
  exact h (congrArg Subtype.val (Function.surjInv_eq hsurj (param t))).symm

/-- The descent adapter preserves evaluation at every parameter, including
every parameter of a singleton. -/
theorem ofCoefficients_apply (u v : Fin m → K) (p : Fin (c + 1) → K)
    (h : Function.FactorsThrough (evalCoefficient p) (fun t : K => u + t • v)) (t : K) :
    (ofCoefficients u v p h).1 ⟨u + t • v, ⟨t, rfl⟩⟩ = evalCoefficient p t := by
  change evalCoefficient p (Function.surjInv _ _) = evalCoefficient p t
  apply h
  exact congrArg Subtype.val (Function.surjInv_eq
    (f := fun s : K => (⟨u + s • v, ⟨s, rfl⟩⟩ : ↥(linePoints u v))) _ _)

/-- Two descending coefficient lists define the same geometric function
exactly when their polynomial functions on the parameter field agree.
Formal polynomial equality is not required, even on a nondegenerate line. -/
theorem ofCoefficients_eq_iff (u v : Fin m → K) (p q : Fin (c + 1) → K)
    (hp : Function.FactorsThrough (evalCoefficient p) (fun t : K => u + t • v))
    (hq : Function.FactorsThrough (evalCoefficient q) (fun t : K => u + t • v)) :
    ofCoefficients u v p hp = ofCoefficients u v q hq ↔
      ∀ t : K, evalCoefficient p t = evalCoefficient q t := by
  constructor
  · intro h t
    simpa only [ofCoefficients_apply] using
      congrArg (fun f : LinePolynomialFunction u v c => f.1 ⟨u + t • v, ⟨t, rfl⟩⟩) h
  · intro h
    apply LinePolynomialFunction.ext
    simpa only [ofCoefficients_apply] using h

/-- On descending coefficient answers, geometric evaluation agrees exactly
with the existing universal `EvaluatesTo` relation at every point of the
line. This comparison does not assert descent of arbitrary game outcomes. -/
theorem ofCoefficients_evaluatesTo_iff {L : LdParams} (line : LineDesc L)
    (p : DegPoly L c)
    (h : Function.FactorsThrough (evalCoefficient p)
      (fun t : ScalarQ L => line.base + t • line.direction))
    (x : ↥(linePoints line.base line.direction)) (a : ScalarQ L) :
    EvaluatesTo line p x.1 a ↔
      (ofCoefficients line.base line.direction p h).1 x = a := by
  rcases x with ⟨x, t, rfl⟩
  rw [ofCoefficients_apply]
  constructor
  · intro hx
    exact hx.2 t rfl
  · intro ht
    refine ⟨⟨t, rfl⟩, fun s hs => ?_⟩
    exact (h hs.symm).trans ht

end LinePolynomialFunction

/-- Every coefficient answer descends on a nonzero-direction line. On a
singleton, descent is exactly constancy of the polynomial function on the
parameter field, not degree zero of a formal representative. -/
theorem coefficients_factorsThrough_iff (u v : Fin m → K) (p : Fin (c + 1) → K) :
    Function.FactorsThrough (evalCoefficient p) (fun t : K => u + t • v) ↔
      v ≠ 0 ∨ ∀ t : K, evalCoefficient p t = evalCoefficient p 0 := by
  constructor
  · intro h
    by_cases hv : v = 0
    · right
      intro t
      apply h
      simp [hv]
    · exact Or.inl hv
  · rintro (hv | h)
    · intro s t hst
      exact congrArg (evalCoefficient p)
        (smul_left_injective K hv (add_left_cancel hst))
    · intro s t _
      exact (h s).trans (h t).symm

/-- The source combining function on geometric lines, with degree at most
`c + 1`. Its only geometric hypothesis is the projection inclusion preceding
`eq:combine-lines`. Affine parameters and bounded polynomial representatives
are constructed inside the degree proof. The function itself uses neither
choice, and zero directions and constant projections are allowed.
Blueprint `def:combine-map`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:984-989`. -/
noncomputable def combineLineFunction
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ)
    (f : LinePolynomialFunction uX vX c) (g : LinePolynomialFunction uZ vZ c) :
    LinePolynomialFunction u v (c + 1) := by
  refine ⟨fun p => p.1 (alphaVar m) * f.1 ⟨projX p.1, (hproj p.1 p.2).1⟩ +
    p.1 (betaVar m) * g.1 ⟨projZ p.1, (hproj p.1 p.2).2⟩, ?_⟩
  obtain ⟨pf, hf⟩ := f.exists_coefficients
  obtain ⟨pg, hg⟩ := g.exists_coefficients
  obtain ⟨aX, bX, aZ, bZ, hcompat⟩ :=
    exists_isCombineLineCompatible_of_projection_mem u v uX vX uZ vZ hproj
  refine ⟨combineLinePolynomial aX bX aZ bZ
    (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) pf pg,
    combineLinePolynomial_natDegree_le _ _ _ _ _ _ _ _ pf pg, ?_⟩
  intro t
  simp only [combineLinePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    linePolynomialOfCoefficients_eval, hf, hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hX : f.1 ⟨projX (u + t • v), (hproj _ ⟨t, rfl⟩).1⟩ =
      f.1 ⟨uX + (aX + bX * t) • vX, ⟨_, rfl⟩⟩ :=
    congrArg f.1 (Subtype.ext (hcompat.2.2.2.2 t).1)
  have hZ : g.1 ⟨projZ (u + t • v), (hproj _ ⟨t, rfl⟩).2⟩ =
      g.1 ⟨uZ + (aZ + bZ * t) • vZ, ⟨_, rfl⟩⟩ :=
    congrArg g.1 (Subtype.ext (hcompat.2.2.2.2 t).2)
  rw [← hX, ← hZ]
  ring

/-- The pointwise source identity for the combining function. All arguments
are geometric points; no parameter or coefficient representative is selected.
This is `eq:combine-lines` of blueprint `def:combine-map`. -/
theorem combineLineFunction_apply
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ)
    (f : LinePolynomialFunction uX vX c) (g : LinePolynomialFunction uZ vZ c)
    (p : ↥(linePoints u v)) :
    (combineLineFunction u v uX vX uZ vZ hproj f g).1 p =
      p.1 (alphaVar m) * f.1 ⟨projX p.1, (hproj p.1 p.2).1⟩ +
        p.1 (betaVar m) * g.1 ⟨projZ p.1, (hproj p.1 p.2).2⟩ := rfl

/-- Every compatible affine choice and every pair of coefficient
representatives of the input functions gives the same geometric combining
function. In particular, neither affine choices nor formal representatives
affect the source output. This is an algebraic comparison with the coefficient
construction, not an additional premise of `combineLineFunction`. -/
theorem combineLineFunction_pullback
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ)
    (f : LinePolynomialFunction uX vX c) (g : LinePolynomialFunction uZ vZ c)
    (pf pg : Fin (c + 1) → K)
    (hf : ∀ t : K, evalCoefficient pf t = f.1 ⟨uX + t • vX, ⟨t, rfl⟩⟩)
    (hg : ∀ t : K, evalCoefficient pg t = g.1 ⟨uZ + t • vZ, ⟨t, rfl⟩⟩)
    (aX bX aZ bZ : K)
    (hcompat : IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
      (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))) (t : K) :
    evalCoefficient (combineLinePoly aX bX aZ bZ
      (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) pf pg) t =
      (combineLineFunction u v uX vX uZ vZ hproj f g).1 ⟨u + t • v, ⟨t, rfl⟩⟩ := by
  rw [(combineLinePoly_spec u v uX vX uZ vZ aX bX aZ bZ
    (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))
    pf pg hcompat t).2.2, hf, hg, combineLineFunction_apply]
  have hX : f.1 ⟨projX (u + t • v), (hproj _ ⟨t, rfl⟩).1⟩ =
      f.1 ⟨uX + (aX + bX * t) • vX, ⟨_, rfl⟩⟩ :=
    congrArg f.1 (Subtype.ext (hcompat.2.2.2.2 t).1)
  have hZ : g.1 ⟨projZ (u + t • v), (hproj _ ⟨t, rfl⟩).2⟩ =
      g.1 ⟨uZ + (aZ + bZ * t) • vZ, ⟨_, rfl⟩⟩ :=
    congrArg g.1 (Subtype.ext (hcompat.2.2.2.2 t).2)
  rw [← hX, ← hZ]
  rfl

/-- Combining descending coefficient answers gives a descending answer, and
its geometric function is the source combination of their geometric
functions. Every compatible affine choice is allowed. This restricted
coefficient comparison neither discards non-descending outcomes nor changes
any measurement or game. -/
theorem combineLinePoly_descends
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ)
    (pf pg : Fin (c + 1) → K)
    (hf : Function.FactorsThrough (evalCoefficient pf) (fun t : K => uX + t • vX))
    (hg : Function.FactorsThrough (evalCoefficient pg) (fun t : K => uZ + t • vZ))
    (aX bX aZ bZ : K)
    (hcompat : IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
      (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))) :
    let q := combineLinePoly aX bX aZ bZ
      (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) pf pg
    ∃ hq : Function.FactorsThrough (evalCoefficient q) (fun t : K => u + t • v),
      LinePolynomialFunction.ofCoefficients u v q hq =
        combineLineFunction u v uX vX uZ vZ hproj
          (LinePolynomialFunction.ofCoefficients uX vX pf hf)
          (LinePolynomialFunction.ofCoefficients uZ vZ pg hg) := by
  let f := LinePolynomialFunction.ofCoefficients uX vX pf hf
  let g := LinePolynomialFunction.ofCoefficients uZ vZ pg hg
  let F := combineLineFunction u v uX vX uZ vZ hproj f g
  let q := combineLinePoly aX bX aZ bZ
    (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) pf pg
  have hval (t : K) : evalCoefficient q t = F.1 ⟨u + t • v, ⟨t, rfl⟩⟩ :=
    combineLineFunction_pullback u v uX vX uZ vZ hproj f g pf pg
      (fun s => (LinePolynomialFunction.ofCoefficients_apply uX vX pf hf s).symm)
      (fun s => (LinePolynomialFunction.ofCoefficients_apply uZ vZ pg hg s).symm)
      aX bX aZ bZ hcompat t
  have hq : Function.FactorsThrough (evalCoefficient q) (fun t : K => u + t • v) := by
    intro s t hst
    rw [hval, hval]
    exact congrArg F.1 (Subtype.ext hst)
  refine ⟨hq, ?_⟩
  apply LinePolynomialFunction.ext
  intro t
  exact (LinePolynomialFunction.ofCoefficients_apply u v q hq t).trans (hval t)

end MIPStarRE.QPBT
