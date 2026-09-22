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

end LinePolynomialFunction

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

end MIPStarRE.QPBT
