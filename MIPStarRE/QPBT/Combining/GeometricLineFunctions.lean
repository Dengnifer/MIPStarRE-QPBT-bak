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

end LinePolynomialFunction

end MIPStarRE.QPBT
