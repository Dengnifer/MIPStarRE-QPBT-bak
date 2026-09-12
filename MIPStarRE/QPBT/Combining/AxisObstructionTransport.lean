import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.LineResampling
import MIPStarRE.QPBT.Observables.WinImplications.Averages

/-!
# Restricted axis averages for the quadratic obstruction

These finite probability identities supply the line-law part of the obstruction
in issue #511. They do not construct a strategy or refute the extended-line
existence assertion. In particular, the function averaged below must still be
identified with the evaluated POVM defect in an application.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`,
  `lem:alnf` and `def:line-point-dist`.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`,
  `lem:qld-4-13`; blueprint `lem:qld-4-13-established`.
* `docs/paper-gaps/qpbt_combined-lines-error-term.tex`, subsection
  "Unrestricted point witnesses in the extended-line assertion".
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Restricting the actual direct line-point law to one axis has weight
`1 / (2 * m)`. The remaining sample is a uniform ambient point on its
canonical axis line; the unused direction coordinate has been integrated out. -/
theorem avgOver_directLinePointDist_axis_index (D : DirectLdParams) (i : Fin D.m)
    (F : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (directLinePointDist D) (fun s =>
        if s.1.kind = .axis ∧ s.1.index = i then F s else 0) =
      (1 / (2 * (D.m : ℝ))) *
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun u =>
          F (directALineDescOf D ⟨u, i, 0⟩, u)) := by
  classical
  rw [directLinePointDist, WinImplications.avgOver_mix]
  simp only [directALinePointDist, directDLinePointDist, Distribution.avgOver_map,
    directALineDescOf, directDLineDescOf, DirectLineDesc.kind, DirectLineDesc.index,
    true_and, reduceCtorEq, false_and, ite_false, avgOver_zero, mul_zero, add_zero]
  rw [avgOver_uniform_equiv_prod (directLdSpaceIndexEquiv D)]
  simp only [directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk]
  have hslice (j : Fin D.m) :
      avgOver (uniformDistribution
          ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
        (fun p => if j = i then F (directALineDescOf D ⟨p.1, j, p.2⟩, p.1) else 0) =
      if j = i then avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => F (directALineDescOf D ⟨u, i, 0⟩, u)) else 0 := by
    by_cases h : j = i
    · subst j
      simp only [ite_true]
      exact avgOver_uniform_fst (β := Fin D.m → DirectScalarQ D)
        (fun u : Fin D.m → DirectScalarQ D => F (directALineDescOf D ⟨u, i, 0⟩, u))
    · simp [h, avgOver_zero]
  simp_rw [show ∀ j, avgOver (uniformDistribution
      ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)))
      (fun p => if j = i then F
        (.axis (lineRepMap (coordinateDirection j) p.1) j
          (lineRepMap_apply_self (coordinateDirection j) p.1), p.1) else 0) =
      if j = i then avgOver (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u => F (directALineDescOf D ⟨u, i, 0⟩, u)) else 0 from hslice]
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  simp only [Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [directALineDescOf]
  ring

/-- The selected axis average can equivalently sample a canonical line first
and then an independent uniform affine parameter. This retains the line as an
argument of `F`, so the identity applies to measurements depending on the line. -/
theorem avgOver_directLinePointDist_axis_index_resample
    (D : DirectLdParams) (i : Fin D.m)
    (F : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (directLinePointDist D) (fun s =>
        if s.1.kind = .axis ∧ s.1.index = i then F s else 0) =
      (1 / (2 * (D.m : ℝ))) *
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun u =>
          let line := directALineDescOf D ⟨u, i, 0⟩
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (line, line.base + t • line.direction))) := by
  let G : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ := fun s =>
    if s.1.kind = .axis ∧ s.1.index = i then F s else 0
  have h := avgOver_directALinePointDist_resample D G
  have hdiag : avgOver (directDLinePointDist D) G = 0 := by
    simp [G, directDLinePointDist, Distribution.avgOver_map,
      directDLineDescOf, DirectLineDesc.kind, avgOver_zero]
  have hresample : avgOver (directLinePointDist D) G =
      avgOver (directLinePointDist D) (fun s =>
        if s.1.kind = .axis ∧ s.1.index = i then
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (s.1, s.1.base + t • s.1.direction)) else 0) := by
    simp only [directLinePointDist, WinImplications.avgOver_mix]
    rw [hdiag]
    rw [← h, Distribution.avgOver_map]
    simp only [G]
    have hif (s : DirectLineDesc D × (Fin D.m → DirectScalarQ D)) :
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          if s.1.kind = .axis ∧ s.1.index = i then
            F (s.1, s.1.base + t • s.1.direction) else 0) =
        if s.1.kind = .axis ∧ s.1.index = i then
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (s.1, s.1.base + t • s.1.direction)) else 0 := by
      split_ifs <;> simp [avgOver_zero]
    simp_rw [hif]
    simp [directDLinePointDist, Distribution.avgOver_map,
      directDLineDescOf, DirectLineDesc.kind, avgOver_zero]
  exact hresample.trans (avgOver_directLinePointDist_axis_index D i _)

/-- A nonnegative line-point integrand dominates the contribution of any one
axis, with its exact mixture weight and its independent affine parameter. -/
theorem avgOver_directLinePointDist_ge_axis_index
    (D : DirectLdParams) (i : Fin D.m)
    (F : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ)
    (hF : ∀ s, 0 ≤ F s) :
    (1 / (2 * (D.m : ℝ))) *
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun u =>
          let line := directALineDescOf D ⟨u, i, 0⟩
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            F (line, line.base + t • line.direction))) ≤
      avgOver (directLinePointDist D) F := by
  rw [← avgOver_directLinePointDist_axis_index_resample]
  apply avgOver_mono
  intro s
  split_ifs
  · exact le_refl _
  · exact hF s

/-- Canonicalizing an axis line leaves every transverse coordinate unchanged.
This applies in particular to the combining coefficient on an X-axis line. -/
theorem lineRepMap_coordinateDirection_apply_ne
    {K : Type*} [Field K] {m : ℕ} (i j : Fin m) (hji : j ≠ i)
    (u : Fin m → K) : lineRepMap (coordinateDirection i) u j = u j := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (sub_lineRepMap_mem_span (coordinateDirection i) u)
  have hj := congrFun ht j
  simp [coordinateDirection, hji] at hj
  exact (sub_eq_zero.mp hj.symm).symm

/-- The coordinate transverse to a selected axis is uniform on its canonical
line bases. The assertion is about the line marginal, before the independent
parameter is drawn, so no independence of a line measurement is assumed. -/
theorem avgOver_axis_base_coordinate (D : DirectLdParams) (i j : Fin D.m)
    (hji : j ≠ i) (g : DirectScalarQ D → ℝ) :
    avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) (fun u =>
        g ((directALineDescOf D ⟨u, i, 0⟩).base j)) =
      avgOver (uniformDistribution (DirectScalarQ D)) g := by
  simp only [directALineDescOf, DirectLineDesc.base,
    lineRepMap_coordinateDirection_apply_ne i j hji]
  exact avgOver_uniform_equiv_fst (Equiv.funSplitAt j (DirectScalarQ D)) g

/-- Transport a lower bound for each fixed axis line to the full direct law.
The bound may depend on a transverse coefficient, which is averaged uniformly.
This is a finite probability lemma, not a conditional version of the paper
construction theorem: it supplies no POVMs or strategy. -/
theorem avgOver_directLinePointDist_ge_axis_coefficient
    (D : DirectLdParams) (i j : Fin D.m) (hji : j ≠ i)
    (F : DirectLineDesc D × (Fin D.m → DirectScalarQ D) → ℝ)
    (g : DirectScalarQ D → ℝ) (hF : ∀ s, 0 ≤ F s)
    (hline : ∀ u : Fin D.m → DirectScalarQ D,
      let line := directALineDescOf D ⟨u, i, 0⟩
      g (line.base j) ≤ avgOver (uniformDistribution (DirectScalarQ D))
        (fun t => F (line, line.base + t • line.direction))) :
    (1 / (2 * (D.m : ℝ))) * avgOver (uniformDistribution (DirectScalarQ D)) g ≤
      avgOver (directLinePointDist D) F := by
  rw [← avgOver_axis_base_coordinate D i j hji]
  exact (mul_le_mul_of_nonneg_left (avgOver_mono _ _ _ hline) (by positivity)).trans
    (avgOver_directLinePointDist_ge_axis_index D i F hF)

end

end MIPStarRE.QPBT
