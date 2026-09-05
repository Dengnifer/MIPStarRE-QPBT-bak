import MIPStarRE.QPBT.Combining.Lines.SubLineExtended

/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma.  First, a uniformly random point of the
coordinate space is the same thing as a uniformly random canonical
representative together with a uniformly random affine parameter along the
direction: the map sending a pair to the point at that parameter on the line
through the representative has constant fibers of size `q`, because the
kernel of the canonical representative map is the span of the direction and
for the zero direction that map is the identity.  Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
`blueprint/src/chapter/ch15_qpbt_combining.tex:1499-1697`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is `def:line-representative`, blueprint
`ch11_qpbt_algebra.tex:500-520`; the coordinate blocks are those of
`def:combine-map`, blueprint `ch15_qpbt_combining.tex:445-480`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/

/-- For the zero direction the canonical representative map of
`def:line-representative` is the identity, since the span of the zero vector
is trivial.  Blueprint `ch11_qpbt_algebra.tex:500-530`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
theorem lineRepMap_zero_apply {K : Type*} [Field K] {m : ℕ}
    (u : Fin m → K) : lineRepMap (0 : Fin m → K) u = u := by
  have hspan : Submodule.span K ({0} : Set (Fin m → K)) = ⊥ := by simp
  have h := sub_lineRepMap_mem_span (0 : Fin m → K) u
  rw [hspan, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-! ## Uniform points of a line -/

/-- The point at a uniformly random affine parameter on the line through the
canonical representative of a uniformly random point is uniformly random on
the whole coordinate space.  Every fiber of the parameterization has exactly
`q` elements: for a nonzero direction the parameter is determined and the
representative varies over a coset of the span of the direction, and for the
zero direction the representative is the point itself and the parameter is
free.  Blueprint `ch15_qpbt_combining.tex:1499-1697`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_lineRepMap_add_smul {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K) :
    (uniformDistribution ((Fin m → K) × K)).map
        (fun w => lineRepMap v w.1 + w.2 • v) =
      uniformDistribution (Fin m → K) := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card K) fun x => ?_
  by_cases hv : v = 0
  · subst hv
    have hfilter :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => lineRepMap (0 : Fin m → K) w.1 + w.2 • (0 : Fin m → K)
              = x)
          = ({x} : Finset (Fin m → K)) ×ˢ (Finset.univ : Finset K) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true, smul_zero,
        add_zero, lineRepMap_zero_apply]
    rw [hfilter, Finset.card_product]
    simp
  · have hinj : Function.Injective
        (fun c : K => (lineRepMap v x + c • v, directLineRepParameter v x)) := by
      intro c₁ c₂ hc
      have hc' : c₁ • v = c₂ • v := by
        have h := congrArg Prod.fst hc
        simpa using h
      have hsub : (c₁ - c₂) • v = 0 := by
        rw [sub_smul, hc', sub_self]
      rcases smul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have himg :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => lineRepMap v w.1 + w.2 • v = x)
          = (Finset.univ : Finset K).image
              (fun c => (lineRepMap v x + c • v,
                directLineRepParameter v x)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw
        have hrep : lineRepMap v w.1 = lineRepMap v x := by
          rw [← hw, lineRepMap_add_smul, lineRepMap_apply_self]
        have hx : x = lineRepMap v x + w.2 • v := by
          rw [← hrep]
          exact hw.symm
        have ht : directLineRepParameter v x = w.2 :=
          directLineRepParameter_eq_of_nonzero hv hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
          (sub_lineRepMap_mem_span v w.1)
        refine ⟨c, ?_⟩
        have hw1 : lineRepMap v x + c • v = w.1 := by
          rw [← hrep, hc]
          abel
        rw [Prod.ext_iff]
        exact ⟨hw1, ht⟩
      · rintro ⟨c, rfl⟩
        show lineRepMap v (lineRepMap v x + c • v) +
          directLineRepParameter v x • v = x
        rw [lineRepMap_add_smul, lineRepMap_apply_self]
        exact (directLineRepParameter_spec v x).symm
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-! ## Injectivity of the two block embeddings -/

/-- The `X`-block coordinate embedding of `def:combine-map` is injective.
Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_injective (m : ℕ) : Function.Injective (embX m) := by
  intro i j hij
  simpa using (finCombineEquiv m).symm.injective hij

/-- The `Z`-block coordinate embedding of `def:combine-map` is injective.
Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embZ_injective (m : ℕ) : Function.Injective (embZ m) := by
  intro i j hij
  simpa using (finCombineEquiv m).symm.injective hij

/-! ## The blocks of an elementary coordinate direction -/

/-- The `X` block of the elementary direction at an `X`-block coordinate is
the elementary direction of the source space at that coordinate.  Blueprint
`ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projX (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) =
      coordinateDirection i := by
  funext j
  simp [projX, coordinateDirection, Pi.single_apply, (embX_injective m).eq_iff]

/-- The `X` block of the elementary direction at a `Z`-block coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projX (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ embZ m i := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `X` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ alphaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `X` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ betaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at a `Z`-block coordinate is
the elementary direction of the source space at that coordinate.  Blueprint
`ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projZ (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) =
      coordinateDirection i := by
  funext j
  simp [projZ, coordinateDirection, Pi.single_apply, (embZ_injective m).eq_iff]

/-- The `Z` block of the elementary direction at an `X`-block coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ}
    (i : Fin m) :
    projZ (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ embX m i := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at the first scalar coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ alphaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

/-- The `Z` block of the elementary direction at the second scalar coordinate
vanishes.  Blueprint `ch15_qpbt_combining.tex:445-480`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ betaVar m := by
    intro h
    simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

end

end MIPStarRE.QPBT
