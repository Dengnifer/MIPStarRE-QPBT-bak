import MIPStarRE.QPBT.Combining.Lines.RestrictedAverage
import MIPStarRE.QPBT.Combining.Lines.SubLineBind
import MIPStarRE.QPBT.Combining.Lines.SubLineProduct
import MIPStarRE.QPBT.Combining.Lines.SubLineTransport

/-!
# A uniform point of the extended space from the sub-line law

The three scalar estimates that combine the two Pauli bases average over an
extended line drawn from the sub-line law together with a uniform affine
parameter on that line.  This module records that the resulting point is a
uniformly random point of the extended coordinate space, so that its two
source blocks are two independent uniform points of the source space.

The argument is the same for the two branches of the directly indexed
line-point law: in both branches the geometric direction of the sampled line
depends only on the stored coordinate index and the stored direction, and the
canonical base point is the canonical representative of the stored point in
that direction.  Conditionally on the direction the sampled point is
therefore the point at a uniform affine parameter on the line through the
canonical representative of a uniform point, which is a uniform point.

## References

The statements support `lem:claim-17-1`, `lem:claim-17-2`, and
`lem:claim-17-3` in `blueprint/src/chapter/ch15_qpbt_combining.tex`, whose
paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1209`.
The sub-line law is `lem:qld-sublines`, blueprint lines 1499--1697, and the
directly indexed line-point law is the one of `def:line-point-dist` repaired
in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Push-forward of a product law along a two-variable map -/

/-- If every slice of a map of a pair carries the uniform law of the second
variable to one and the same law, then the map carries the uniform law of the
pair to that law.  Blueprint `ch15_qpbt_combining.tex:1499-1697`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_uncurry {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α × β → γ) (ν : Distribution γ)
    (hg : ∀ a, (uniformDistribution β).map (fun b => g (a, b)) = ν) :
    (uniformDistribution (α × β)).map g = ν := by
  classical
  rw [uniformDistribution_prod, Distribution.prod_map_eq_bind,
    show (fun a => (uniformDistribution β).map (fun b => g (a, b))) =
      fun _ => ν from funext hg]
  exact Distribution.bind_const _ (uniformDistribution_isProbability α) ν

/-! ## A uniform point on a sampled directly indexed line -/


/-- Reading the point at a uniform affine parameter on the canonical line of a
uniform direct sample, in any direction determined by the stored coordinate
index and the stored direction, gives a uniform point of the coordinate
space.  Blueprint `ch15_qpbt_combining.tex:1499-1697`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_directLine_add_smul (D : DirectLdParams)
    (V : Fin D.m × (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D)) :
    (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
        (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
          p.2 • V (p.1.index, p.1.direction)) =
      uniformDistribution (Fin D.m → DirectScalarQ D) := by
  classical
  let e : DirectLdSpace D × DirectScalarQ D ≃
      (Fin D.m × (Fin D.m → DirectScalarQ D)) ×
        ((Fin D.m → DirectScalarQ D) × DirectScalarQ D) :=
    { toFun := fun p => ((p.1.index, p.1.direction), (p.1.point, p.2))
      invFun := fun w => (⟨w.2.1, w.1.1, w.1.2⟩, w.2.2)
      left_inv := by rintro ⟨⟨pt, i, dir⟩, t⟩; rfl
      right_inv := by rintro ⟨⟨i, dir⟩, pt, t⟩; rfl }
  have hequiv :
      (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e =
        uniformDistribution ((Fin D.m × (Fin D.m → DirectScalarQ D)) ×
          ((Fin D.m → DirectScalarQ D) × DirectScalarQ D)) :=
    uniformDistribution_map_equiv e
  have hmap :
      (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)) =
        ((uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e).map
          (fun w => lineRepMap (V w.1) w.2.1 + w.2.2 • V w.1) := by
    rw [Distribution.map_map]
    rfl
  rw [hmap, hequiv]
  refine uniformDistribution_map_uncurry _ _ fun a => ?_
  exact uniformDistribution_map_lineRepMap_add_smul (V a)


/-- Averaging a function of the point at a uniform affine parameter on the
canonical line of a uniform direct sample is averaging it at a uniform point.
Blueprint `ch15_qpbt_combining.tex:1499-1697`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem avgOver_uniform_directLdSpace_line_add_smul (D : DirectLdParams)
    (V : Fin D.m × (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D))
    (g : (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (lineRepMap (V (s.index, s.direction)) s.point +
            t • V (s.index, s.direction)))) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
  classical
  calc
    avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (lineRepMap (V (s.index, s.direction)) s.point +
              t • V (s.index, s.direction)))) =
        avgOver (Distribution.prod (uniformDistribution (DirectLdSpace D))
            (uniformDistribution (DirectScalarQ D)))
          (fun p => g (lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction))) :=
      (avgOver_prod (uniformDistribution (DirectLdSpace D))
          (uniformDistribution (DirectScalarQ D))
          (fun p => g (lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)))).symm
    _ = avgOver ((Distribution.prod (uniformDistribution (DirectLdSpace D))
            (uniformDistribution (DirectScalarQ D))).map
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction))) g :=
      (Distribution.avgOver_map
          (Distribution.prod (uniformDistribution (DirectLdSpace D))
            (uniformDistribution (DirectScalarQ D)))
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)) g).symm
    _ = avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
      rw [← uniformDistribution_prod,
        uniformDistribution_map_directLine_add_smul]


/-- Averaging a function of the point at a uniform affine parameter on a line
drawn from the directly indexed line-point law is averaging it at a uniform
point of the coordinate space.  Blueprint
`ch15_qpbt_combining.tex:1499-1697`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem avgOver_directLinePointDist_line_add_smul (D : DirectLdParams)
    (g : (Fin D.m → DirectScalarQ D) → ℝ) :
    avgOver ((directLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (line.base + t • line.direction))) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
  classical
  have haxis :
      avgOver (directALinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    rw [directALinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => coordinateDirection w.1) g
  have hdiag :
      avgOver (directDLinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    rw [directDLinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => directPrefixProjection w.1 w.2) g
  rw [Distribution.avgOver_map, directLinePointDist, avgOver_mix, haxis, hdiag]
  ring

/-! ## The two source blocks of a sub-line point -/


/-- Averaging a function of the two source blocks of the point at a uniform
affine parameter on an extended line of the sub-line law is averaging it at
two independent uniform points of the source space.  This is the input of the
three scalar estimates `lem:claim-17-1`, `lem:claim-17-2`, and
`lem:claim-17-3`, blueprint `ch15_qpbt_combining.tex:2651-2830`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1209`. -/
theorem SubLineWitness.avgOver_projX_projZ (P : AdmissibleParams)
    (sublines : SubLineWitness P)
    (f : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) → ℝ) :
    avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t =>
            f (projX (directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
      avgOver (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) f := by
  classical
  have hpair :
      (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX (directPointToPauli P u),
          projZ (directPointToPauli P u))) =
        uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) := by
    rw [uniformDistribution_prod]
    exact uniformDistribution_map_projX_projZ_pauli P
  have hmarginal :
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => f (projX (directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
        avgOver ((directLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
              (fun t => f (projX (directPointToPauli P
                  (line.base + t • line.direction)),
                projZ (directPointToPauli P
                  (line.base + t • line.direction))))) := by
    rw [← sublines.extended_marginal, Distribution.avgOver_map]
  refine hmarginal.trans ?_
  refine (avgOver_directLinePointDist_line_add_smul P.extendedDirectLd
    (fun u => f (projX (directPointToPauli P u),
      projZ (directPointToPauli P u)))).trans ?_
  rw [← hpair, Distribution.avgOver_map]

end

end MIPStarRE.QPBT
