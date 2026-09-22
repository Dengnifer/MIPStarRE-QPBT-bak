import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Questions

/-!
# Subcube pairs and diagonal samples

The tensor-code commutation test sends two points of a hidden subcube. Its
subcubes fix a suffix, whereas the classical low-degree test fixes a prefix.
Reversing coordinates and replacing the independent second point by its
difference from the first gives the exact comparison of these sampling laws.
The hidden index is not included in the pair question.

These are auxiliary results for the open tensor-code import, not a strategy
reduction or a proof of tensor-code soundness.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272,443-458`
- Ji et al., arXiv:2111.08131v3, Figure 1 (subcube commutation test).
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
- Blueprint `lem:ld-soundness` (the printed proof route remains open).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT

noncomputable section

/-- Two independent points of a uniform hidden subcube, with the suffix
convention of Figure 1 of arXiv:2111.08131v3. The shared suffix is taken from
`sample.point`; the free coordinates of the second point are taken from the
independent uniform `sample.direction`. -/
def subcubePair (D : DirectLdParams) (sample : DirectLdSpace D) :
    (Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D) :=
  (fun j => sample.point j.rev,
    fun j => if j.rev.val < sample.index.val then sample.point j.rev
      else sample.direction j.rev)

/-- The ordered pair obtained from the two endpoints separated by one unit
of the sampled diagonal direction, with coordinates reversed. A zero
direction produces a repeated point, as allowed by the tensor-code test. -/
def diagonalPair (D : DirectLdParams) (sample : DirectLdSpace D) :
    (Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D) :=
  (fun j => sample.point j.rev,
    fun j => (sample.point + directPrefixProjection sample.index sample.direction) j.rev)

/-- The hidden-subcube pair distribution in the tensor-code test. Neither
the sampled index nor the remaining subcube data is sent to a prover. -/
def tensorPairDistribution (D : DirectLdParams) :
    Distribution ((Fin D.m → DirectScalarQ D) × (Fin D.m → DirectScalarQ D)) :=
  (uniformDistribution (DirectLdSpace D)).map (subcubePair D)

/-- Subtracting the first point from the independent second point is a
bijection of the underlying uniform samples. -/
def pairDifferenceEquiv (D : DirectLdParams) : DirectLdSpace D ≃ DirectLdSpace D where
  toFun sample := ⟨sample.point, sample.index, sample.direction - sample.point⟩
  invFun sample := ⟨sample.point, sample.index, sample.direction + sample.point⟩
  left_inv sample := by simp
  right_inv sample := by simp

/-- Exact comparison of the hidden-subcube pair law with diagonal sampling.
This includes repeated points and forgets the hidden index on both sides;
it makes no assertion about measurements or game values. -/
theorem tensorPairDistribution_eq_diagonal (D : DirectLdParams) :
    tensorPairDistribution D =
      (uniformDistribution (DirectLdSpace D)).map (diagonalPair D) := by
  rw [← uniformDistribution_map_equiv (pairDifferenceEquiv D), Distribution.map_map]
  unfold tensorPairDistribution
  congr 1
  funext sample
  apply Prod.ext
  · rfl
  · funext j
    change (if j.rev.val < sample.index.val then sample.point j.rev
        else sample.direction j.rev) =
      sample.point j.rev + (if j.rev.val < sample.index.val then 0
        else sample.direction j.rev - sample.point j.rev)
    split_ifs <;> simp

/-- Translation by the projected direction preserves uniform sampling of
the point, index, and unrestricted direction. -/
def endpointShiftEquiv (D : DirectLdParams) : DirectLdSpace D ≃ DirectLdSpace D where
  toFun sample :=
    ⟨sample.point + directPrefixProjection sample.index sample.direction,
      sample.index, sample.direction⟩
  invFun sample :=
    ⟨sample.point - directPrefixProjection sample.index sample.direction,
      sample.index, sample.direction⟩
  left_inv sample := by simp
  right_inv sample := by simp

/-- The second endpoint and the sampled diagonal line have exactly the
original line/point law. The line retains its index and its full projected
direction; no uniformity conditional on a nonzero direction is assumed. -/
theorem diagonal_endpoint_distribution (D : DirectLdParams) :
    (uniformDistribution (DirectLdSpace D)).map (fun sample =>
      (directDLineDescOf D sample,
        sample.point + directPrefixProjection sample.index sample.direction)) =
      directDLinePointDist D := by
  calc
    _ = ((uniformDistribution (DirectLdSpace D)).map (endpointShiftEquiv D)).map
        (fun sample => (directDLineDescOf D sample, sample.point)) := by
      rw [Distribution.map_map]
      congr 1
      funext sample
      apply Prod.ext
      · change directDLineDescOf D sample = directDLineDescOf D
          ⟨sample.point + directPrefixProjection sample.index sample.direction,
            sample.index, sample.direction⟩
        unfold directDLineDescOf
        have hbase := lineRepMap_add_smul
          (directPrefixProjection sample.index sample.direction) sample.point
          (1 : DirectScalarQ D)
        simp only [one_smul] at hbase
        simp only [hbase]
      · rfl
    _ = directDLinePointDist D := by
      rw [uniformDistribution_map_equiv]
      rfl

end

end MIPStarRE.QPBT.TensorCodeImport
