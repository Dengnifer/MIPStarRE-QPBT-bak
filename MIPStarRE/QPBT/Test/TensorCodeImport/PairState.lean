import MIPStarRE.QPBT.Test.TensorCodeImport.PairMeasurement

/-!
# The correlated pair-register state

Both players receive copies of the same finite register of compatible
diagonal samples. Tensoring the original state with a maximally correlated
register state preserves normalization and realizes the common block choice
used by the projective pair measurements.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-458`
- Ji et al., arXiv:2111.08131v3, Definition 4.5 and Figure 2.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

noncomputable section

/-- Adjoin a maximally correlated copy of the finite pair register to each
player's carrier. The original state is retained as a tensor factor. -/
def correlatedPairState (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    EuclideanSpace ℂ ((S.ιA × PairRegister D) × (S.ιB × PairRegister D)) :=
  reindexState prodShuffle (vecTensor S.ψ (eprState (PairRegister D)))

/-- The state accompanying the constructed pair measurements has unit norm. -/
theorem correlatedPairState_norm (D : DirectLdParams) (S : Strategy (directLdGame D)) :
    ‖correlatedPairState D S‖ = 1 := by
  rw [correlatedPairState, reindexState_norm_eq, vecTensor_norm_eq,
    S.ψ_norm, eprState_norm, one_mul]

end

end MIPStarRE.QPBT.TensorCodeImport
