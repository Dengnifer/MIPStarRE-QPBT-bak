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

open MIPStarRE.LDT MIPStarRE.Quantum DistanceCalculus
open scoped BigOperators

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

/-- The Born weight of two block diagonal operators on the correlated state
is the uniform average of the original Born weights in matching blocks.
In particular, the two players' hidden samples are correlated, not sampled
independently. -/
theorem correlatedPairState_born (D : DirectLdParams) (S : Strategy (directLdGame D))
    (A : PairRegister D → Op S.ιA) (B : PairRegister D → Op S.ιB) :
    stateQForm (correlatedPairState D S)
        (heteroKron (Matrix.blockDiagonal A) (Matrix.blockDiagonal B)) =
      avgOver (uniformDistribution (PairRegister D))
        (fun register => stateQForm S.ψ (heteroKron (A register) (B register))) := by
  have hcoord (i : S.ιA) (j : S.ιB) (r s : PairRegister D) :
      correlatedPairState D S ((i, r), (j, s)) =
        if r = s then S.ψ (i, j) * (Real.sqrt (Fintype.card (PairRegister D) : ℝ) : ℂ)⁻¹
        else 0 := by
    simp [correlatedPairState, reindexState, vecTensor, eprState, prodShuffle]
  have hscalar : (Real.sqrt (Fintype.card (PairRegister D) : ℝ) : ℂ)⁻¹ ^ 2 =
      (Fintype.card (PairRegister D) : ℂ)⁻¹ := by
    simpa only [pow_two] using inv_sqrt_natCast_mul_self (Fintype.card (PairRegister D))
  have hamp : inner ℂ (correlatedPairState D S)
      (applyOperatorToState (heteroKron (Matrix.blockDiagonal A) (Matrix.blockDiagonal B))
        (correlatedPairState D S)) =
      (Fintype.card (PairRegister D) : ℂ)⁻¹ *
        ∑ register, inner ℂ S.ψ (applyOperatorToState (heteroKron (A register) (B register))
          S.ψ) := by
    unfold applyOperatorToState heteroKron Matrix.kronecker
    simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec]
    simp_rw [← Finset.univ_product_univ, Finset.sum_product]
    simp [hcoord, Matrix.blockDiagonal_apply, mul_assoc, mul_comm]
    ring_nf
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring_nf
    rw [Finset.sum_comm]
    simp only [Fintype.card_pi, Nat.cast_prod] at hscalar
    rw [hscalar]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun register _ => ?_
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold stateQForm
  rw [hamp, avgOver_uniform_eq_inv_card_mul_sum]
  rw [show (Fintype.card (PairRegister D) : ℂ)⁻¹ =
      Complex.ofReal ((Fintype.card (PairRegister D) : ℝ)⁻¹) from
    (Complex.ofReal_inv (Fintype.card (PairRegister D) : ℝ)).symm]
  simp only [Complex.re_ofReal_mul, Complex.re_sum]

end

end MIPStarRE.QPBT.TensorCodeImport
