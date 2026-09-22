import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue

/-!
# Tensor-code weights applied to source branch losses

This module proves the scalar factor `3/2` for the tensor-code weights
applied to actual classical low-degree branch rejection probabilities. It
does not identify this weighted sum with a tensor-code strategy's rejection
probability: that requires the separate measurement and predicate comparisons.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186,320-392`
- Ji et al., arXiv:2111.08131v3, Figure 2 and Definition 4.6.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

noncomputable section

/-- Source branch rejection probabilities reweighted by the tensor-code
test: mass `1/3` for each role-symmetric cross-test and mass `1/9` for
each of the three synchronicity tests. This is a source loss sum, not the
value of a constructed tensor-code strategy. -/
def weightedSourceRejection (D : DirectLdParams) (S : Strategy (directLdGame D)) : ℝ :=
  let B := directLdBranchRejectionProbability D S
  (B (.aline, .point) + B (.point, .aline) +
    B (.dline, .point) + B (.point, .dline)) / 6 +
    (B (.point, .point) + B (.aline, .aline) + B (.dline, .dline)) / 9

/-- On the source game's valid domain, the tensor-weighted source loss of
the established correlated seed lift is at most `3/2` times the original
rejection probability. This holds for arbitrary strategies and simultaneity;
it is only the branch-weight part of the one-coordinate tensor reduction. -/
theorem weighted_source_rejection_le (L : LdParams) (S : Strategy (ldGame L)) :
    weightedSourceRejection L.toDirectLdParams (ldStrategyToDirect L S) ≤
      (3 / 2 : ℝ) * (1 - S.value) := by
  let D := L.toDirectLdParams
  let T := ldStrategyToDirect L S
  have hnonneg := directLdBranchRejectionProbability_nonneg D T
  rw [← ldStrategyToDirect_value_eq L S,
    ← directLdRejectionProbability_eq_one_sub_value D T,
    directLdRejectionProbability, avgOver_ldType_pair]
  unfold weightedSourceRejection
  dsimp only
  linarith [hnonneg (.point, .point), hnonneg (.aline, .aline),
    hnonneg (.dline, .dline), hnonneg (.aline, .dline), hnonneg (.dline, .aline)]

end

end MIPStarRE.QPBT.TensorCodeImport
