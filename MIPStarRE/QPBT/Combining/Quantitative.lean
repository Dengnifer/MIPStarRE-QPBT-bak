import MIPStarRE.QPBT.Combining.Apply
import MIPStarRE.QPBT.Combining.QuantitativeScalars

/-!
# Quantitative global polynomial-pair construction

This module combines the coefficient-`30` direct low-degree estimate with the
existing point and extended-line constructions.  The resulting witness uses
the actual rounded polynomial-pair measurements, with the final consistency
error capped by one.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* blueprint `lem:qld-4-7`
-/

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The quantitative rounded global-pair construction used by the final QPBT
soundness argument.  It retains the complete projective measurements produced
by the coefficient-`30` construction and caps each of their four consistency
defects by the same explicit error `g`. -/
theorem exists_quantitative_global_pair_witness
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr1 : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1)
    (S : ProjectiveSetting P e) :
    ∃ g : ℝ,
      0 ≤ g ∧
      g ≤ 10000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        (Real.rpow e quantitativeGlobalPairPower +
          Real.rpow (P.q : ℝ) (-quantitativeGlobalPairPower) +
          Real.rpow 2
            (-(quantitativeGlobalPairPower * ((P.m * P.d : ℕ) : ℝ)))) ∧
      Nonempty (GlobalPairWitness S g) := by
  obtain ⟨points⟩ := exists_combined_points_witness_explicit P e S
  obtain ⟨lines⟩ :=
    exists_extended_lines_witness_established_of_points_witness_explicit
      P e S points
  obtain ⟨pair⟩ := ExtendedLineGame.pair_witness_of_points_lines_quantitative P e
    (pauliBaselinePointError e)
    ((P.m : ℝ) * pauliBaselineExtendedLineError e
      (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))) S points lines
  let delta := deltaLd 30 quantitativeLowDegreePower
    (directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e
          (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
      (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
    P.q (2 * P.m + 2) P.d 1
  let eta := delta + Real.sqrt (220 * Real.rpow delta (1 / 4 : ℝ)) +
    2 * Real.sqrt (2 * delta)
  let pairError := 8 * (4 * eta + 8 * pauliBaselinePointError e) +
    (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)
  let g := min 1 pairError
  have hdelta : 0 ≤ delta := by
    dsimp [delta, deltaLd, directPassingErrorEnvelope]
    positivity
  have hpoint : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hpairError : 0 ≤ pairError := by
    dsimp [pairError]
    positivity
  have hbound := quantitative_actual_rounded_global_pair_error_bound P e he he1 hr1
  refine ⟨g, le_min (by norm_num) hpairError, ?_, ?_⟩
  · simpa only [g, pairError, eta, delta, quantitativeGlobalPairEnvelope,
      Nat.cast_mul] using hbound
  · refine ⟨{ pair with point_consistent_alice := ?_, point_consistent_bob := ?_ }⟩
    · intro W
      change _ ≤ min 1 pairError
      refine le_min ?_ ?_
      · unfold consistencyDefect
        calc
          _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
            avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
              S .AA' .BA'' (by trivial) _ _
          _ = 1 := avgOver_const_of_isProbability _
            (uniformDistribution_isProbability _) 1
      · simpa only [pairError, eta, delta, Nat.cast_mul] using
          pair.point_consistent_alice W
    · intro W
      change _ ≤ min 1 pairError
      refine le_min ?_ ?_
      · unfold consistencyDefect
        calc
          _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
            avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
              S .BB' .AB'' (by trivial) _ _
          _ = 1 := avgOver_const_of_isProbability _
            (uniformDistribution_isProbability _) 1
      · simpa only [pairError, eta, delta, Nat.cast_mul] using
          pair.point_consistent_bob W

end

end MIPStarRE.QPBT
