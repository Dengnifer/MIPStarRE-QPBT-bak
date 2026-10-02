module

public import MIPStarRE.QPBT.Combining.Apply
public import MIPStarRE.QPBT.Combining.QuantitativeNativeGlobalPairScalars

/-!
# Quantitative global polynomial-pair construction

This module combines the native direct low-degree estimate with the existing
point and extended-line constructions. The resulting witness uses the actual
rounded polynomial-pair measurements at their concrete capped error. A
separate corollary records the polynomial envelope printed in the source.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`
* blueprint `lem:qld-4-7`
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- The projective global polynomial-pair witness at the concrete native
mixed error.  This construction uses no scalar comparison with a common
polynomial envelope. -/
theorem exists_quantitative_global_pair_witness_native
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e)
    (S : ProjectiveSetting P e) :
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e
          (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
      (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))
    let lambda := directNativeError P.extendedDirectLd passing
    Nonempty (GlobalPairWitness S
      (nativeGlobalPairError P lambda (pauliBaselinePointError e))) := by
  intro passing lambda
  obtain ⟨points⟩ := exists_combined_points_witness_explicit P e S
  obtain ⟨lines⟩ :=
    exists_extended_lines_witness_established_of_points_witness_explicit
      P e S points
  obtain ⟨pair⟩ := ExtendedLineGame.pair_witness_of_points_lines_at_native_error P e
    (pauliBaselinePointError e)
    ((P.m : ℝ) * pauliBaselineExtendedLineError e
      (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))) S points lines
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact direct_native_error_nonneg _ hpassing
  have hpoint : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  refine ⟨{ pair with point_consistent_alice := ?_, point_consistent_bob := ?_ }⟩
  · intro W
    unfold nativeGlobalPairError
    refine le_min ?_ ?_
    · unfold consistencyDefect
      calc
        _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
          avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
            S .AA' .BA'' (by trivial) _ _
        _ = 1 := avgOver_const_of_isProbability _
          (uniformDistribution_isProbability _) 1
    · simpa only [passing, lambda, Nat.cast_mul] using
        pair.point_consistent_alice W
  · intro W
    unfold nativeGlobalPairError
    refine le_min ?_ ?_
    · unfold consistencyDefect
      calc
        _ ≤ avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun _ => 1) :=
          avgOver_mono _ _ _ fun u => consistencyDefect_integrand_le_one
            S .BB' .AB'' (by trivial) _ _
        _ = 1 := avgOver_const_of_isProbability _
          (uniformDistribution_isProbability _) 1
    · simpa only [passing, lambda, Nat.cast_mul] using
        pair.point_consistent_bob W

/-- The quantitative global-pair witness at the concrete native mixed error.
The returned equality identifies the witness error with `nativeGlobalPairError`,
while the final inequality is only a common-envelope consequence. -/
theorem exists_quantitative_global_pair_witness_at_native_error
    (P : AdmissibleParams) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hr1 : ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) ≤ 1)
    (S : ProjectiveSetting P e) :
    let passing := directPassingErrorEnvelope
      (pauliBaselinePointError e + (P.m : ℝ) *
        pauliBaselineExtendedLineError e
          (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))
      (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ))
    let lambda := directNativeError P.extendedDirectLd passing
    ∃ g : ℝ,
      g = nativeGlobalPairError P lambda (pauliBaselinePointError e) ∧
      0 ≤ g ∧
      g ≤ 10000000 * (((P.m * P.d : ℕ) : ℝ) ^ (4 : ℕ)) *
        quantitativeGlobalPairEnvelope P e ∧
      Nonempty (GlobalPairWitness S g) := by
  intro passing lambda
  let g := nativeGlobalPairError P lambda (pauliBaselinePointError e)
  have hpassing : 0 ≤ passing := by
    dsimp [passing, directPassingErrorEnvelope]
    positivity
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda]
    exact direct_native_error_nonneg _ hpassing
  have hpoint : 0 ≤ pauliBaselinePointError e := by
    unfold pauliBaselinePointError
    exact mul_nonneg
      (le_trans zero_le_one one_le_pauli_baseline_point_constant)
      (Real.rpow_nonneg he _)
  have hbound := quantitative_native_global_pair_error_bound P e he he1 hr1
  have hw := exists_quantitative_global_pair_witness_native P e he S
  refine ⟨g, rfl, native_global_pair_error_nonneg P hlambda hpoint, ?_, ?_⟩
  · simpa only [g, passing, lambda] using hbound
  · simpa only [g, passing, lambda] using hw

/-- Weakening: the concrete native-error witness implies this fixed
polynomial-envelope form, matching the error shape printed in paper
`lem:qld-4-7`. -/
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
  obtain ⟨g, _, hg0, hbound, hpair⟩ :=
    exists_quantitative_global_pair_witness_at_native_error P e he he1 hr1 S
  refine ⟨g, hg0, ?_, hpair⟩
  simpa only [quantitativeGlobalPairEnvelope] using hbound

end

end MIPStarRE.QPBT
