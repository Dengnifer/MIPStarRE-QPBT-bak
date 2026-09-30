# Issue 729 quantitative baseline blueprint coverage

Date: 2026-09-29

Frozen source commit: `4526886890dc72886bc81032366557082267ef78`

This ledger records the complete correspondence for the quantitative QPBT
baseline admitted in issue #729. The frozen interface contains 114 public
mathematical declarations: 24 definitions and 90 theorems. Each declaration
below is linked exactly once from a Lean-only quantitative entry in Chapters
13--16. The entries display the load-bearing domains, hypotheses, constants,
exponents, and conclusions; they do not replace or redirect any source-labelled
paper statement.

All 114 names elaborate against the frozen source. The 90 theorems were also
checked with `#print axioms`; none depends on `sorryAx`, and their closures use
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` as
applicable. The supplied-global-witness results remain explicitly conditional in
`thm:qld-supplied-global-consistency-explicit`; no later quantitative
global-pair, component-bound, or final-soundness declaration is listed or
marked proved. There are no unresolved declarations in this inventory.

| Kind | Lean declaration | Frozen source | Blueprint label |
|---|---|---|---|
| `theorem` | `MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean:226` | `thm:qld-rounded-polynomials-explicit` |
| `theorem` | `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean:171` | `thm:qld-rounded-polynomials-explicit` |
| `theorem` | `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_scalar_mass_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLineGame/ScalarNonlinearMass.lean:173` | `thm:qld-rounded-polynomials-explicit` |
| `theorem` | `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean:341` | `thm:qld-rounded-polynomials-explicit` |
| `theorem` | `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_wrong_variable_mass_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean:196` | `thm:qld-rounded-polynomials-explicit` |
| `theorem` | `MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit` | `MIPStarRE/QPBT/Combining/Points/Consistency.lean:370` | `thm:qld-combined-points-explicit` |
| `theorem` | `MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit` | `MIPStarRE/QPBT/Combining/Points/Commutation.lean:363` | `thm:qld-combined-points-explicit` |
| `theorem` | `MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit` | `MIPStarRE/QPBT/Combining/Points/Sandwich.lean:194` | `thm:qld-combined-points-explicit` |
| `theorem` | `MIPStarRE.QPBT.ProjectiveSetting.sandwich_point_ordered_dist_le_explicit` | `MIPStarRE/QPBT/Combining/Points/Sandwich.lean:148` | `thm:qld-combined-points-explicit` |
| `theorem` | `MIPStarRE.QPBT.ProjectiveSetting.twisted_commutator_avg_le_explicit` | `MIPStarRE/QPBT/Observables/ExpandedCommutation.lean:188` | `thm:qld-twisted-commutation-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_bob_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:278` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/AnticommutingObs.lean:729` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/TwistedCommutation.lean:278` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:180` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean:449` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/TwistedCommutation.lean:350` | `thm:qld-twisted-commutation-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:377` | `thm:qld-twisted-commutation-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean:265` | `thm:qld-point-observable-halves-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_cons_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean:346` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_cons_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:292` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_cons_swapped_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:63` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean:136` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:110` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_comm_swapped_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:121` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_low_degree_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:616` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_low_degree_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean:245` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_magic_square_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean:483` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_ms_cons_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean:176` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_ms_cons_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:509` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_ms_cons_swapped_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:159` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:782` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_interchanged_explicit` | `MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean:437` | `thm:qld-win-implications-explicit` |
| `theorem` | `MIPStarRE.QPBT.arbitrary_strategy_isometry_bounds_explicit_baseline` | `MIPStarRE/QPBT/Test/Soundness/NaimarkAssembly.lean:42` | `thm:qld-isometry-baselines-explicit` |
| `theorem` | `MIPStarRE.QPBT.arbitrary_strategy_raw_isometry_bounds_explicit_baseline` | `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransfer.lean:666` | `thm:pauli-soundness-explicit-baseline` |
| `theorem` | `MIPStarRE.QPBT.coarse_commutator_bound_explicit` | `MIPStarRE/QPBT/Games/Sandwich/Pasting/CodewordConsistency.lean:89` | `thm:qld-pasting-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/Construction.lean:200` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_line_measurement_consistency_explicit` | `MIPStarRE/QPBT/Combining/Lines/Construction.lean:515` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_line_restored_defect_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/Construction.lean:314` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/Conditioning.lean:66` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:376` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:257` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.delta_extract_le_delta_qld_explicit` | `MIPStarRE/QPBT/Extraction/Unitary.lean:268` | `thm:qld-extraction-witness-explicit` |
| `theorem` | `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_explicit` | `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:114` | `thm:qld-direct-soundness-explicit` |
| `theorem` | `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit` | `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:245` | `thm:qld-direct-soundness-explicit` |
| `theorem` | `MIPStarRE.QPBT.direct_ld_transport_constants_explicit` | `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Error.lean:461` | `thm:qld-direct-soundness-explicit` |
| `theorem` | `MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/EvaluatedPauliConsistency.lean:64` | `thm:qld-supplied-global-consistency-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_combined_lines_witness_of_points_witness_explicit` | `MIPStarRE/QPBT/Combining/Lines.lean:119` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_combined_points_witness_explicit` | `MIPStarRE/QPBT/Combining/Points.lean:67` | `thm:qld-combined-points-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_extended_lines_witness_established_of_points_witness_explicit` | `MIPStarRE/QPBT/Combining/Apply.lean:218` | `thm:qld-extended-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/StateExtraction.lean:109` | `thm:qld-extraction-witness-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_extraction_witness_explicit` | `MIPStarRE/QPBT/Extraction/SourceUnitary.lean:24` | `thm:qld-extraction-witness-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_extraction_witness_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/Unitary.lean:173` | `thm:qld-extraction-witness-explicit` |
| `theorem` | `MIPStarRE.QPBT.exists_global_pair_witness_explicit` | `MIPStarRE/QPBT/Combining/Apply.lean:308` | `thm:qld-global-pair-witness-explicit` |
| `theorem` | `MIPStarRE.QPBT.exp_line_point_cons_explicit'` | `MIPStarRE/QPBT/Observables/LineMeasurement.lean:315` | `thm:qld-expanded-comparisons-explicit` |
| `theorem` | `MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit` | `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:205` | `thm:qld-combined-lines-explicit` |
| `theorem` | `MIPStarRE.QPBT.exp_point_self_cons_explicit` | `MIPStarRE/QPBT/Observables/PointConsistency.lean:716` | `thm:qld-expanded-comparisons-explicit` |
| `theorem` | `MIPStarRE.QPBT.extracted_obs_self_consistent_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/SwappedConsistency.lean:104` | `thm:qld-supplied-global-consistency-explicit` |
| `def` | `MIPStarRE.QPBT.globalPairBoundConstant` | `MIPStarRE/QPBT/Combining/ErrorBounds.lean:353` | `def:qld-global-pair-generic-constants` |
| `def` | `MIPStarRE.QPBT.globalPairBoundPower` | `MIPStarRE/QPBT/Combining/ErrorBounds.lean:346` | `def:qld-global-pair-generic-constants` |
| `theorem` | `MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit` | `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:175` | `thm:qld-supplied-global-consistency-explicit` |
| `theorem` | `MIPStarRE.QPBT.global_pair_error_bound_explicit` | `MIPStarRE/QPBT/Combining/ErrorBounds.lean:370` | `thm:qld-global-pair-bound-explicit` |
| `def` | `MIPStarRE.QPBT.heterogeneousPastingError` | `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:356` | `def:qld-heterogeneous-pasting-error-explicit` |
| `theorem` | `MIPStarRE.QPBT.heterogeneous_pasting_error_is_poly_err₂` | `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:360` | `thm:qld-pasting-explicit` |
| `theorem` | `MIPStarRE.QPBT.one_le_pauli_baseline_extended_line_constant` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:202` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.one_le_pauli_baseline_line_constant` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:40` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.one_le_pauli_baseline_passing_constant` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:404` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.one_le_pauli_baseline_point_constant` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:26` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit` | `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:450` | `thm:qld-pasting-explicit` |
| `theorem` | `MIPStarRE.QPBT.op_dist_sq_commutator_right_le_explicit` | `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:675` | `thm:qld-pasting-explicit` |
| `theorem` | `MIPStarRE.QPBT.pasting_error_heterogeneous_explicit` | `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:271` | `thm:qld-pasting-explicit` |
| `theorem` | `MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit` | `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:131` | `thm:qld-pasting-explicit` |
| `def` | `MIPStarRE.QPBT.pauliBaselineCommutatorConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:22` | `def:pauli-observable-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliBaselineExtendedLineConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:48` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineExtendedLineError` | `MIPStarRE/QPBT/ExplicitConstants.lean:54` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineExtractionConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:94` | `def:qld-extraction-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliBaselineGlobalAbsorptionConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:75` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineGlobalAbsorptionPower` | `MIPStarRE/QPBT/ExplicitConstants.lean:84` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineGlobalPairConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:87` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineGlobalPairPower` | `MIPStarRE/QPBT/ExplicitConstants.lean:91` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineLineConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:39` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineLineError` | `MIPStarRE/QPBT/ExplicitConstants.lean:43` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineLowDegreeConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:69` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineLowDegreePower` | `MIPStarRE/QPBT/ExplicitConstants.lean:72` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselinePassingConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:59` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselinePassingError` | `MIPStarRE/QPBT/ExplicitConstants.lean:64` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselinePointConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:30` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselinePointError` | `MIPStarRE/QPBT/ExplicitConstants.lean:35` | `def:qld-baseline-scalar-functions` |
| `def` | `MIPStarRE.QPBT.pauliBaselineProjectiveConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:97` | `def:qld-extraction-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliBaselineProjectivePower` | `MIPStarRE/QPBT/ExplicitConstants.lean:102` | `def:qld-extraction-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliBaselineTwistedConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:26` | `def:pauli-observable-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliSoundnessBaselineConstant` | `MIPStarRE/QPBT/ExplicitConstants.lean:106` | `def:qld-extraction-baseline-constants` |
| `def` | `MIPStarRE.QPBT.pauliSoundnessBaselinePower` | `MIPStarRE/QPBT/ExplicitConstants.lean:110` | `def:qld-extraction-baseline-constants` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_actual_rounded_global_pair_error_bound` | `MIPStarRE/QPBT/Combining/ActualErrorBounds.lean:158` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_combining_bound` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:229` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_conditioned_line_bound` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:64` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_direct_global_pair_error_bound` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:632` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_direct_passing_bound` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:422` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_extended_line_error_is_poly_err₂` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:217` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_global_absorption_bound` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:567` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_line_error_is_poly_err₂` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:54` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_passing_error_is_poly_err₂` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:411` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_baseline_point_error_is_poly_err` | `MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean:33` | `thm:qld-baseline-scalar-bounds` |
| `theorem` | `MIPStarRE.QPBT.pauli_edge_card` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:468` | `lem:pauli-edge-card-explicit` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_delta_qld_of_extraction_witness_explicit` | `MIPStarRE/QPBT/Test/Soundness/OperatorTransfer.lean:251` | `thm:qld-isometry-baselines-explicit` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_explicit_baseline` | `MIPStarRE/QPBT/Test/Soundness.lean:51` | `thm:pauli-soundness-explicit-baseline` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_qubit_explicit_baseline` | `MIPStarRE/QPBT/Test/QubitForm.lean:421` | `thm:pauli-soundness-explicit-baseline` |
| `theorem` | `MIPStarRE.QPBT.projective_setting_isometry_bounds_explicit_baseline` | `MIPStarRE/QPBT/Test/Soundness/ProjectiveSetting.lean:36` | `thm:qld-isometry-baselines-explicit` |
| `theorem` | `MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:309` | `thm:qld-subline-overlaps-explicit` |
| `theorem` | `MIPStarRE.QPBT.subline_remove_x_factor_at_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:32` | `thm:qld-subline-overlaps-explicit` |
| `theorem` | `MIPStarRE.QPBT.subline_z_term_near_one_at_explicit` | `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:192` | `thm:qld-subline-overlaps-explicit` |
| `theorem` | `MIPStarRE.QPBT.tilde_m_consistent_point_meas'_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean:247` | `thm:qld-supplied-global-consistency-explicit` |
| `theorem` | `MIPStarRE.QPBT.tilde_m_consistent_point_meas_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean:107` | `thm:qld-supplied-global-consistency-explicit` |
| `theorem` | `MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_card` | `MIPStarRE/QPBT/Extraction/ObservableConsistency.lean:50` | `thm:qld-supplied-global-consistency-explicit` |
| `theorem` | `MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_explicit` | `MIPStarRE/QPBT/Extraction/ObservableConsistency.lean:82` | `thm:qld-supplied-global-consistency-explicit` |
