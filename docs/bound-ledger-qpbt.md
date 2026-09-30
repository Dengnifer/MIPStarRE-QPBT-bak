# QPBT bound ledger

> **Draft status, September 30, 2026.** This ledger is a prospective record for
> the quantitative QPBT correction in PR #736. It is pending integration of the
> degree-two soundness theorem and the native-LDT-error propagation. A row whose
> stated-bound cell begins `PROPOSED, UNPROVED` names an absent sibling and does
> not assert that Lean proves the target. Its disposition records the intended
> post-proof classification only. The other rows were inspected in the
> published quantitative source at commit `b9cf07572bc08c48b81947054a11f23e6e577ac5`
> or in its frozen LDT dependency. The completion gate's static `DELEGATED`
> result checks table shape, not mathematical coverage, proof closure, or track
> completion.

This ledger covers stage estimates on the registered headline paths to
`MIPStarRE.QPBT.pauli_soundness`, `MIPStarRE.QPBT.pauli_soundness_qubit`,
`MIPStarRE.QPBT.exists_ld_soundness`, and
`MIPStarRE.QPBT.exists_spcc_value_one`. For compact locators, `O/`, `C/`,
`E/`, `G/`, and `T/` denote the `Observables/`, `Combining/`, `Extraction/`,
`Games/`, and `Test/` directories under `MIPStarRE/QPBT/`. A locator on a
proposed declaration identifies the existing implementation anchor, not an
existing declaration.

Write

\[
 e=\min(\varepsilon,1),\qquad n=md,\qquad r=n/q,\qquad
 \tau=1/8192,\qquad b=1/67108864,
\]

and let \(E_t=e^t+q^{-t}+2^{-tn}\). For the native direct-LDT input, set

\[
 \Lambda_h(t)=\min\!\left\{1,
 400000h^{5/4}d^{1/4}
 \left[(3t)^\tau+(d/q)^\tau+\exp(-4hd)\right]\right\}.
\]

For a supplied direct-LDT error \(\lambda\), define

\[
 \eta(\lambda)=\lambda+\sqrt{220}\lambda^{1/8}
   +2\sqrt2\lambda^{1/2},
 \qquad
 G(\lambda,Q)=\min\!\left\{1,
 32\eta(\lambda)+64Q+\frac{12n+4d+14}{q}\right\}.
\]

The extraction notation is

\[
 X=2800\left(10^7n^4E_{2b}+\sqrt e+r\right),\qquad
 Y=48g+2752e+4r.
\]

For the inherited fixed-constant route, write

\[
\begin{aligned}
c&=1024(172+\sqrt{344}),\\
t_0&=2(2c+4886363136+4),\\
Q_0&=10560(344+3t_0)+24t_0+11008,\\
L_0&=115(1+(16Q_0+8320)^{1/8})+1,\\
H_0&=1+6(\sqrt{Q_0}+L_0^{1/4}+Q_0^{1/4}+1),\\
D_0&=4+3\sqrt{Q_0+H_0}.
\end{aligned}
\]

Let \(Q=Q_0e^{1/8}\), \(L=L_0(e^{1/64}+r^{1/4})\),
\(L_{\rm ext}=mH_0(e^{1/256}+r^{1/16})\),
\(H_p(a,z)=115(a^{1/4}+z^{1/8})\), and let \(\rho\) be retained line mass.
When the native error is propagated, put \(J=4\eta(\Lambda_M(T))+8Q\), where
\(M=2m+2\) and \(T=3(\sqrt{Q+L_{\rm ext}}+r)\).

The historical explicit baseline uses

\[
\begin{aligned}
a_L&=2500000000,\quad \beta=1/80000,\\
A&=2[a_L4^{a_L}(D_0^\beta+2)+\sqrt{Q_0}+1]
  +a_L+\tfrac{33}{32}\beta+3,\\
a_G&=1024A,\quad a_P=16\cdot2800^2a_G,\\
a_0&=346\cdot21^3a_P^4,\quad b_0=1/5242880000.
\end{aligned}
\]

Here \(\Delta_{a,t}=a n^a(\varepsilon^t+q^{-t}+2^{-tn})\). The word
`sharp` concerns retained powers and separate error terms; coefficient-only
slack is reported in `docs/error-bounds.md`.

## Explicit headline status

The published source contains explicit fixed-constant siblings for
`pauli_soundness` and `pauli_soundness_qubit`, and exact perfect completeness
for `exists_spcc_value_one`. The general seed-indexed theorem
`exists_ld_soundness` still lacks its public explicit sibling: source inspection
finds witnesses \((10^{24},1/160000)\), with its first two errors retained at
\(E\) and its third at \(E+2\sqrt{9\varepsilon+E}+md/q\). That missing sibling
is tracked in #727 and prevents a C8 completion claim. The degree-two, mixed,
native-error, and exact-qubit declarations marked proposed below are also
unproved until the final #736 integration and axiom audit.

## Stage ledger

| Stage lemma | Stated bound | Bound the argument supports | Disposition |
|---|---|---|---|
| `MIPStarRE.QPBT.WinImplications.win_comm_explicit` — `O/WinImplications/Commuting.lean:136` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_cons_explicit` — same file `:346` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_interchanged_explicit` — `O/WinImplications/Approx.lean:110` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_cons_interchanged_explicit` — same file `:292` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_ms_cons_explicit` — `O/WinImplications/MagicSquare.lean:176` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_magic_square_explicit` — same file `:483` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_ms_cons_interchanged_explicit` — `O/WinImplications/Approx.lean:509` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_low_degree_explicit` — `O/WinImplications/LowDegree.lean:616` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_low_degree_interchanged_explicit` — `O/WinImplications/ApproxLines.lean:245` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_explicit` — `O/WinImplications/LowDegree.lean:782` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_interchanged_explicit` — `O/WinImplications/ApproxLines.lean:437` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit` — `O/WinImplications/CommutingObs.lean:265` | \(16\delta\) | Same squared-distance order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit` — same file `:449` | \(1024(c_1+\sqrt{c_2+c_3})\) | Calculated \(1536(c_1+c_2+c_3)\), after the missing complete-measurement adapter | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit` — `O/WinImplications/TwistedCommutation.lean:278` | \(c(e+\sqrt e)\) | Calculated \(792576e\) | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit` — `O/WinImplications/InterchangedCommutation.lean:180` | \(c(e+\sqrt e)\) | Same calculated linear bound, opposite orientation | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit` — `O/WinImplications/AnticommutingObs.lean:729` | \(4886363136e\) | Same linear error order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_bob_explicit` — `O/WinImplications/InterchangedCommutation.lean:278` | \(4886363136e\) | Same linear error order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit` — `O/WinImplications/TwistedCommutation.lean:350` | \((2c+4886363136+4)\sqrt e\) | Calculated linear commutation plus the existing linear anticommutation contribution | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit` — `O/WinImplications/InterchangedCommutation.lean:377` | Same square-root bound | Same calculated linear improvement | deferred #735 |
| `MIPStarRE.QPBT.twisted_commutator_avg_le_explicit` — `O/ExpandedCommutation.lean:188` | \(t_0\sqrt e\) | Calculated \(9774311424e\) | deferred #735 |
| `MIPStarRE.QPBT.exp_point_self_cons_explicit` — `O/PointConsistency.lean:716` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.exp_line_point_cons_explicit'` — `O/LineMeasurement.lean:315` | \(348\sqrt e\) | Existing proof first obtains \(172e\), independently capped by four; missing exported linear sibling | deferred #727 |
| `MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit` — `C/Points/Commutation.lean:363` | \(t_0\sqrt e\) | Linear bound after the #735 commutation adapter | deferred #735 |
| `MIPStarRE.QPBT.ProjectiveSetting.sandwich_point_ordered_dist_le_explicit` — `C/Points/Sandwich.lean:148` | \(t_0\sqrt e\) | Same commutator input; linear after #735 | deferred #735 |
| `MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit` — same file `:194` | \(688e\) | Linear in \(e\) | sharp |
| `MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit` — `C/Points/Consistency.lean:370` | \((344+3t_0)(e+\sqrt e)\) | Linear defect after the stronger commutator construction | deferred #735 |
| `MIPStarRE.QPBT.exists_combined_points_witness_explicit` — `C/Points.lean:67` | \(Q_0e^{1/8}\) | Calculated actual-witness target \(10^{15}e^{1/4}\) | deferred #735 |
| `MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit` — `C/Lines/PointComparison.lean:205` | \(1040(e+\sqrt e)\) | Linear bound after exposing the existing linear expanded-line comparison | deferred #727 |
| `MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit` — same file `:257` | \(8Q+2080(e+\sqrt e)\) | Same bound with its terms retained | sharp |
| `MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit` — same file `:376` | \(8Q+2080(e+\sqrt e)\) | Same orders; sharper incoming line estimate is a separate backlog item | sharp |
| `MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit` — `C/Lines/Conditioning.lean:66` | \((8Q+2080(e+\sqrt e))/\rho\) | Same conditional-probability scaling | sharp |
| `MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit` — `G/DistanceTheorems/Calculus.lean:450` | \(16\delta\) | Linear squared-distance bound | sharp |
| `MIPStarRE.QPBT.op_dist_sq_commutator_right_le_explicit` — same file `:675` | \(16\delta\) | Same bound on the other tensor factor | sharp |
| `MIPStarRE.QPBT.coarse_commutator_bound_explicit` — `G/Sandwich/Pasting/CodewordConsistency.lean:89` | \(32\delta\) | Linear squared-distance bound | sharp |
| `MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit` — `G/Sandwich/Pasting/Heterogeneous.lean:131` | \(H_p(\eta,\delta)\) | At the actual projective consumer, calculated \(307\delta+16\eta\); missing projective refinement | deferred #735 |
| `MIPStarRE.QPBT.pasting_error_heterogeneous_explicit` — same file `:271` | \(H_p(\eta,\delta)\) | Same projective refinement; heterogeneous transport is exact | deferred #735 |
| `MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit` — `C/Lines/Construction.lean:200` | \(H_p(r,(8Q+2080(e+\sqrt e))/\rho)\) | Apply the missing projective refinement to these actual measurements | deferred #735 |
| `MIPStarRE.QPBT.combined_line_restored_defect_le_explicit` — same file `:314` | \(\rho H_p(\cdots)+1/(2q)\) | Calculated \(2456Q+638560(e+\sqrt e)+17r\) | deferred #735 |
| `MIPStarRE.QPBT.combined_line_measurement_consistency_explicit` — same file `:515` | \(L\) | Retained capped restored expression; stronger projective route requires #735 | deferred #735 |
| `MIPStarRE.QPBT.exists_combined_lines_witness_of_points_witness_explicit` — `C/Lines.lean:119` | \(L\) | Same constructed measurements at the sharper restored error | deferred #735 |
| `MIPStarRE.QPBT.subline_remove_x_factor_at_explicit` — `C/ExtendedLines/Estimates.lean:32` | \(2\sqrt m(\delta_P^{1/4}+\delta_Q^{1/4})\) | Retain the underlying mixed root; export the term-specific dimension dependence | deferred #727 |
| `MIPStarRE.QPBT.subline_z_term_near_one_at_explicit` — same file `:192` | \(2\sqrt m(\delta_P^{1/4}+\delta_Q^{1/4}+e^{1/4})\) | Retain term-specific dimension factors before common-envelope absorption | deferred #727 |
| `MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit` — same file `:309` | \(6[\sqrt Q+\sqrt m(\delta_P^{1/4}+Q^{1/4}+e^{1/4})]\) | This explicit mixed expression is stronger than the later \(mH_0\) envelope | sharp |
| `MIPStarRE.QPBT.exists_extended_lines_witness_established_of_points_witness_explicit` — `C/Apply.lean:218` | \(L_{\rm ext}\) | Unit-capped mixed overlap expression from the previous row; missing witness interface retaining it | deferred #727 |
| `MIPStarRE.QPBT.ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope` — `C/ExtendedLineGame/PassingValue.lean:89` | \(T=3(\sqrt{Q+L_{\rm ext}}+r)\) | Existing seven-branch expression retains separate terms; calculated linear replacement \((7Q+20L_{\rm ext}+5r)/9\) needs #735 | deferred #735 |
| `MIPStarRE.LDT.Test.mainFormal` — `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300` | \(100000N^2h^4[(3t)^{1/40000}+(d/q)^{1/40000}+e^{-N/(2560000h^2)}]\) | Frozen sharper linear-triangle sibling below | necessary: retain the printed LDT thm:main-formal statement |
| `MIPStarRE.LDT.Test.main_formal_linear_triangle` — `MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean:147` | \(10000N^{1/4}h^{1/2}[(3t)^\tau+(d/q)^\tau+e^{-N/(640000h^2)}]\), capped by one | At \(N=2560000h^3d\), exactly \(\Lambda_h(t)\) | sharp |
| Proposed `MIPStarRE.QPBT.direct_coordinate_main_formal_at_native_error` — anchor `C/DirectLowDegree/Transport/Simultaneous.lean:164` | PROPOSED, UNPROVED: current quantitative wrapper uses \(\delta_{\rm LD}(30,\tau)\) | Three relations at \(\Lambda_h(t)\), with the same measurements | sharp |
| Proposed `MIPStarRE.QPBT.exists_direct_simultaneous_polynomial_measurements_at_native_error_of_k_eq_one` — anchor same file `:334` | PROPOSED, UNPROVED: missing sibling | Three tuple relations at \(\Lambda_h(t)\) | sharp |
| Proposed `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_at_native_error` — anchor `C/DirectLowDegree/Soundness.lean:335` | PROPOSED, UNPROVED: missing sibling | \(\Lambda_h(t)\) | sharp |
| Proposed `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_at_native_error` — anchor `C/DirectLowDegree/AnyStrategySoundness.lean:315` | PROPOSED, UNPROVED: missing sibling | \(\Lambda_h(t)\), with exact compression | sharp |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_quantitative` — `C/DirectLowDegree/Soundness.lean:335` | \(\delta_{\rm LD}(30,\tau)\) | Corollary of the proposed native-error result | necessary: paper lem:ld-soundness prints the common deltaLd form |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_quantitative` — `C/DirectLowDegree/AnyStrategySoundness.lean:315` | Same common deltaLd form | Same corollary after exact Naimark compression | necessary: paper lem:ld-soundness prints the common deltaLd form |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left` — `G/DistanceTheorems/RoundingTransport.lean:138` | \(\lambda+\sqrt{220}\lambda^{1/8}+2\sqrt{\lambda+z}\) | Calculated \(660\lambda^{1/4}+9\lambda+3z\), with the same rounding chosen before postprocessing | deferred #735 |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_right` — same file `:256` | Same bound, opposite orientation | Same calculated stronger transport | deferred #735 |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency` — same file `:310` | Both preceding bounds for one pair | Same paired-witness stronger transport | deferred #735 |
| Proposed `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_at_native_error` — anchor `C/ExtendedLineGame/RoundedPolynomialEstimates.lean:273` | PROPOSED, UNPROVED: current input is inflated before rounding | Both orderings at \(J=4\eta(\Lambda_M(T))+8Q\) | sharp |
| Proposed `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_scalar_mass_at_native_error` — anchor `C/ExtendedLineGame/ScalarNonlinearMass.lean:207` | PROPOSED, UNPROVED: missing sibling | \(2J+2(Md+1)/q\), with the same rounded measurements | sharp |
| Proposed `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_wrong_variable_mass_at_native_error` — anchor `C/ExtendedLineGame/WrongVariableMass.lean:237` | PROPOSED, UNPROVED: missing sibling | \(2J+2(2n+2)/q\), in both orderings | sharp |
| Proposed `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_at_native_error` — anchor same file `:416` | PROPOSED, UNPROVED: missing sibling | \(6J+(12n+4d+10)/q\) | sharp |
| Proposed `MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_at_native_error` — anchor `C/ExtendedLineGame/PairPointConsistency.lean:283` | PROPOSED, UNPROVED: missing sibling | \(8J+(12n+4d+14)/q\), for all four point comparisons | sharp |
| Proposed `MIPStarRE.QPBT.exists_quantitative_global_pair_witness_mixed` — anchor `C/Quantitative.lean:28` | PROPOSED, UNPROVED: missing explicit-error sibling | \(g=G(\Lambda_M(T),Q)\), with actual complete projective measurements | sharp |
| `MIPStarRE.QPBT.pullingMeas_eval_consistencyDefect_le` — `E/PullingDefect.lean:136` | \(12g+688e\) | Same separate linear terms | sharp |
| `MIPStarRE.QPBT.tildeObs_opDistSq_le_pulling_eval_add` — `E/PullingMeasurement.lean:201` | Four times evaluated defect plus \(4r\) | \(Y=48g+2752e+4r\) after substitution | sharp |
| `MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_explicit` — `E/ObservableConsistency.lean:82` | \(x=2800(g+\sqrt e+r)\) | \(Y\); missing exported state-specific interface | deferred #727 |
| `MIPStarRE.QPBT.extracted_obs_self_consistent_of_global_pair_witness_explicit` — `E/SwappedConsistency.lean:104` | \(x\) | Exact transport of the preceding observable bound | deferred #727 |
| `MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit` — `E/NonencodingSupport.lean:175` | \(g+(1+2\sqrt{172})\sqrt e\) | Same separate witness and game-error terms | sharp |
| `MIPStarRE.QPBT.tilde_m_consistent_point_meas_of_global_pair_witness_explicit` — `E/SuppliedPointConsistency.lean:107` | \((2+2\sqrt{172})(g+\sqrt e+r)\) | \(2g+(1+2\sqrt{172})\sqrt e+r\); coefficient-only differences | sharp |
| `MIPStarRE.QPBT.tilde_m_consistent_point_meas'_of_global_pair_witness_explicit` — same file `:247` | Same bound, opposite orientation | Same term orders | sharp |
| `MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit` — `E/EvaluatedPauliConsistency.lean:64` | \((2+4\sqrt{172})(g+\sqrt e+r)\) | Same three orders; smaller termwise coefficients before absorption | sharp |
| `MIPStarRE.QPBT.Extraction.norm_sub_eprProjection_le_of_pauli_dist` — `E/ProjectionFromDistance.lean:84` | Projection norm error \(2\sqrt z\) | Same root order | sharp |
| `MIPStarRE.QPBT.ProjectiveSetting.exists_unit_aux_near_eprProjection` — `E/EPRState.lean:148` | Twice the projection norm error | Same order, including zero projection | sharp |
| `MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit` — `E/StateExtraction.lean:109` | \(s^2\le16x\) | \(16Y\), after exposing the inherited state-specific interface | deferred #727 |
| `MIPStarRE.QPBT.ProjectiveSetting.extraction_pauli_dist_le` — `E/ConcretePauliComparison.lean:126` | \(D_{\rm swap}\le2z+2r+4s\) | Separate evaluated-defect, collision, and state-norm terms | sharp |
| `MIPStarRE.QPBT.exists_extraction_witness_with_component_bounds` — `T/Soundness/ComponentBounds.lean:38` | \(s^2\le16x\), \(D_{\rm swap}\le2x+2r+16\sqrt x\) | Same separate conclusions; the \(18(x+\sqrt x+r)\) record scale is not used for their propagation | sharp |
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_alice_le_components` — `T/Soundness/OperatorTransfer.lean:138` | \(D_{\rm iso}\le2D_{\rm swap}+2s^2\) | Same separate terms | sharp |
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_bob_le_components` — same file `:182` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.pauli_naimark_operator_distanceA_le` — `T/Soundness/NaimarkOperatorTransfer.lean:409` | \(D_{\rm Naimark}\le3D_{\rm iso}+6s^2\) | Same separate terms | sharp |
| `MIPStarRE.QPBT.pauli_naimark_operator_distanceB_le` — same file `:474` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distanceA_le_completed` — `T/Soundness/RawOperatorTransferCore.lean:570` | \(D_{\rm raw}\le2D_{\rm completed}+4s^2+344e\) | Same terms; no answer averaging | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distanceB_le_completed` — same file `:676` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.exists_pauli_soundness_witness_with_component_bounds` — `T/Soundness/ComponentBounds.lean:160` | \(s^2\le16x\); both raw errors \(\le472x+24r+192\sqrt x+344e\) | Same witness and separate orders | sharp |
| `MIPStarRE.QPBT.pauli_soundness_state_distance_le_two` — `T/Soundness/RawOperatorTransferCore.lean:392` | \(s\le2\) | Universal norm cap | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_a_le_four` — same file `:405` | \(D_A\le4\) | Universal raw-family cap | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_b_le_four` — same file `:423` | \(D_B\le4\) | Universal raw-family cap | sharp |
| Proposed `MIPStarRE.QPBT.sqrt_quantitative_extraction_scale_le_degree_two` — anchor `T/Soundness/QuantitativeScalars.lean:262` | PROPOSED, UNPROVED: current result pads \(n^2\) to \(n^4\) | \(\sqrt x\le10^6n^2E_b\) | sharp |
| Proposed `MIPStarRE.QPBT.pauli_soundness_quantitative_mixed` — anchor `T/QuantitativeSoundness.lean:42` | PROPOSED, UNPROVED: missing full-domain mixed headline | \(s^2\le\min(4,16X)\); raw errors \(\le\min(4,472X+24r+192\sqrt X+344e)\) | sharp |
| Proposed `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two` — anchor same file `:42` | PROPOSED, UNPROVED: current common bound is \(C=\min(4,10^{14}n^4E_b)\) | \(I=\min(4,10^9n^2E_b)\), using a reconstructed witness on the enlarged small branch | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_canonical` — `T/QuantitativeSoundness.lean:152` | \(\Delta_{100,b}\) | Current proof weakens \(C\); proposed integration derives the same paper-shaped form from \(I\) | necessary: thm:pauli prints one common a(md)^a robustness function |
| `MIPStarRE.QPBT.qubit_state_error_to_qubit` — `T/QubitForm.lean:356` | Equality of state norms | Equality | sharp |
| `MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit` — same file `:376` | Equality with Alice's raw distance | Equality | sharp |
| `MIPStarRE.QPBT.qubit_operator_distance_b_to_qubit` — same file `:395` | Equality with Bob's raw distance | Equality | sharp |
| Proposed `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_mixed` — anchor `T/QuantitativeQubitForm.lean:29` | PROPOSED, UNPROVED: missing sibling | Exact qubit transport of the mixed headline | sharp |
| Proposed `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_degree_two` — anchor same file `:29` | PROPOSED, UNPROVED: missing sibling | \(I\), with all three metrics exactly preserved | sharp |
| `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_canonical` — `T/QuantitativeQubitForm.lean:50` | \(\Delta_{100,b}\) | Exact transport of the canonical field-coordinate result, proposed to derive from \(I\) | necessary: cor:pauli-binary prints the common robustness function |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit` — `C/DirectLowDegree/Soundness.lean:245` | \(\delta_{\rm LD}(a_L,\beta)\) | Historical fixed-witness baseline; the stronger native-error route is recorded separately | necessary: retain the paper-form low-degree baseline alongside its sharper sibling |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_explicit` — `C/DirectLowDegree/AnyStrategySoundness.lean:114` | Same historical error | Exact compression preserves that error | necessary: retain the paper-form low-degree baseline alongside its sharper sibling |
| `MIPStarRE.QPBT.pauli_baseline_actual_rounded_global_pair_error_bound` — `C/ActualErrorBounds.lean:158` | \(\Delta_{a_G,1/327680000}\) | Historical actual rounded expression \(G\), before canonical absorption | necessary: lem:qld-4-7 prints a common a(md)^a polynomial error |
| `MIPStarRE.QPBT.exists_global_pair_witness_explicit` — `C/Apply.lean:308` | \(\Delta_{a_G,1/327680000}\) | Historical witness construction at that baseline | necessary: retain the fixed-witness paper-form baseline |
| `MIPStarRE.QPBT.projective_setting_isometry_bounds_explicit_baseline` — `T/Soundness/ProjectiveSetting.lean:36` | \(\Delta_{a_P,b_0}\) | Historical common envelope; separate components are exposed above | necessary: retain the fixed-witness thm:pauli comparison baseline |
| `MIPStarRE.QPBT.arbitrary_strategy_isometry_bounds_explicit_baseline` — `T/Soundness/NaimarkAssembly.lean:42` | \(\Delta_{21a_P^2,b_0}\) | Historical common envelope; exact state and separate operator transfer are available | necessary: retain the fixed-witness thm:pauli comparison baseline |
| `MIPStarRE.QPBT.arbitrary_strategy_raw_isometry_bounds_explicit_baseline` — `T/Soundness/RawOperatorTransfer.lean:95` | \(\Delta_{a_0,b_0}\) | Historical raw-answer baseline | necessary: retain the fixed-witness thm:pauli comparison baseline |
| `MIPStarRE.QPBT.pauli_soundness_explicit_baseline` — `T/Soundness.lean:51` | Explicit \((a_0,b_0)\) | Same historical bound; no opaque existential specialization | necessary: preserve the historical explicit sibling of thm:pauli |
| `MIPStarRE.QPBT.pauli_soundness` — `T/Soundness.lean:110` | Existential \(a,b\) | Explicit baseline \((a_0,b_0)\), with proposed improved siblings above | necessary: retain the printed thm:pauli statement |
| `MIPStarRE.QPBT.pauli_soundness_qubit_explicit_baseline` — `T/QubitForm.lean:421` | Explicit \((a_0,b_0)\) | Exact transport of the historical baseline | necessary: preserve the historical explicit sibling of cor:pauli-binary |
| `MIPStarRE.QPBT.pauli_soundness_qubit` — same file `:461` | Existential \(a,b\) | Same explicit historical constants, with a proposed improved sibling above | necessary: retain the printed cor:pauli-binary statement |
| `MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_combinedError` — `C/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean:63` | Mixed defects \(\le F+(m+k)d/q\); polynomial defect \(\le F\) | Separate errors, with \(F=\mathrm{mainFormalError}\) at dimension \(m+k\) and passing error \(30\varepsilon\) | sharp |
| `MIPStarRE.QPBT.exists_directCombinedTransportConstants` — `C/DirectLowDegree/Transport/Combining/Error.lean:232` | Existential constants; proof selects \(10^{23},1/80000\) | Raw \(F+(m+k)d/q\), retaining the \(1/40000\) power and its tail; explicit mixed transport interface missing | deferred #727 |
| `MIPStarRE.QPBT.exists_direct_ld_soundness` — `C/DirectLowDegree/Soundness.lean:66` | Existential deltaLd bound | Fixed proof witnesses \(10^{23},1/80000\); public fixed-constant sibling missing | deferred #727 |
| `MIPStarRE.QPBT.ldPointPair_consistencyDefect_le` — `C/DirectLowDegree/Transport/PointAgreement.lean:323` | \(9\varepsilon\) | Same linear game-error order | sharp |
| `MIPStarRE.QPBT.polyTupleAgreement_avg_le_mdq` — `T/LowDegreeGameTheorems.lean:34` | \(md/q\) | Same collision bound, independent of tuple length | sharp |
| `MIPStarRE.QPBT.exists_ld_soundness` — `T/LowDegreeGameTheorems.lean:82` | Existential constants; proof composes witnesses \(10^{24},1/160000\) | First two errors retain \(E\); third retains \(E+2\sqrt{9\varepsilon+E}+md/q\); explicit headline sibling and separated interface missing | deferred #727 |
| `MIPStarRE.QPBT.honestMeasurement_rejected_mul` — `T/Completeness.lean:231` | Every rejected product is zero | Exact zero | sharp |
| `MIPStarRE.QPBT.exists_spcc_value_one` — `T/Completeness.lean:267` | Value exactly one, with an SPCC witness | Exact perfect completeness | sharp |

## Pending proof gates

Before this ledger can serve as final mathematical evidence, PR #736 must
provide and axiom-audit the proposed native-error, mixed, degree-two, and qubit
siblings; the report must replace every proposed locator with the merged
declaration and exact source location; and the final quantitative survey must
recheck the table against the merged proof. The explicit sibling for
`exists_ld_soundness` remains separate backlog under #727 even after the
bounded two-improvement task closes.
