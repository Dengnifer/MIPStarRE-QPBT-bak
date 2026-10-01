# QPBT bound ledger

> **Authored ledger status, October 1, 2026.** This ledger is reconciled against
> final PR #736 source head `6ea9f96bd86aaaad613130dea49eefdf6e80c5a9`,
> merged normally as `0b847308c30769be983bbd05c297e1014db76590`.
> It contains 152 stage rows, including every one of the 57 PR #736 bound-strength
> rows. The ledger and companion report await their own normal CI, `review.sh`,
> and separate independent mathematical review; this status does not claim those
> document gates have completed.

> **Proof-source status.** The native-LDT transport, exact global-pair error,
> separated six-term and fractional scalar certificates, mixed component bounds,
> fractional field and qubit headlines, degree-two and degree-four compatibility
> results, canonical corollaries, and fixed baselines named below are all present
> at the final source head. The static C8 `DELEGATED` result checks table syntax
> only; it does not certify mathematical coverage, proof closure, or completion of
> the QPBT track.

This ledger covers stage estimates on the registered headline paths to
`MIPStarRE.QPBT.pauli_soundness`, `MIPStarRE.QPBT.pauli_soundness_qubit`,
`MIPStarRE.QPBT.exists_ld_soundness`, and
`MIPStarRE.QPBT.exists_spcc_value_one`, together with the explicit quantitative
siblings and compatibility paths used by the final report. Source locators are
paths and line numbers at final head `6ea9f96b`; the fully qualified declaration
name is authoritative if later edits move a line.

Write

\[
 e=\min(\varepsilon,1),\qquad n=md,\qquad r=n/q,\qquad
 h=2m+2,\qquad \tau=1/8192,\qquad b=1/67108864,
\]

and let \(E_a=e^a+q^{-a}+2^{-an}\). For the native direct-LDT input, set

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

For the native route, put

\[
 T=3\left(\sqrt{Q+L_{\rm ext}}+r\right),\qquad
 \lambda=\Lambda_h(T),\qquad J=4\eta(\lambda)+8Q,
\]

\[
 G=G(\lambda,Q),\qquad
 X_{\rm native}=2800\left(G+\sqrt e+r\right).
\]

The earlier extraction identity is denoted separately by

\[
 Y_{\rm old}=48g+2752e+4r.
\]

For the fractional terminal estimate, set

\[
 M=m^{20481/262144}d^{1/64},\qquad K=M^2,
\]

so that the merged proof gives

\[
 G\le277248K E_{2b},\qquad
 H=\min\{4,10769120ME_b\}.
\]

The construction theorem giving the exact witness at \(G\) assumes only
\(e\ge0\). The root certificates use \(0\le e\le1\), and the extraction
certificate \(\sqrt{X_{\rm native}}\le16218ME_b\) additionally uses
\(r\le1\). The degree-four consequence
\(G\le10^7n^4E_{2b}\) follows from the fractional estimate without the
coefficient-30 `deltaLd` route. The separately derived coefficient 14596 is an
unimplemented coefficient-only refinement, not the proved coefficient.

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

Let \(Q=Q_0e^{1/8}\),
\(L=L_0(e^{1/64}+r^{1/4})\),
\(L_{\rm ext}=mH_0(e^{1/256}+r^{1/16})\), and
\(H_p(a,z)=115(a^{1/4}+z^{1/8})\). The exact native construction and the
separated certificates remain distinct from these historical common envelopes.

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
slack is described in `docs/error-bounds.md`.

## Explicit headline status

The final source contains explicit fixed-constant siblings for
`pauli_soundness` and `pauli_soundness_qubit`, the native mixed and fractional
siblings in field and exact-qubit coordinates, the degree-two and degree-four
compatibility results, and exact perfect completeness for
`exists_spcc_value_one`. One witness in the fractional theorem controls the
unsquared state norm and both raw summed-squared prescribed-answer operator
errors at \(H\); the mixed theorem separately retains the squared state bound
\(\min(4,16X_{\rm native})\) and the two raw bounds
\(\min(4,472X_{\rm native}+24r+192\sqrt{X_{\rm native}}+344e)\).

The general seed-indexed theorem `exists_ld_soundness` still lacks its public
explicit sibling. Source inspection finds witnesses \((10^{24},1/160000)\),
with its first two errors retained at \(E\) and its third at
\(E+2\sqrt{9\varepsilon+E}+md/q\). That missing sibling and its separated
interface remain tracked in #727 and prevent a whole-track C8 completion claim.
The committed QPBT axiom audit has 53 commands; the quantitative declarations
used here close only over `propext`, `Classical.choice`, and `Quot.sound`.

## Stage ledger

| Stage lemma | Stated bound | Bound the argument supports | Disposition |
|---|---|---|---|
| `MIPStarRE.QPBT.WinImplications.win_comm_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean:136` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_cons_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean:347` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:110` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_comm_cons_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:293` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_ms_cons_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean:176` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_magic_square_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean:484` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_ms_cons_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean:511` | \(1376e\) | \(1376e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_low_degree_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:616` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_low_degree_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean:245` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean:782` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean:437` | \(86e\) | \(86e\) | sharp |
| `MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean:265` | \(16\delta\) | Same squared-distance order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean:450` | \(1024(c_1+\sqrt{c_2+c_3})\) | Calculated \(1536(c_1+c_2+c_3)\), after the missing complete-measurement adapter | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/TwistedCommutation.lean:278` | \(c(e+\sqrt e)\) | Calculated \(792576e\) | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:180` | \(c(e+\sqrt e)\) | Same calculated linear bound, opposite orientation | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/AnticommutingObs.lean:729` | \(4886363136e\) | Same linear error order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_bob_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:279` | \(4886363136e\) | Same linear error order | sharp |
| `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/TwistedCommutation.lean:351` | \((2c+4886363136+4)\sqrt e\) | Calculated linear commutation plus the existing linear anticommutation contribution | deferred #735 |
| `MIPStarRE.QPBT.WinImplications.point_obs_twisted_commutation_interchanged_explicit` — `MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean:379` | Same square-root bound | Same calculated linear improvement | deferred #735 |
| `MIPStarRE.QPBT.twisted_commutator_avg_le_explicit` — `MIPStarRE/QPBT/Observables/ExpandedCommutation.lean:188` | \(t_0\sqrt e\) | Calculated \(9774311424e\) | deferred #735 |
| `MIPStarRE.QPBT.exp_point_self_cons_explicit` — `MIPStarRE/QPBT/Observables/PointConsistency.lean:716` | \(172e\) | \(172e\) | sharp |
| `MIPStarRE.QPBT.exp_line_point_cons_explicit'` — `MIPStarRE/QPBT/Observables/LineMeasurement.lean:315` | \(348\sqrt e\) | Existing proof first obtains \(172e\), independently capped by four; missing exported linear sibling | deferred #727 |
| `MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit` — `MIPStarRE/QPBT/Combining/Points/Commutation.lean:363` | \(t_0\sqrt e\) | Linear bound after the #735 commutation adapter | deferred #735 |
| `MIPStarRE.QPBT.ProjectiveSetting.sandwich_point_ordered_dist_le_explicit` — `MIPStarRE/QPBT/Combining/Points/Sandwich.lean:148` | \(t_0\sqrt e\) | Same commutator input; linear after #735 | deferred #735 |
| `MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit` — `MIPStarRE/QPBT/Combining/Points/Sandwich.lean:194` | \(688e\) | Linear in \(e\) | sharp |
| `MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit` — `MIPStarRE/QPBT/Combining/Points/Consistency.lean:370` | \((344+3t_0)(e+\sqrt e)\) | Linear defect after the stronger commutator construction | deferred #735 |
| `MIPStarRE.QPBT.exists_combined_points_witness_explicit` — `MIPStarRE/QPBT/Combining/Points.lean:67` | \(Q_0e^{1/8}\) | Calculated actual-witness target \(10^{15}e^{1/4}\) | deferred #735 |
| `MIPStarRE.QPBT.exp_line_point_same_placement_distance_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:205` | \(1040(e+\sqrt e)\) | Linear bound after exposing the existing linear expanded-line comparison | deferred #727 |
| `MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:257` | \(8Q+2080(e+\sqrt e)\) | Same bound with its terms retained | sharp |
| `MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/PointComparison.lean:377` | \(8Q+2080(e+\sqrt e)\) | Same orders; sharper incoming line estimate is a separate backlog item | sharp |
| `MIPStarRE.QPBT.combined_points_conditioned_line_marginal_defect_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/Conditioning.lean:66` | \((8Q+2080(e+\sqrt e))/\rho\) | Same conditional-probability scaling | sharp |
| `MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:450` | \(16\delta\) | Linear squared-distance bound | sharp |
| `MIPStarRE.QPBT.op_dist_sq_commutator_right_le_explicit` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:674` | \(16\delta\) | Same bound on the other tensor factor | sharp |
| `MIPStarRE.QPBT.coarse_commutator_bound_explicit` — `MIPStarRE/QPBT/Games/Sandwich/Pasting/CodewordConsistency.lean:89` | \(32\delta\) | Linear squared-distance bound | sharp |
| `MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit` — `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:131` | \(H_p(\eta,\delta)\) | At the actual projective consumer, calculated \(307\delta+16\eta\); missing projective refinement | deferred #735 |
| `MIPStarRE.QPBT.pasting_error_heterogeneous_explicit` — `MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean:271` | \(H_p(\eta,\delta)\) | Same projective refinement; heterogeneous transport is exact | deferred #735 |
| `MIPStarRE.QPBT.combined_line_conditioned_defect_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/Construction.lean:200` | \(H_p(r,(8Q+2080(e+\sqrt e))/\rho)\) | Apply the missing projective refinement to these actual measurements | deferred #735 |
| `MIPStarRE.QPBT.combined_line_restored_defect_le_explicit` — `MIPStarRE/QPBT/Combining/Lines/Construction.lean:315` | \(\rho H_p(\cdots)+1/(2q)\) | Calculated \(2456Q+638560(e+\sqrt e)+17r\) | deferred #735 |
| `MIPStarRE.QPBT.combined_line_measurement_consistency_explicit` — `MIPStarRE/QPBT/Combining/Lines/Construction.lean:517` | \(L\) | Retained capped restored expression; stronger projective route requires #735 | deferred #735 |
| `MIPStarRE.QPBT.exists_combined_lines_witness_of_points_witness_explicit` — `MIPStarRE/QPBT/Combining/Lines.lean:119` | \(L\) | Same constructed measurements at the sharper restored error | deferred #735 |
| `MIPStarRE.QPBT.subline_remove_x_factor_at_explicit` — `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:32` | \(2\sqrt m(\delta_P^{1/4}+\delta_Q^{1/4})\) | Retain the underlying mixed root; export the term-specific dimension dependence | deferred #727 |
| `MIPStarRE.QPBT.subline_z_term_near_one_at_explicit` — `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:193` | \(2\sqrt m(\delta_P^{1/4}+\delta_Q^{1/4}+e^{1/4})\) | Retain term-specific dimension factors before common-envelope absorption | deferred #727 |
| `MIPStarRE.QPBT.subline_joint_overlap_near_one_at_explicit` — `MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean:311` | \(6[\sqrt Q+\sqrt m(\delta_P^{1/4}+Q^{1/4}+e^{1/4})]\) | This explicit mixed expression is stronger than the later \(mH_0\) envelope | sharp |
| `MIPStarRE.QPBT.exists_extended_lines_witness_established_of_points_witness_explicit` — `MIPStarRE/QPBT/Combining/Apply.lean:218` | \(L_{\rm ext}\) | Unit-capped mixed overlap expression from the previous row; missing witness interface retaining it | deferred #727 |
| `MIPStarRE.QPBT.ExtendedLineGame.strategy_value_ge_directPassingErrorEnvelope` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/PassingValue.lean:89` | \(T=3(\sqrt{Q+L_{\rm ext}}+r)\) | Existing seven-branch expression retains separate terms; calculated linear replacement \((7Q+20L_{\rm ext}+5r)/9\) needs #735 | deferred #735 |
| `MIPStarRE.LDT.Test.mainFormal` — `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300` | \(100000N^2h^4[(3t)^{1/40000}+(d/q)^{1/40000}+\exp(-N/(2560000h^2))]\) | Frozen sharper linear-triangle sibling below | necessary: retain the printed LDT thm:main-formal statement |
| `MIPStarRE.LDT.Test.main_formal_linear_triangle` — `MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean:147` | \(10000N^{1/4}h^{1/2}[(3t)^\tau+(d/q)^\tau+\exp(-N/(640000h^2))]\), capped by one | At \(N=2560000h^3d\), exactly \(\Lambda_h(t)\) | sharp |
| `MIPStarRE.QPBT.sqrt_rpow_eq` — `MIPStarRE/QPBT/Combining/QuantitativeScalarBase.lean:27` | `sqrt(x^a) = x^(a/2)` for `x >= 0` | Exact real-power identity shared by the native scalar proofs | sharp |
| `MIPStarRE.QPBT.direct_ld_aux_parameter_linear_triangle_exp_arg` — `MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean:105` | `N/(640000 h^2) = 4hd` for `N = 2560000 h^3 d` | Exact exponential argument, hence tail `exp(-4hd)` | sharp |
| `MIPStarRE.QPBT.direct_ld_aux_parameter_quarter_eq` — `MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean:117` | `N^(1/4) = 40 h^(3/4) d^(1/4)` | Exact fourth root; no padding to `40hd` | sharp |
| `MIPStarRE.QPBT.main_formal_linear_triangle_error_eq_direct_native_error` — `MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean:372` | The imported capped linear-triangle error equals `Lambda_h(t)` | Exact specialization of the frozen LDT theorem | sharp |
| `MIPStarRE.QPBT.direct_native_error_le_delta_ld_quantitative` — `MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean:589` | `Lambda_h(t) <= deltaLd 30 tau t q h d 1` | The exact native error is stronger; this is the source-form weakening | necessary: paper `lem:ld-soundness` prints the common `deltaLd` form |
| `MIPStarRE.QPBT.direct_coordinate_main_formal_at_native_error` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Simultaneous.lean:163` | All three coordinate relations hold at `Lambda_h(t)` for one projective measurement pair | Same relations and measurements, with no transport loss | sharp |
| `MIPStarRE.QPBT.exists_direct_simultaneous_polynomial_measurements_at_native_error_of_k_eq_one` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Simultaneous.lean:418` | All three singleton-tuple relations hold at `Lambda_h(t)` | Singleton relabeling preserves measurements and bounds exactly | sharp |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_at_native_error` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:334` | Projective one-coordinate soundness at `Lambda_h(t)` | Exactly `Lambda_h(t)` for all three defects | sharp |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_at_native_error` — `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:363` | Arbitrary-strategy one-coordinate soundness at `Lambda_h(t)` | Exact Naimark compression preserves all three defects | sharp |
| `MIPStarRE.QPBT.native_rounding_error_eq` — `MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean:298` | The rounding expression equals `eta(lambda)` | Exact separation into `lambda`, `lambda^(1/8)`, and `lambda^(1/2)` | sharp |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_at_native_error` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean:315` | Both orderings hold at `J` | One rounded pair satisfies both orderings at the same `J` | sharp |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_scalar_mass_at_native_error` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/ScalarNonlinearMass.lean:206` | At most `2J + 2(hd+1)/q` on both sides | Same rounded measurements retain the ordered and scalar-mass estimates | sharp |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_wrong_variable_mass_at_native_error` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean:236` | At most `2J + 2(2n+2)/q` in both orderings and on both sides | Same rounded measurements retain all preceding estimates | sharp |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_at_native_error` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean:453` | At most `6J + (12n+4d+10)/q` on both sides | Same rounded measurements concentrate on the separated image | sharp |
| `MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_at_native_error` — `MIPStarRE/QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean:283` | Each of four point comparisons is at most `8J + (12n+4d+14)/q` | Exact arithmetic for the constructed projective pair | sharp |
| `MIPStarRE.QPBT.quantitative_native_global_pair_error_bound` — `MIPStarRE/QPBT/Combining/QuantitativeScalars.lean:773` | G <= 10^7 n^4 E_(2b) | G <= 277248 K E_(2b); the preserved corollary follows without deltaLd 30 | deferred #727 |
| `MIPStarRE.QPBT.exists_quantitative_global_pair_witness_at_native_error` — `MIPStarRE/QPBT/Combining/Quantitative.lean:87` | One witness has g = G and g <= 10^7 n^4 E_(2b) | The exact same witness is constructed independently of the coarse comparison; its additional compatibility inequality follows from the fractional G bound | deferred #727 |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeMixedScale` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:51` | `X_native = 2800(G + sqrt(e) + r)` | Exact extraction scale at the native global-pair error | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_mixed_components` — `MIPStarRE/QPBT/Test/QuantitativeSoundness.lean:40` | State squared is at most `min(4,16 X_native)`; both raw errors are at most `min(4,472 X_native + 24r + 192 sqrt(X_native) + 344e)` | One witness retains the exact native `G` and all three component orders | sharp |
| `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_mixed_components` — `MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean:29` | Exact qubit transport of the native mixed bounds | All three metrics are preserved by equality | sharp |
| `MIPStarRE.QPBT.sqrt_quantitative_extraction_scale_le_degree_two` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:294` | From `x <= 10^11 n^4 E_(2b)`, `sqrt(x) <= 10^6 n^2 E_b` | Degree two is retained; `sqrt(10^11) <= 10^6` is coefficient-only slack | sharp |
| `MIPStarRE.QPBT.quantitative_state_component_lt_degree_two_raw_error` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:468` | `4 sqrt(x) < 10^9 n^2 E_b` | First gives `4 sqrt(x) <= 4*10^6 n^2 E_b` | sharp |
| `MIPStarRE.QPBT.quantitative_operator_component_lt_degree_two_raw_error` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:497` | Mixed raw component is below `10^9 n^2 E_b` on the nonsaturated branch | First gives `664000368 n^2 E_b` | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two` — `MIPStarRE/QPBT/Test/QuantitativeSoundness.lean:368` | One witness has unsquared state and both raw errors at most I | The same witness satisfies H; I is a preserved internal form | deferred #727 |
| `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_degree_two` — `MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean:87` | Exact qubit transport of I | The same exact transport satisfies H | deferred #727 |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two_error_le_quantitative_error` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean:167` | `I <= C` | Exact capped comparison | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two_error_lt_quantitative_error_iff` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean:201` | `I < C` iff the uncapped degree-two error is below four | Exact strictness criterion | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two_error_le_deltaQld` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean:259` | `I <= deltaQld 100 b epsilon m d q` | Exact comparison used by the canonical corollary | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_canonical` — `MIPStarRE/QPBT/Test/QuantitativeSoundness.lean:412` | Common `deltaQld 100 b` state/operator bound | Proved weakening of `I` | necessary: paper `thm:pauli` prints the common `a(md)^a` robustness form |
| `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_canonical` — `MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean:130` | Exact qubit form of the canonical bound | Exact transport of the field-coordinate canonical witness | necessary: paper `cor:pauli-binary` prints the common robustness form |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_power_eq_gain_mul_baseline` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:89` | `b = (625/8) b_0` | Exact exponent gain `78.125` | sharp |
| `MIPStarRE.QPBT.pauli_soundness_explicit_baseline` — `MIPStarRE/QPBT/Test/Soundness.lean:51` | Fixed field baseline `(a_0,b_0)` | Exact constants traced from the proof | sharp |
| `MIPStarRE.QPBT.pauli_soundness_qubit_explicit_baseline` — `MIPStarRE/QPBT/Test/QubitForm.lean:421` | Exact qubit transport of the fixed baseline | All three metrics are preserved by equality | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_degree_two_error_lt_explicit_baseline_clipped` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean:372` | `I` is strictly below the clipped explicit baseline | Exact before/after comparison | sharp |
| `MIPStarRE.QPBT.quantitativeNativeSeparatedRaw` — `MIPStarRE/QPBT/Combining/QuantitativeNativeScalars/Core.lean:25` | U_s with six separate contributions | The separated native scalar expression | sharp |
| `MIPStarRE.QPBT.quantitativeNativeSeparatedError` — `MIPStarRE/QPBT/Combining/QuantitativeNativeScalars/Core.lean:44` | L_s = min(1,U_s) | The capped separated native scalar expression | sharp |
| `MIPStarRE.QPBT.quantitative_native_error_rpow_le_separated` — `MIPStarRE/QPBT/Combining/QuantitativeNativeScalars/Core.lean:357` | lambda^s <= L_s for 0 <= s <= 1 | Six native contributions with distinct error and dimension powers | sharp |
| `MIPStarRE.QPBT.exists_quantitative_global_pair_witness_native` — `MIPStarRE/QPBT/Combining/Quantitative.lean:27` | A witness with error exactly G | The exact native witness; no coarse global-pair comparison is needed | sharp |
| `MIPStarRE.QPBT.quantitativeNativeGlobalPairSeparatedError` — `MIPStarRE/QPBT/Combining/QuantitativeNativeGlobalPairScalars.lean:23` | B_G = min(1,32 L_1 + 32 sqrt(220) L_(1/8) + 64 sqrt(2) L_(1/2) + 64Q + c) | Separate native powers, point error and collision term | sharp |
| `MIPStarRE.QPBT.quantitative_native_global_pair_error_le_separated` — `MIPStarRE/QPBT/Combining/QuantitativeNativeGlobalPairScalars.lean:34` | G <= B_G | Separate native powers, point error and collision term | sharp |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeSeparatedScale` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/NativeSeparated.lean:25` | Y_sep = 2800(B_G + sqrt(e) + r) | Separated extraction scale | sharp |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeSeparatedRoot` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/NativeSeparated.lean:32` | Z_sep, the termwise square-root certificate | Separate L_(1/2), L_(1/16), L_(1/4), point, collision, error and ratio contributions | sharp |
| `MIPStarRE.QPBT.quantitative_native_extraction_scale_bounds` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/NativeSeparated.lean:48` | X_native <= Y_sep and sqrt(X_native) <= Z_sep | Both estimates are retained separately | sharp |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeFractionalDimension` — `MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean:44` | M = m^(20481/262144) d^(1/64) | Fractional dimension powers before the compatibility corollaries | sharp |
| `MIPStarRE.QPBT.quantitative_native_error_one_sixteenth_le_fractional_base` — `MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean:162` | lambda^(1/16) <= 12 M E_b | Terminal scalar certificate from the separate native terms | sharp |
| `MIPStarRE.QPBT.quantitative_native_global_pair_sqrt_le_fractional_base` — `MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean:580` | sqrt(G) <= 304 M E_b | Terminal rounding, point and collision certificates | sharp |
| `MIPStarRE.QPBT.quantitative_native_extraction_sqrt_le_fractional_base` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Fractional.lean:40` | sqrt(X_native) <= 16218 M E_b when r <= 1 | Terminal certificate from sqrt(2800) <= 53 and the separate scale terms | sharp |
| `MIPStarRE.QPBT.quantitative_native_global_pair_error_le_fractional` — `MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean:860` | G <= 277248 K E_(2b) for 0 <= e <= 1, with no ratio assumption | Square the checked root certificate and use E_b^2 <= 3 E_(2b), doubling all three exponents | sharp |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeFractionalRawError` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Fractional.lean:26` | 10769120 M E_b | Terminal common error; the exact mixed component estimates remain separately available | sharp |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeFractionalError` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Fractional.lean:33` | H = min(4,10769120 M E_b), e = min(epsilon,1) | Universal cap and source clipping of the terminal error | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_fractional` — `MIPStarRE/QPBT/Test/QuantitativeSoundness.lean:178` | One witness has unsquared state and both raw errors at most H | The witness retains the mixed estimates; the terminal common raw coefficient is 664*16218+368 = 10769120 | sharp |
| `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_fractional` — `MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean:63` | Exact qubit transport of H | All three metrics are preserved by equality | sharp |
| `MIPStarRE.QPBT.pauli_soundness_quantitative_fractional_error_le_degree_two` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean:23` | H <= I | H retains fractional dimensions; I is the preserved internal comparison target | deferred #727 |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeDegreeTwoRawError` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:35` | 10^9 n^2 E_b | 10769120 M E_b | deferred #727 |
| `MIPStarRE.QPBT.pauliSoundnessQuantitativeDegreeTwoError` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:44` | I = min(4,10^9 n^2 E_b) | H | deferred #727 |
| `MIPStarRE.QPBT.pauli_soundness_quantitative` — `MIPStarRE/QPBT/Test/QuantitativeSoundness.lean:390` | One witness has common bound C | The same witness satisfies H through I | deferred #727 |
| `MIPStarRE.QPBT.sqrt_quantitative_extraction_scale_le` — `MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean:342` | Historical degree-four square-root envelope | The preserved degree-two square-root sibling | deferred #727 |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_quantitative` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:370` | \(\delta_{\rm LD}(30,\tau)\) | Weakening of the proved native-error result | necessary: paper lem:ld-soundness prints the common deltaLd form |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_quantitative` — `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:405` | Same common deltaLd form | Same weakening after exact Naimark compression | necessary: paper lem:ld-soundness prints the common deltaLd form |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left` — `MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean:138` | \(\lambda+\sqrt{220}\lambda^{1/8}+2\sqrt{\lambda+z}\) | Calculated \(660\lambda^{1/4}+9\lambda+3z\), with the same rounding chosen before postprocessing | deferred #735 |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_right` — `MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean:256` | Same bound, opposite orientation | Same calculated stronger transport | deferred #735 |
| `MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency` — `MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean:310` | Both preceding bounds for one pair | Same paired-witness stronger transport | deferred #735 |
| `MIPStarRE.QPBT.pullingMeas_eval_consistencyDefect_le` — `MIPStarRE/QPBT/Extraction/PullingDefect.lean:136` | \(12g+688e\) | Same separate linear terms | sharp |
| `MIPStarRE.QPBT.tildeObs_opDistSq_le_pulling_eval_add` — `MIPStarRE/QPBT/Extraction/PullingMeasurement.lean:201` | Four times evaluated defect plus \(4r\) | \(Y=48g+2752e+4r\) after substitution | sharp |
| `MIPStarRE.QPBT.tilde_obs_self_consistent_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/ObservableConsistency.lean:82` | \(x=2800(g+\sqrt e+r)\) | \(Y\); missing exported state-specific interface | deferred #727 |
| `MIPStarRE.QPBT.extracted_obs_self_consistent_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/SwappedConsistency.lean:104` | \(x\) | Exact transport of the preceding observable bound | deferred #727 |
| `MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit` — `MIPStarRE/QPBT/Extraction/NonencodingSupport.lean:175` | \(g+(1+2\sqrt{172})\sqrt e\) | Same separate witness and game-error terms | sharp |
| `MIPStarRE.QPBT.tilde_m_consistent_point_meas_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean:107` | \((2+2\sqrt{172})(g+\sqrt e+r)\) | \(2g+(1+2\sqrt{172})\sqrt e+r\); coefficient-only differences | sharp |
| `MIPStarRE.QPBT.tilde_m_consistent_point_meas'_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean:247` | Same bound, opposite orientation | Same term orders | sharp |
| `MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/EvaluatedPauliConsistency.lean:64` | \((2+4\sqrt{172})(g+\sqrt e+r)\) | Same three orders; smaller termwise coefficients before absorption | sharp |
| `MIPStarRE.QPBT.Extraction.norm_sub_eprProjection_le_of_pauli_dist` — `MIPStarRE/QPBT/Extraction/ProjectionFromDistance.lean:84` | Projection norm error \(2\sqrt z\) | Same root order | sharp |
| `MIPStarRE.QPBT.ProjectiveSetting.exists_unit_aux_near_eprProjection` — `MIPStarRE/QPBT/Extraction/EPRState.lean:148` | Twice the projection norm error | Same order, including zero projection | sharp |
| `MIPStarRE.QPBT.exists_extraction_aux_of_global_pair_witness_explicit` — `MIPStarRE/QPBT/Extraction/StateExtraction.lean:109` | \(s^2\le16x\) | \(16Y\), after exposing the inherited state-specific interface | deferred #727 |
| `MIPStarRE.QPBT.ProjectiveSetting.extraction_pauli_dist_le` — `MIPStarRE/QPBT/Extraction/ConcretePauliComparison.lean:126` | \(D_{\rm swap}\le2z+2r+4s\) | Separate evaluated-defect, collision, and state-norm terms | sharp |
| `MIPStarRE.QPBT.exists_extraction_witness_with_component_bounds` — `MIPStarRE/QPBT/Test/Soundness/ComponentBounds.lean:38` | \(s^2\le16x\), \(D_{\rm swap}\le2x+2r+16\sqrt x\) | Same separate conclusions; the \(18(x+\sqrt x+r)\) record scale is not used for their propagation | sharp |
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_alice_le_components` — `MIPStarRE/QPBT/Test/Soundness/OperatorTransfer.lean:138` | \(D_{\rm iso}\le2D_{\rm swap}+2s^2\) | Same separate terms | sharp |
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_bob_le_components` — `MIPStarRE/QPBT/Test/Soundness/OperatorTransfer.lean:182` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.pauli_naimark_operator_distanceA_le` — `MIPStarRE/QPBT/Test/Soundness/NaimarkOperatorTransfer.lean:409` | \(D_{\rm Naimark}\le3D_{\rm iso}+6s^2\) | Same separate terms | sharp |
| `MIPStarRE.QPBT.pauli_naimark_operator_distanceB_le` — `MIPStarRE/QPBT/Test/Soundness/NaimarkOperatorTransfer.lean:474` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distanceA_le_completed` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean:570` | \(D_{\rm raw}\le2D_{\rm completed}+4s^2+344e\) | Same terms; no answer averaging | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distanceB_le_completed` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean:676` | Same inequality | Same separate terms | sharp |
| `MIPStarRE.QPBT.exists_pauli_soundness_witness_with_component_bounds` — `MIPStarRE/QPBT/Test/Soundness/ComponentBounds.lean:160` | \(s^2\le16x\); both raw errors \(\le472x+24r+192\sqrt x+344e\) | Same witness and separate orders | sharp |
| `MIPStarRE.QPBT.pauli_soundness_state_distance_le_two` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean:392` | \(s\le2\) | Universal norm cap | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_a_le_four` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean:405` | \(D_A\le4\) | Universal raw-family cap | sharp |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_b_le_four` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean:423` | \(D_B\le4\) | Universal raw-family cap | sharp |
| `MIPStarRE.QPBT.qubit_state_error_to_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:356` | Equality of state norms | Equality | sharp |
| `MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:376` | Equality with Alice's raw distance | Equality | sharp |
| `MIPStarRE.QPBT.qubit_operator_distance_b_to_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:395` | Equality with Bob's raw distance | Equality | sharp |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_explicit` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:245` | \(\delta_{\rm LD}(a_L,\beta)\) | Historical fixed-witness baseline; the stronger native-error route is recorded separately | necessary: paper `lem:ld-soundness` uses the common `deltaLd` form |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_explicit` — `MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean:317` | Same historical error | Exact compression preserves that error | necessary: paper `lem:ld-soundness` uses the common `deltaLd` form |
| `MIPStarRE.QPBT.pauli_baseline_actual_rounded_global_pair_error_bound` — `MIPStarRE/QPBT/Combining/ActualErrorBounds.lean:158` | \(\Delta_{a_G,1/327680000}\) | Historical actual rounded expression \(G\), before canonical absorption | necessary: lem:qld-4-7 prints a common a(md)^a polynomial error |
| `MIPStarRE.QPBT.exists_global_pair_witness_explicit` — `MIPStarRE/QPBT/Combining/Apply.lean:308` | \(\Delta_{a_G,1/327680000}\) | Historical witness construction at that baseline | deferred #727 |
| `MIPStarRE.QPBT.projective_setting_isometry_bounds_explicit_baseline` — `MIPStarRE/QPBT/Test/Soundness/ProjectiveSetting.lean:36` | \(\Delta_{a_P,b_0}\) | Historical common envelope; separate components are exposed above | deferred #727 |
| `MIPStarRE.QPBT.arbitrary_strategy_isometry_bounds_explicit_baseline` — `MIPStarRE/QPBT/Test/Soundness/NaimarkAssembly.lean:42` | \(\Delta_{21a_P^2,b_0}\) | Historical common envelope; exact state and separate operator transfer are available | deferred #727 |
| `MIPStarRE.QPBT.arbitrary_strategy_raw_isometry_bounds_explicit_baseline` — `MIPStarRE/QPBT/Test/Soundness/RawOperatorTransfer.lean:95` | \(\Delta_{a_0,b_0}\) | Historical raw-answer baseline | deferred #727 |
| `MIPStarRE.QPBT.pauli_soundness` — `MIPStarRE/QPBT/Test/Soundness.lean:110` | Existential \(a,b\) | Explicit baseline \((a_0,b_0)\), with proved native mixed and degree-two siblings above | necessary: retain the printed thm:pauli statement |
| `MIPStarRE.QPBT.pauli_soundness_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:461` | Existential \(a,b\) | Same explicit historical constants, with proved exact qubit siblings above | necessary: retain the printed cor:pauli-binary statement |
| `MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_combinedError` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean:63` | Mixed defects \(\le F+(m+k)d/q\); polynomial defect \(\le F\) | Separate errors, with \(F=\mathrm{mainFormalError}\) at dimension \(m+k\) and passing error \(30\varepsilon\) | sharp |
| `MIPStarRE.QPBT.exists_directCombinedTransportConstants` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Error.lean:232` | Existential constants; proof selects \(10^{23},1/80000\) | Raw \(F+(m+k)d/q\), retaining the \(1/40000\) power and its tail; explicit mixed transport interface missing | deferred #727 |
| `MIPStarRE.QPBT.exists_direct_ld_soundness` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:66` | Existential deltaLd bound | Fixed proof witnesses \(10^{23},1/80000\); public fixed-constant sibling missing | deferred #727 |
| `MIPStarRE.QPBT.ldPointPair_consistencyDefect_le` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/PointAgreement.lean:323` | \(9\varepsilon\) | Same linear game-error order | sharp |
| `MIPStarRE.QPBT.polyTupleAgreement_avg_le_mdq` — `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:34` | \(md/q\) | Same collision bound, independent of tuple length | sharp |
| `MIPStarRE.QPBT.exists_ld_soundness` — `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` | Existential constants; proof composes witnesses \(10^{24},1/160000\) | First two errors retain \(E\); third retains \(E+2\sqrt{9\varepsilon+E}+md/q\); explicit headline sibling and separated interface missing | deferred #727 |
| `MIPStarRE.QPBT.honestMeasurement_rejected_mul` — `MIPStarRE/QPBT/Test/Completeness.lean:231` | Every rejected product is zero | Exact zero | sharp |
| `MIPStarRE.QPBT.exists_spcc_value_one` — `MIPStarRE/QPBT/Test/Completeness.lean:267` | Value exactly one, with an SPCC witness | Exact perfect completeness | sharp |

## Validation and remaining backlog

The table has 152 data rows. It consists of 95 rows retained from the earlier
survey plus all 57 PR #736 bound-strength rows. Nineteen of those PR rows
replace the corresponding historical rows with the final statement, locator,
and disposition; the other 38 are new rows. No PR row is combined with another.
Fifty-four rows retain the PR cells verbatim. In the three separated-scale
rows, the PR symbols `Y` and `Z` are written as `Y_sep` and `Z_sep` solely to
distinguish them from the earlier extraction quantity \(Y_{\rm old}\); their
bounds and dispositions are unchanged.

For final source head `6ea9f96bd86aaaad613130dea49eefdf6e80c5a9`,
exact-head CI passed all eight steps and all nine contexts in 567 summed
step-seconds. The canonical declaration check resolved 2,198 Lean references.
The blueprint axiom closure checked 2,187 declarations across 407 modules with
zero failures: 403 statement-only and 1,784 proof-level placements. Review
5372229944 approved the mathematics and requested prose and dependency repairs;
review 5372895844 approved the final editorial patch after independently
checking that code and formulas were unchanged. The normal seven-gate merge had
no override.

The ledger records the proved bounded improvement and inherited quantitative
backlog. The explicit sibling for `exists_ld_soundness` remains deferred under
#727. The source-argument improvements grouped under #735 are independently
checked mathematics but remain unimplemented. The static C8 result is reported
only as `DELEGATED`; it is not a mathematical-coverage result or a claim that
the whole QPBT track is complete. This ledger and the companion report await
their own normal CI, `review.sh`, and separate independent mathematical review.
