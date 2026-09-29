# Issue 729 coefficient-30 global-pair blueprint coverage

Date: 2026-09-29

This ledger records the 38 quantitative declarations introduced by source
commit `dee02c251105a9975bb77733566f29d75b872828`.  The correspondence is frozen
against that commit, rather than against file line numbers: the scalar source
had 1183 lines and SHA-256
`38de7dc50bcc802fc38ce4159dcdc54c943258d6026e7601470e3bbe39893d9c`, while
`Combining/Quantitative.lean` had SHA-256
`603a6add70ff7f98088b8d1253646729a4c7e6e3ea1f041debcbc47d2fc0e396`.
Subsequent file splitting may move declarations without changing this public
interface.

The seven new nodes are Lean-only quantitative or scope-restricted statements.
They do not replace or modify any paper-labelled node.  In the table, `P` is
an admissible Pauli parameter triple, `D` is a direct low-degree parameter
tuple, `n=md`, `rho=md/q`, and the displayed envelopes and errors are exactly
those defined in `def:qld-coefficient-thirty-scales` and the pre-existing
baseline nodes.

| Fully qualified declaration | Kind | Blueprint node | Complete signature summary |
|---|---|---|---|
| `MIPStarRE.QPBT.quantitativeLowDegreePower` | def | `def:qld-coefficient-thirty-scales` | Real constant `1/8192`. |
| `MIPStarRE.QPBT.quantitativeGlobalPairPower` | def | `def:qld-coefficient-thirty-scales` | Real constant `1/33554432`. |
| `MIPStarRE.QPBT.quantitativePreRoundingPower` | def | `def:qld-coefficient-thirty-scales` | Real constant `1/4194304`. |
| `MIPStarRE.QPBT.directQuantitativeEnvelope` | def | `def:qld-coefficient-thirty-scales` | For real `epsilon,q,m,d`, the sum `epsilon^(1/8192)+q^(-1/8192)+2^(-md/8192)`. |
| `MIPStarRE.QPBT.quantitativePreRoundingEnvelope` | def | `def:qld-coefficient-thirty-scales` | For admissible `P` and real `e`, the same three-term envelope with exponent `1/4194304`. |
| `MIPStarRE.QPBT.quantitativeGlobalPairEnvelope` | def | `def:qld-coefficient-thirty-scales` | For admissible `P` and real `e`, the same three-term envelope with exponent `1/33554432`. |
| `MIPStarRE.QPBT.three_rpow_quantitative_low_degree_power_le_two` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | `3^(1/8192) <= 2`. |
| `MIPStarRE.QPBT.direct_ld_aux_parameter_linear_triangle_exp_arg` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters, identifies the linear-triangle exponential argument after substituting `N_D=2560000 m^3 d`. |
| `MIPStarRE.QPBT.direct_ld_aux_parameter_quarter_le` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters, the fourth root of the auxiliary sampling parameter is bounded by the stated coarse `md` expression. |
| `MIPStarRE.QPBT.direct_ld_aux_parameter_quarter_le_sharp` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | The degree-sensitive refinement of the preceding fourth-root bound. |
| `MIPStarRE.QPBT.direct_ld_field_term_quantitative_eq` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters, factors the field term into the `q^(-1/8192)` contribution used in `E_D`. |
| `MIPStarRE.QPBT.direct_ld_exponential_term_quantitative_le` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters, bounds the native exponential tail by the `2^(-md/8192)` contribution. |
| `MIPStarRE.QPBT.direct_ld_test_term_quantitative_le` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters and nonnegative incoming error, bounds the test term by its `epsilon^(1/8192)` contribution. |
| `MIPStarRE.QPBT.direct_quantitative_envelope_nonneg` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | `E_D(epsilon) >= 0` for nonnegative `epsilon` and direct parameters. |
| `MIPStarRE.QPBT.direct_ld_linear_triangle_raw_error_le` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | Under the direct-parameter and nonnegative-error hypotheses, the native linear-triangle raw error is at most `30(md)^30 E_D(epsilon)`. |
| `MIPStarRE.QPBT.main_formal_linear_triangle_error_le_delta_ld_quantitative` | theorem | `thm:qld-coefficient-thirty-ldt-scalars` | For direct parameters with `k=1` and nonnegative error, the linear-triangle error is at most `delta_ld(30,tau,epsilon,q,m,d,k)=30(md)^30 E_D(epsilon)`. |
| `MIPStarRE.QPBT.pauli_baseline_point_constant_le` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | `C_pt <= 10^15`. |
| `MIPStarRE.QPBT.pauli_baseline_line_constant_le` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | `C_line <= 10^5`. |
| `MIPStarRE.QPBT.pauli_baseline_extended_line_constant_le` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | `C_ext <= 10^9`. |
| `MIPStarRE.QPBT.pauli_baseline_passing_constant_le` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | `C_pass <= 10^8`. |
| `MIPStarRE.QPBT.pauli_baseline_direct_passing_bound_uncapped` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | For admissible `P`, `0<=e,r<=1`, the direct passing envelope at the constructed point and extended-line errors is at most `10^8 m(e^(1/512)+r^(1/32))`, without a unit cap. |
| `MIPStarRE.QPBT.direct_passing_error_envelope_quantitative_bound` | theorem | `thm:qld-coefficient-thirty-passing-scalars` | For real `n>=1` and `0<=e,r<=1`, `V(E_pt(e)+n E_ext(e,r),r) <= n E_pass(e,r)`. |
| `MIPStarRE.QPBT.quantitative_low_degree_error_bound` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | For admissible `P`, `0<=e<=1`, and `rho<=1`, the coefficient-30 low-degree error for dimension `2m+2` is at most `10^30 n^32 E_pre(P,e)`. |
| `MIPStarRE.QPBT.quantitative_pre_rounding_envelope_nonneg` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | `E_pre(P,e)>=0` for admissible `P` and `e>=0`. |
| `MIPStarRE.QPBT.quantitative_point_error_root_bound` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | For admissible `P` and `0<=e<=1`, `sqrt(E_pt(e)) <= 4*10^7 E_pre(P,e)`. |
| `MIPStarRE.QPBT.quantitative_ratio_bound_of_nonneg` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | For admissible `P` and `e>=0`, `rho <= n E_pre(P,e)`. |
| `MIPStarRE.QPBT.quantitative_pre_rounding_envelope_eighth_root_le` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | For admissible `P` and `e>=0`, the eighth root of `E_pre(P,e)` is at most `E_pair(P,e)`. |
| `MIPStarRE.QPBT.quantitative_actual_rounded_global_pair_error_bound` | theorem | `thm:qld-coefficient-thirty-rounding-scalars` | For admissible `P`, `0<=e<=1`, and `rho<=1`, the capped exact rounded-pair error `min(1,R)` is at most `10^7 n^4 E_pair(P,e)`, with `delta`, `eta`, and `R` displayed in the node. |
| `MIPStarRE.QPBT.direct_coordinate_main_formal_quantitative` | theorem | `thm:qld-coefficient-thirty-direct-soundness` | For a projective direct strategy, `k=1`, a coordinate, nonnegative error, and value at least `1-epsilon`, constructs projective polynomial measurements with all three coordinate defects at most `delta_ld(30,tau,epsilon,q,m,d,k)`. |
| `MIPStarRE.QPBT.exists_direct_simultaneous_polynomial_measurements_quantitative_of_k_eq_one` | theorem | `thm:qld-coefficient-thirty-direct-soundness` | Under the same projective, `k=1`, nonnegative-error, and passing hypotheses, constructs one-coordinate tuple measurements with the same three bounds. |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_quantitative` | theorem | `thm:qld-coefficient-thirty-direct-soundness` | For positive error, a projective direct strategy with `k=1` and value at least `1-epsilon` has projective tuple measurements satisfying all three coefficient-30 bounds. |
| `MIPStarRE.QPBT.direct_ld_soundness_of_k_eq_one_any_strategy_quantitative` | theorem | `thm:qld-coefficient-thirty-direct-soundness` | For positive error and an arbitrary direct strategy with `k=1` and value at least `1-epsilon`, dilation and compression give tuple measurements with the same three bounds; output projectivity is not asserted. |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_ordered_estimates_quantitative` | theorem | `thm:qld-coefficient-thirty-rounded-polynomials` | From a projective setting plus supplied combined-point and directly indexed extended-line witnesses, constructs projective rounded polynomial measurements with both ordered defects on both placements bounded by `E=4 eta+8 delta_Q`. |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_scalar_mass_quantitative` | theorem | `thm:qld-coefficient-thirty-rounded-polynomials` | Under the same supplied witnesses, additionally bounds both scalar nonlinear masses by `2E+2((2m+2)d+1)/q`. |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_wrong_variable_mass_quantitative` | theorem | `thm:qld-coefficient-thirty-rounded-polynomials` | Under the same supplied witnesses, additionally bounds both wrong-variable masses by `2E+2(2md+2)/q`. |
| `MIPStarRE.QPBT.ExtendedLineGame.rounded_polynomial_separated_mass_quantitative` | theorem | `thm:qld-coefficient-thirty-rounded-polynomials` | Under the same supplied witnesses, constructs rounded measurements with both ordered defects at most `E` and both non-separated masses at most `6E+(12md+4d+10)/q`. |
| `MIPStarRE.QPBT.ExtendedLineGame.pair_witness_of_points_lines_quantitative` | theorem | `thm:qld-coefficient-thirty-rounded-polynomials` | Under the same supplied witnesses, constructs complete projective polynomial-pair measurements whose four point defects are at most `8E+(12md+4d+14)/q`; no sign or small-regime assumption is required. |
| `MIPStarRE.QPBT.exists_quantitative_global_pair_witness` | theorem | `thm:qld-small-regime-global-pair` | For admissible `P`, a projective Pauli setting, `0<=e<=1`, and `md/q<=1`, constructs the two complete projective pair measurements and `g` with `0<=g<=10^7(md)^4 E_pair(P,e)`, bounding all four point defects; no global-pair witness is supplied. |

Every declaration occurs in exactly one `\lean{...}` tag in the active
blueprint.  The 32 theorem declarations were checked in a temporary module
importing both `MIPStarRE` and `MIPStarRE.QPBT.Combining.Quantitative`; every
axiom closure was exactly `propext`, `Classical.choice`, and `Quot.sound`.
The aggregate `MIPStarRE.QPBT` import at this snapshot does not yet re-export
`Combining.Quantitative`; that export is the remaining integration-side delta.
