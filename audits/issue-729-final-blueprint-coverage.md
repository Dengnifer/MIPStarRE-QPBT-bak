# Issue 729 final quantitative soundness blueprint coverage

Date: 2026-09-29

Lean source commit: `3ae0b085606b4cdbbc6fe99dbde2f314a691ab50`

Assigned integration head: `95b4dec9c9d5829e1f7189c77d812645655fbf3e`

This ledger records the final issue #729 documentation delta. It is additional
to the preserved 114-declaration baseline, the eight component declarations,
and the 38 coefficient-30/global-pair declarations in the three earlier issue
#729 coverage ledgers. No source-labelled blueprint statement or link is
replaced.

The source delta relative to admission commit `388bfa7c` contains exactly 29
new public mathematical declarations: four definitions and 25 theorems. The
split of `Combining/QuantitativeScalars.lean` and
`Test/Soundness/RawOperatorTransfer.lean` only moved earlier declarations and
did not create additional public mathematics. Every new declaration below is
linked exactly once in the final Lean-only section of Chapter 16.

## Correspondence

| Kind | Lean declaration | Blueprint label |
|---|---|---|
| `def` | `MIPStarRE.QPBT.pauliSoundnessQuantitativePower` | `def:pauli-final-quantitative-error` |
| `def` | `MIPStarRE.QPBT.pauliSoundnessQuantitativeEnvelope` | `def:pauli-final-quantitative-error` |
| `def` | `MIPStarRE.QPBT.pauliSoundnessQuantitativeRawError` | `def:pauli-final-quantitative-error` |
| `def` | `MIPStarRE.QPBT.pauliSoundnessQuantitativeError` | `def:pauli-final-quantitative-error` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_power_eq_half_global_pair` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_power_pos` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_power_lt_one` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_power_eq_gain_mul_baseline` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_envelope_nonneg` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.quantitative_global_pair_envelope_le_pauli_soundness` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.sqrt_quantitative_global_pair_envelope_le_pauli_soundness` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.sqrt_error_le_quantitative_global_pair_envelope` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.quantitative_ratio_le_global_pair_envelope` | `thm:pauli-final-envelope-support` |
| `theorem` | `MIPStarRE.QPBT.quantitative_extraction_scale_le` | `thm:pauli-final-component-absorption` |
| `theorem` | `MIPStarRE.QPBT.sqrt_quantitative_extraction_scale_le` | `thm:pauli-final-component-absorption` |
| `theorem` | `MIPStarRE.QPBT.quantitative_state_component_le_raw_error` | `thm:pauli-final-component-absorption` |
| `theorem` | `MIPStarRE.QPBT.quantitative_operator_component_le_raw_error` | `thm:pauli-final-component-absorption` |
| `theorem` | `MIPStarRE.QPBT.four_le_pauli_soundness_quantitative_raw_error_of_md_eq_one` | `thm:pauli-final-full-domain-support` |
| `theorem` | `MIPStarRE.QPBT.four_le_pauli_soundness_quantitative_raw_error_of_one_le_ratio` | `thm:pauli-final-full-domain-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_envelope_mono_error` | `thm:pauli-final-full-domain-support` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_error_le_deltaQld` | `thm:pauli-final-full-domain-support` |
| `theorem` | `MIPStarRE.QPBT.one_hundred_lt_pauli_soundness_baseline_constant` | `thm:pauli-final-baseline-comparison` |
| `theorem` | `MIPStarRE.QPBT.deltaQld_quantitative_lt_explicit_baseline` | `thm:pauli-final-baseline-comparison` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_error_lt_explicit_baseline_of_le_one` | `thm:pauli-final-baseline-comparison` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_error_lt_explicit_baseline_clipped` | `thm:pauli-final-baseline-comparison` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative` | `thm:pauli-final-quantitative-soundness` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_quantitative_canonical` | `thm:pauli-final-quantitative-soundness` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative` | `cor:pauli-final-quantitative-qubit` |
| `theorem` | `MIPStarRE.QPBT.pauli_soundness_qubit_quantitative_canonical` | `cor:pauli-final-quantitative-qubit` |

## Statement audit

The structured error is
`min 4 (10^14 * (m*d)^4 * E_b(P, min epsilon 1))`, with
`b = 1/67108864` and
`E_b(P,e) = e^b + q^(-b) + 2^(-b*m*d)`. The raw and qubit headlines retain the
full source parameter domain: admissible parameters, nonnegative error, an
arbitrary strategy, and value at least `1 - epsilon`. They construct one
witness shared by the unsquared state norm and both prescribed-answer sums of
squared operator-action norms. No small-regime, supplied-witness, bridge, or
range hypothesis is added. The isometry-conjugated effects retain their range
projections.

The canonical corollaries use `deltaQld 100 b` with the same witnesses. The
comparison theorem is strict for `0 <= e <= 1`; on the full nonnegative domain
it compares the new error with the fixed baseline evaluated at
`min epsilon 1`. It therefore does not claim a strict inequality between two
universally saturated caps. The exponent identity gives the exact improvement
factor `625/8 = 78.125` over the fixed baseline exponent
`1/5242880000`.

## Validation record

The declaration inventory was taken from
`/tmp/qpbt-final-c-public-declarations-729.json` and checked against commit
`3ae0b085606b4cdbbc6fe99dbde2f314a691ab50`. The inventory contains 29 new
public mathematical declarations, and the final Chapter 16 section links all
29 exactly once. The four definitions and 25 theorems have no missing or
duplicate blueprint links.

The command `leanblueprint web`, run from `blueprint/`, completed successfully;
it emitted only the repository's existing missing-bibliography warnings. After
regenerating `blueprint/lean_decls`, the normal command
`lake exe checkdecls blueprint/lean_decls` resolved all 2,132 declarations.
`scripts/blueprint_lean_sync.py --root . --ci` reported that the blueprint and
Lean code are in sync. Its four orphan-`\leanok` warnings and six
header-`\leanok` warnings concern pre-existing Chapter 13, Chapter 14, and
earlier Chapter 16 entries; this change does not alter those entries.

The aggregate import was refreshed with the targeted command
`lake build MIPStarRE.QPBT`; no full `lake build` was run. The root import then
checked all 25 newly linked theorems with no `sorryAx`, and every axiom closure
contained only `propext`, `Classical.choice`, and `Quot.sound`. The scoped
LaTeX convention check, unfaithful-marker audit, blueprint sync audit, and
`git diff --check` all completed successfully.
