# Issue 729 component-bound blueprint coverage

Date: 2026-09-29

Public-interface source commit: `88436c45b51ebf485ed31ebfdfd0414aa2c59a74`

Documentation and import normalization commit:
`b912107c82ee0ff3ae098215eb55bd57ce7e1f4e`

This ledger records the issue #729 separate state- and operator-component
bounds in the quantitative QPBT blueprint. It is a delta from the preserved
114-declaration baseline in
`audits/issue-729-baseline-blueprint-coverage.md`; none of those earlier links
or source-labelled statements was removed or redirected.

Commit `88436c45b51ebf485ed31ebfdfd0414aa2c59a74` is the frozen source of the
eight public mathematical declarations below. Commit
`b912107c82ee0ff3ae098215eb55bd57ce7e1f4e` subsequently normalized a private
helper spelling and the aggregate QPBT import; it did not change this public
component interface.

The source delta contains eight public mathematical declarations and eleven
private proof helpers. Every public declaration is linked exactly once in
Chapter 16. The private helpers are listed for completeness but are not
promoted to blueprint claims. All eight public declarations have standard
axiom closures containing only `propext`, `Classical.choice`, and `Quot.sound`
as applicable.

Two completion claims are deliberately withheld. The declarations
`exists_extraction_witness_with_component_bounds` and
`exists_pauli_soundness_witness_with_component_bounds` carry
`**Unfaithful:**` docstring markers because they assume a supplied
`GlobalPairWitness`. Their blueprint nodes therefore retain statement-level
`\leanok` markers but have no proof-level `\leanok`, even though their kernel
axiom closures are standard. The same marker policy removes proof-level
completion claims from the inherited nodes
`thm:qld-supplied-global-consistency-explicit` and
`thm:qld-extraction-witness-explicit`; their statement links remain intact.

## Public declaration correspondence

| Lean declaration | Exact mathematical signature recorded | Blueprint label | Status |
|---|---|---|---|
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_alice_le_components` | Alice's complete squared isometry distance is at most twice the swap-family squared distance plus twice the actual squared state error. | `thm:pauli-component-isometry-transfer-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.ExtractionWitness.pauli_distance_bob_le_components` | Bob's complete squared isometry distance satisfies the same separate-component estimate, on the same ideal state. | `thm:pauli-component-isometry-transfer-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.raw_pauli_effects_sum_adjoint_mul_le_one` | For any Pauli-answer POVM, the prescribed Pauli subfamily satisfies `sum M_u^* M_u <= I`. | `lem:pauli-raw-effects-square-sum-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.pauli_soundness_state_distance_le_two` | For any strategy and any soundness witness, the extracted and ideal unit states have norm distance at most `2`. | `thm:pauli-universal-distance-caps-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_a_le_four` | For any strategy, soundness witness, and Pauli basis, Alice's prescribed-family squared distance is at most `4`. | `thm:pauli-universal-distance-caps-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.raw_pauli_operator_distance_b_le_four` | Under the same witness-only conditions, Bob's prescribed-family squared distance is at most `4`. | `thm:pauli-universal-distance-caps-support` | Statement and proof marked complete. |
| `MIPStarRE.QPBT.exists_extraction_witness_with_component_bounds` | For `r = md/q` and `x = 2800(deltaG + sqrt epsilon + r)`, a supplied global witness gives one extraction witness at scale `18(x + sqrt x + r)` with squared state error at most `16x` and both swap-family distances at most `2x + 2r + 16 sqrt x`, using one auxiliary vector. | `thm:qld-supplied-extraction-components-explicit` | Statement marked; proof marker withheld because the declaration is marked unfaithful. |
| `MIPStarRE.QPBT.exists_pauli_soundness_witness_with_component_bounds` | For one supplied global witness on the Naimark setting, one soundness witness has squared state error at most `16x` and both prescribed-family squared distances at most `472x + 24r + 192 sqrt x + 344 epsilon`. | `thm:pauli-supplied-global-component-transfer-explicit` | Statement marked; proof marker withheld because the declaration is marked unfaithful. |

The two supplied-witness rows display all hypotheses: `0 <= epsilon <= 1`,
`0 <= deltaG`, the projective setting or arbitrary strategy with its passing
bound, and the single supplied global polynomial-pair witness. No public entry
presents that witness as internally constructed.

## Private declaration inventory

| Private declaration | Mathematical role | Blueprint treatment |
|---|---|---|
| `full_pauli_distance_alice_of_le` | Reindexes a parameterized Alice swap-family bound into the complete tensor-placement distance. | Explained in the component-transfer proof; no link. |
| `full_pauli_distance_bob_of_le` | Bob-side version of the same reindexing. | Explained in the component-transfer proof; no link. |
| `raw_sum_conj_isometry_adjoint_mul_le_one` | Transfers a square-sum contraction through an isometry. | Used in the universal-cap proof narrative; no link. |
| `raw_left_sum_adjoint_mul_le_one` | Transfers the contraction through left tensor placement. | Used in the universal-cap proof narrative; no link. |
| `raw_right_sum_adjoint_mul_le_one` | Transfers the contraction through right tensor placement. | Used in the universal-cap proof narrative; no link. |
| `rawIdealPauliMeasurement` | Packages the canonical Pauli projectors as a complete measurement. | Private definition; no public claim or link. |
| `raw_pauli_proj_on_a_eq_tensor` | Identifies Alice's ideal projector with its tensor placement. | Private register identity; no link. |
| `raw_pauli_proj_on_b_eq_tensor` | Identifies Bob's ideal projector with its tensor placement. | Private register identity; no link. |
| `raw_pauli_proj_on_a_sum_adjoint_mul_le_one` | Gives the ideal Alice family's square-sum contraction. | Used in the universal-cap proof narrative; no link. |
| `raw_pauli_proj_on_b_sum_adjoint_mul_le_one` | Gives the ideal Bob family's square-sum contraction. | Used in the universal-cap proof narrative; no link. |
| `ideal_state_norm_one` | Proves normalization of the ideal state from the auxiliary and EPR factors. | Used in the universal state-cap proof narrative; no link. |

## Faithfulness verdict

The six unconditional public estimates are Lean-only support statements and
match their displayed hypotheses and conclusions exactly. The two witness
existence statements also match their Lean signatures exactly, but have an
extra supplied-global-witness assumption relative to the source construction.
They remain visibly conditional and do not carry proof-level completion tags.
The source theorem `thm:pauli` and the source lemma `lem:qld-unitary` are not
claimed to be discharged by this delta.
