---
date: 2026-09-14
issue: 529
pr: 536
role: native-prover-continuation
base: cd67b656b00b4b0c202db4398b8e1ae2761316c9
started_at: 2026-09-14T20:23:50+09:00
deadline: 2026-09-14T11:48:50Z
elapsed_budget_seconds: 1500
finalization_reserve_seconds: 180
status: naimark-witness-pullback-proved
source_theorem_status: notready
prior_report: audits/2026-09-14_pauli-soundness-529-transfer.md
new_public_declarations: 32
---

# Pauli soundness under genuine Naimark compression

## Result and scope

The actual, value-preserving Naimark dilation and return of supplied
soundness data to an arbitrary original strategy are proved. Both original
local spaces and measurement families remain independent. No projectivity,
symmetry, ideal-state range assumption, additional field assumption, or
outcome-count factor is imposed on the original strategy.

For a supplied witness on the concrete dilation, let `e` be its unsquared
state error and `dA`, `dB` its Pauli squared-sum errors at one basis. The
composed witness has exactly the same state error and satisfies

```text
original Alice distance <= 3 * dA + 6 * e^2
original Bob distance   <= 3 * dB + 6 * e^2
each original distance <= 4
```

Consequently, if all three supplied errors are at most `delta`, the state
error remains at most `delta` and both operator errors are at most
`9 * delta`, for every nonnegative `delta`. The small-error estimate is
`3 * delta + 6 * delta^2`; use it for `delta <= 1`, and use the absolute
bound four for `delta >= 1`. A common bound for all conclusions is
`9 * delta`. If the supplied bound is `deltaQld a b epsilon m d q`, with
`a >= 1` and `epsilon >= 0`, replacing `a` by `9 * a` absorbs this factor.
The exponent `b` is unchanged and no upper bound on `epsilon` is needed
for this scalar comparison.

These are conditional transfer theorems. The supplied data are precisely
the witness and its three error bounds for the actual dilation. They are
not new hypotheses of `pauli_soundness`.

## Construction and exact identities

Before proving, this session read `AGENTS.md`, the prover persona, local
README and DESIGN, the prior transfer audit, paper `thm:pauli` at
`08_classical_and_quantum_low_degree_tests.tex:1426-1447`, the final argument
at `14_analysis_of_the_pauli_basis_test.tex:1862-1876`, and the extraction
transfer paper-gap note. Full strategy-construction signatures were inspected.

`pauliNaimarkStrategy` uses the existing `paddedStrategy` and
`dilatedMeasurement` APIs with the actual `naimarkEmbedding` maps. Its
projectivity, prepared-state equality, and exact game-value preservation
are proved. `pauliNaimarkSetting` composes these facts with the original
winning premise to produce the existing `ProjectiveSetting` type.
No value-attainment theorem or `exists_spcc_value_one` is invoked.

For each player and every Pauli outcome, `compressAt_postprocess` and
`compressAt_dilatedMeasurement` give compression of the actual
`pauliQuestion` / `pauliAnswerOrZero` readout. With `J` the corresponding
ground embedding, `naimarkCompression_eq_adjoint` expresses this as
`M_h = J.adjoint * P_h * J`. For the supplied isometry `phi`, set
`Q = phi * J * J.adjoint * phi.adjoint` and
`N_h = phi * P_h * phi.adjoint`. The two public
`ofNaimark_compression_alice/bob` identities say exactly

```text
(phi * J) * M_h * (phi * J).adjoint = Q * N_h * Q
```

with the appropriate identity operator on the other player's full space.
The proof never infers the generally false identity `P_h * J = J * M_h`.
The previous one-sided intertwining transfer is preserved and is not used
as a substitute for this two-sided compression estimate.

The three-term decomposition is
`Q(N_h-T_h)Delta - Q N_h(I-Q)Delta - (I-Q)T_h Delta`.
The generic analytic estimate uses summed-square contraction of `N` and
of the opposite-register mirror family. The explicit EPR coordinate proof
retains `M.transpose` for a general complex matrix. Its specialization uses
the existing `pauliProj_transpose` theorem for the fixed field model;
same-label transport is derived, not assumed. This introduces no new field
instance or restriction on `AdmissibleParams`. General-prime source-domain
questions remain separate from this existing interface.

The actual transformed state is fixed by each local `Q`. The ideal state
is unit because its auxiliary vector and EPR factor are unit. Neither the
proof nor the converter assumes that ideal state lies in either range.
The contraction proof explicitly handles isometrically conjugated
families whose sum is only a range projection on the enlarged space.

## Validation and statement integrity

Focused Lean checks passed for `CompressionBounds.lean`, `IdealPauli.lean`,
`NaimarkTransfer.lean`, and their `Soundness.lean` re-export. The new modules
have no warnings or proof-integrity tokens. The re-export reports only the
inherited `pauli_soundness` proof hole. Products and reproducer logs are
private to this worktree under `.lake/`; no full build was run.

Full signatures and transitive axiom closures are checked in
`.lake/issue529-naimark-axioms.lean`, with output in its `.log` counterpart.
All 32 new public declarations, including both dilation producers, both
compression identities, both complete operator estimates, and both
converters, use only `propext`, `Classical.choice`, and `Quot.sound`.
The existing transpose theorem was checked separately. The unchanged
source theorem still depends on `sorryAx`. These are full closures,
including private helpers, not just scans of the new proof bodies.
The 13 preserved supplied-extraction declarations were also rechecked; each
retains the same three standard axioms. Their separate log is
`.lake/issue529-transfer-axioms-preserved.log`.

`leanblueprint web` passed. Blueprint synchronization passed after updating
the ignored derived declaration index, with the 14 pre-existing warnings
about statement-only formalization marks. The existing declaration checker
resolved all 1459 entries via `lake env lean --run scripts/Checkdecls.lean`.
The installed-hook check and whitespace check passed. Normal commit-hook
results and the exact final commit are reported in the terminal receipt.

The public theorem's assumptions, quantifier order, error function, and
three conclusions are unchanged. The paper assumes an admissible tuple
and a successful arbitrary strategy; its conclusion is local isometries,
a unit auxiliary state, the norm bound, and both Pauli comparisons on the
ideal state. Lean retains its existing finite-dimensional, fixed-field
encoding and the same source-shaped statement. Verdict: unchanged
boundary encoding, inherited proof hole, no new source completion.
Both new blueprint support examples expose the supplied-witness premise.
The source node remains not ready.

## Remaining obligations and preserved work

The Naimark return is no longer an obstacle. Unrestricted soundness still
requires the genuine global-pair construction, including its zero-error
endpoint, and composition with the proved conditional extraction result
published in PR #544 at `6857f1c510f569b63b72ff022b2476d641f5ff5b`.
That branch was not imported. This base's inherited unfinished
`exists_extractionWitness_ofGlobalPairWitness` was not invoked. The
source-domain and combined-lines error comparisons also remain upstream.
There is no proof hole in the new return or scalar composition.

`RangeProjection.lean`, `Ancilla.lean`, `ErrorBounds.lean`,
`StateTransfer.lean`, and `OperatorTransfer.lean` are byte-for-byte unchanged
from the base. The previous audit remains intact; its description of the
then-outstanding Naimark return is superseded only by this dated result.
No descendant, full build, CI/review run, dispatch, publication, push, PR
mutation, hook override, or runtime/account/cap change occurred. All writes
were confined to the authorized issue-529 worktree. Issue #513 and frozen
PR #552 were not touched.

## Cost provenance

Preserved historical spans are 6020 seconds of overlapping prerequisites,
1903, 48, 5722, and 2295 seconds, and the latest supplied-extraction
transfer's 1111.608 seconds. They remain separate and are not summed into
unique active time. The prior report retains the corresponding historical
token records. Unknown per-session counts remain unknown, and cumulative
native token snapshots are nonadditive. MAIN records this session's final
native telemetry; this worktree neither edits that registry nor resets
prior attribution.
