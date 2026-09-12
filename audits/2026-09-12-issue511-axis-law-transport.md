# Issue 511: restricted axis-law transport

Session `prover-511-20260912-03`, started 2026-09-12T07:30:18Z.
Pinned main: `fd83ecda4ec0bf8397687eff9ebcc034525d0dd6`.
The third attempt has a 25-minute limit, superseding the older 60-minute
paragraph. No descendants or reviewers were launched.

## Result

`Combining/AxisObstructionTransport.lean` proves the distributional part of
the finite quadratic obstruction. For a direct dimension M and coordinate i,
the restriction of the actual `directLinePointDist` to axis lines with index i
has weight 1/(2M). Its average can first sample a canonical line and then an
independent uniform affine parameter, while retaining the line as an argument
of the integrand. The proof reuses the existing joint resampling theorem in
`DirectLowDegree/Transport/LineResampling.lean`.

Canonicalizing an i-axis line preserves each coordinate j distinct from i.
The j-coordinate of the resulting canonical base is uniform. This is proved
from the kernel property of `lineRepMap` and Mathlib's `Equiv.funSplitAt`;
it does not assume that the representative has zero i-coordinate.

The final theorem transports a per-line lower bound g(base[j]) for any
nonnegative integrand F to

    E_direct F >= (1/(2M)) E_alpha g(alpha).

Its hypotheses concern scalar functions and finite averages. It constructs
no measurement and is not a conditional replacement for the target. At M=4
the weight is 1/8. In the quadratic example, the intended per-line bound is
zero at alpha=0 and 1-2/q otherwise. Its scalar expectation is the factor
(1-1/q)(1-2/q) established in the predecessor packet.

## Precise Remaining Obligations

The new theorems establish sampling identities and the general lower-bound
transport. They do not yet instantiate that transport with the actual
`ExtendedLinesWitness` integrand. That application must identify the placed
POVMs, their degree support and completed evaluations, and translate the
canonical affine parameter to the X-coordinate if the representative has a
nonzero X-coordinate. The source/direct scalar equivalence must also carry
the deterministic quadratic answer. Nonnegativity must be supplied for the
actual integrand, not assumed as a new paper hypothesis.

Thus neither 21/256 for the actual witness defect nor the negation of the
target is claimed as a theorem here. A fixed eight-element field cannot
refute existential universal constants. A full strategy counterexample also
requires unbounded admissible field sizes, a closed perfect-strategy
construction for those sizes, and the final asymptotic contradiction.
The target and its inherited admission remain unchanged.

## Sources and Integrity Audit

Read the original `lem:qld-4-13` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`,
the construction at 1118-1137 and `claim:17-1` at 1140-1173. Read
`lem:alnf` and `def:line-point-dist` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`.
The blueprint entry is `lem:qld-4-13-established`, which already records
the direct-law and completed-answer discrepancies; no completion tag changes.

Paper assumptions: an admissible projective strategy and the preceding
constructed points with polynomially controlled error. Lean assumptions:
the strategy and arbitrary real point error, with every witness at that
error. Paper conclusion: two field-answer line consistency estimates and
the axis degree restriction. Lean conclusion: a directly indexed witness
on the completed alphabet with error C*m*deltaCombine(epsilon,md/q),
independent of the supplied point error. Verdict: the unrestricted point
quantifier is an unsupported strengthening. All target hypotheses,
quantifiers, constants, conclusions and its proof body are preserved.

## Provenance and Accumulated Cost

Immutable predecessor receipts read:
`~/.cache/mipstarre-dev/sessions/prover-511-20260912-01.last.md` and
`prover-511-20260912-02.last.md`, including the second checkpoint.
PR #525 at `23022fa0b23c4b152afc6c655affe5ad734a1b45` supplies the prose
obstruction. PR #547 at `a4917f5da004a44085d4e910f36de023b6702445`
supplies the finite POVM proof; its source and audit were read without edits.
No predecessor proof is duplicated in this PR or counted as a new closure.
All-ref history of `Apply.lean` was searched. Saved `6e8d67ef` and
`aeaca3ae` concern controlled point errors; they do not discharge the
assigned unrestricted statement.

Historical scoped prover subtotal: 28,436 seconds for the earlier #118/#119
episode, plus 828 seconds for attempt one, plus 2,869 seconds for the reused
#509 packet, plus 3,957 seconds for attempt two, gives 36,090 seconds before
this session. The primary dispatcher registry supplies the 3,957-second
final duration, superseding attempt two's 3,827-second cleanup receipt.
PR #525's 414-second review remains separate. This session's final dispatcher
duration is added once; token counters from historical resumed threads are
not summed. Other owner/operator costs are excluded, not treated as zero.

## Validation and Next Gate

The six new lemmas pass focused Lean checking. Their axiom closure and the
unchanged target are checked in the runtime file
`~/.cache/mipstarre-dev/sessions/prover-511-20260912-03-axioms.lean`.
Hook installation is checked in this worktree. Final validation and publication
results belong to the session receipt. No full-CI success is implied here.
Next gates are the remaining operator-level application, independent review,
and separately scoped repair of the unrestricted interface.
