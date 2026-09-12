# Issue 509: point error through a line-point coupling

Session `prover-509-20260912-04`, dispatched at 07:29:34Z on September 12,
2026, on pinned main `fd83ecda4ec0bf8397687eff9ebcc034525d0dd6`.
The active-work limit is 25 minutes; this is a continuation of the existing
gap episode, not a reset of its mathematical or operational costs.

## Mathematical Result

For a fixed line and a point on it, let T be the line POVM, Q the opposite
point POVM, e(f) the evaluation of a line outcome, and c a deterministic
reference answer. Define the joint weights

    w(f,a) = <psi, (T_f tensor Q_a) psi>.

Positivity makes these weights nonnegative. Completeness gives their row and
column marginals as the expectations of T_f tensor I and I tensor Q_a.
The pointwise indicator inequality

    |1[e(f) != a] - 1[e(f) != c]| <= 1[a != c]

therefore implies

    |Pr[e(f) != a] - Pr[e(f) != c]| <= Pr[a != c].

The new `line_point_coupling_disagreement_le` proves this for any nonnegative
finite weights. `line_point_povm_coupling_le` constructs the quantum coupling
and proves both marginal identities. `consistencyDefect_line_point_coupling_le`
averages it and identifies the first term with the repository's actual
`consistencyDefect`. Evaluating a fixed line POVM by postprocessing supplies
its T argument; no independence of the line and point answers is assumed.
The result applies to the completed answer alphabet as well as field answers.

The coefficient one is sharp: take a deterministic line answer c and a
deterministic point answer different from c. The two sides of the inequality
are then both one in a unit state. More generally, mixtures give equality at
every point error between zero and one. No normalization is needed for the
formal statements, which also hold for unnormalized nonnegative weights.

This estimate retains an actual measured point error, not the declared upper
bound `deltaQ` and not the strategy error. It implies a robust lower bound:
any lower bound b on disagreement with the deterministic reference yields
line-point disagreement at least b minus the actual point error.

## Independent Obstruction Check

The source was read first: `lem:qld-4-13` at lines 1020-1034 and
`claim:17-1` at lines 1140-1173 of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
The source retains the error of the previously constructed points. Blueprint
`lem:qld-4-13` is still marked `notready`.

For m=d=1 and perfect strategies, the unrestricted auxiliary admits
deterministic joint answers (x^2,0) at a sufficiently large finite point-error
bound. The combined answer is alpha*x^2. On X-axis lines with alpha nonzero,
each permitted affine polynomial agrees at at most two field points. The
coupling shows explicitly why arbitrary random line outcomes cannot improve
that bound: their marginal weights are independent of the subsequently
sampled point. The X-axis part of the direct law has mass 1/8, giving

    defect >= (1/8) * (1 - 1/q) * (1 - 2/q).

For unbounded admissible q=2^(2k+1), this tends to 1/8. The requested
`IsPolyErr₂` bound at (0,1/q) tends to zero. This is the existing mathematical
obstruction, independently checked, not a newly kernel-checked negation.
Formal integration into the direct line law, unbounded admissible parameters,
and admission-free perfect strategies remain prerequisites of a full formal
refutation. The coupling lemmas do not use these missing prerequisites.

## Provenance and Costs

The first #509 receipt is
`~/.cache/mipstarre-dev/sessions/prover-509-20260912-01.last.md`, published
at `54716ad9118f6250be63b30c9bee0dc2fbd79eb2` (PR #531).
Its dispatcher duration is 2869 seconds, superseding its 47-minute checkpoint.
The second approach's two dispatches produced no proof: session -02 failed
with service errors after 58 seconds and -03 failed with concurrency errors
after 914 seconds. Their immutable JSONL receipts were read; missing token
usage remains unknown, not zero.

The related finite-POVM proof at
`a4917f5da004a44085d4e910f36de023b6702445` and its audit were read without
modifying or importing that predecessor. It records reuse of first-attempt
#509 lemmas. The present change reuses the existing main tensor-positivity,
quadratic-form summation, and averaging APIs, and adds a distinct coupling
estimate. No predecessor code is duplicated. All-ref history of `Apply.lean`
was searched; the newer saved `aeaca3ae` also leaves this exact target admitted.

The established historical subtotal is 28436 seconds for thirteen #118 and
three #119 sessions. Adding #509's 2869, 58, and 914 seconds and the related
#511 sessions' 828 and 3957 seconds gives 37062 seconds before this session.
This includes failed service waits as recorded wall time, without calling
them active mathematical work. Review and operator costs are excluded, not
zero. Add this session's final dispatcher duration once, replacing any
in-progress checkpoint interval; cumulative token counters are not summed.

## Statement Integrity and Validation

Paper assumptions: admissible projective strategy and the previously
constructed points with polynomially controlled error. Lean assumptions:
every real `deltaQ` and every point witness at that error, with no relation
to epsilon. Paper conclusion: field-answer line consistency with degree
md+1 and axis degree d. Lean conclusion: the directly indexed, completed-answer
witness at `deltaCombine(m^2*epsilon,md/q)`, independent of the supplied
point error. Verdict: unsupported strengthening by universal point choice,
in addition to the documented distribution and completed-answer differences.

The public signature, constants, quantifiers, and existing proof hole are
unchanged. New results are formalization-only auxiliaries, so no paper
completion marker is added. Focused checks and axiom audit results, exact
published head, and CI status are recorded in the final session receipt.
No descendant, reviewer, merge, or change to another worktree is authorized
or performed by this session. The next gate is independent review of this
auxiliary result, followed by a separately scoped interface-realignment
decision for the obstructed target.
