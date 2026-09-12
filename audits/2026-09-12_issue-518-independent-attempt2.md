# Point consistency through an encoding-supported reference

Session `prover-518-20260912-04`, continuing
`prover-518-20260912-02` in the assigned independent-attempt worktree.
Starting head: `d647a481`. Assigned statement:
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Result and duplicate completion

`MIPStarRE.QPBT.tildeM_consistent_pointMeas` is proved with its assigned
public signature unchanged. Focused compilation and a fresh axiom audit
succeed. The target depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

During validation, the original #518 branch acquired commit
`f4806b2e0a1bfbf1ae22a699a6c0e9877a1bdbdd`, committed at 07:19:48Z.
Its complete target declaration is byte-for-byte identical to this
worktree's declaration. The initial search had found only the reduction
through the still-open mass theorem. This later completion triggers the
owner's instruction to stop when the target is already discharged. The
present changes are preserved as a local source checkpoint. No duplicate
PR, full build, or review is launched; publication and exact-head CI for
the original #518 branch remain with that branch's owner.

## Mathematical argument

The source is Item 1 of `lem:qld-construct-the-paulis`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
The unrestricted substitution of decoded evaluation for polynomial
evaluation is false, as recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex`. The proof uses that identity
only for encodings.

Postprocessing the strategy's Pauli answer and the ideal ancillary answer
by the encoding of their sum gives a complete reference measurement
supported on encodings. Perfect correlation of the ancillary answers
preserves the Pauli-basis and point consistency defects under convolution.
Coupling through the expanded point measurements gives evaluated
global-marginal/reference inconsistency at most
`deltaG + C * sqrt epsilon`. Schwartz-Zippel and completeness then bound
Bob's non-encoding marginal mass by
`deltaG + C * sqrt epsilon + md/q`.

The decoded-overlap calculation bounds the target defect by `deltaG`
plus that mass. For every non-encoding outcome its evaluated overlap is
bounded by its marginal mass, and its decoded overlap is nonnegative.
The resulting bound `2 * deltaG + C * sqrt epsilon + md/q` is at most
`(C + 1) * (deltaG + sqrt epsilon + md/q)` because `C >= 1` and all
three error terms are nonnegative.

## Reused content

- The decoded-overlap auxiliary is recovered from `6521816f`, including
  its build-linter correction; its original proof is from `16ddc770`.
- The averaged defect comparison is recovered from `16ddc770`.
- The encoding reference, polynomial collision, support mass, tensor
  convolution, pair-state transport, and reference coupling modules, plus
  the public tensor-measurement API, are recovered from `e36fd1aa` (#517).
  Their earlier provenance is retained in that commit's audit
  `audits/2026-09-12_nonencoding-marginal-mass-517.md`.
- Only necessary proof modules are recovered. No other branch is modified.
  The neighboring mass, opposite-player, and observable obligations remain
  unchanged in this worktree.

## Statement integrity

- Paper assumptions: admissible parameters, a projective strategy passing
  the test, and the global measurement supplied by `lem:qld-4-7`.
- Lean assumptions: exactly the existing parameter domain,
  `0 <= epsilon <= 1`, `0 <= deltaG`, `ProjectiveSetting`, supplied
  `GlobalPairWitness`, and either Pauli basis.
- Paper conclusion: Alice's point measurement is consistent with Bob's
  pulled-apart measurement on uniformly random points, with enlarged error.
- Lean conclusion: the same player order and distribution, bounded by the
  original `deltaConstructPaulis` with a universal constant at least one.
- Verdict: exact preservation of the assigned conditional theorem and its
  documented decoder correction. The supplied witness remains an explicit
  premise; its source-facing existence is not proved here.

## Validation and accounting

Focused `lake env lean` compilation, producing private `.olean` files,
succeeds for all nine changed or recovered Lean modules. The target
signature matches the assigned base byte-for-byte. The target, its defect
comparison, `global_marginal_encoding_consistency`, and
`right_mass_outside_encoding_le_evaluated_defect` have no `sorryAx`.
The unchanged `nonencodingMarginalMass_le` still has `sorryAx`, confirming
that it is outside the completed target's dependency closure. Four unrelated
direct holes remain in `Consistency.lean`; no hole or axiom is introduced.
The hook-installation, whitespace, and proof-integrity scans pass.

Prior failed sessions remain failed: `prover-518-20260912-01` records
2532 seconds and unknown usage; `prover-518-20260912-02`, thread
`01a09423-ca53-79e2-8687-809b7cefba4e`, records 59 seconds and unknown
usage after exhausted HTTP 503 retries. Their combined recorded wall time
is 2591 seconds, not an active-work estimate or an episode total. This
worktree had no uncommitted partial work on entry. Neither missing usage
nor retry time is reclassified as zero, and no counter is reset. The
dispatcher retains the present session's time and usage; support-proof
costs remain in their original #517 and prerequisite records.
