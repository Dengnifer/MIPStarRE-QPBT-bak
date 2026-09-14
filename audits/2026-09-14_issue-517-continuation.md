# Issue 517 continuation: supplied-witness support estimate

## Result and provenance

Admission was at 2026-09-14T06:16:32Z, with a 25-minute continuation bound.
The assigned clean branch was `issue-517-proof-nonencodingmarginalmass-le`
at `e36fd1aa056782007917b0d6c5e19b85ea28179b`. That commit already proves
`MIPStarRE.QPBT.nonencodingMarginalMass_le`. This continuation verifies that
proof and records its conditional scope; it claims no new proof-hole closure.

The frozen PR539 head is `ca866da402947c9ee7e1dd5e935a2782fe0d1602`.
Its `audits/2026-09-12_issue-519-point-consistency-prime.md` records that the
support proofs were recovered from issue517's `e36fd1aa`. Its target
`nonencodingMarginalMass_le` remains unfinished on that separate branch.
Thus these inputs confirm the existing proof's prerequisites, rather than
provide a new independent proof of the target.

Only the small `NonencodingSupport.lean` difference is adopted: the explicit
supplied-witness documentation and local classical decidability scopes. The
resulting file is byte-identical to the frozen PR539 file. The target receives
the corresponding `**Unfaithful:**` marker required for source-facing use.
Its statement and proof body are unchanged. No branch merge, new helper,
axiom, proof hole, or blueprint completion marker is introduced.
The proof-level completion marker on `lem:qld-nonencoding-mass-bound` is
removed to respect the propagated source-construction marker; the explicitly
conditional statement and its declaration links remain unchanged.

The `GlobalPairWitness`, setting, and observable interfaces agree with the
frozen head, so source-interface migration is unnecessary for this target.
Commit `27f4c8110d0ff41fe834a8bb5b12bab72de44a33` separately places the joint
source obligation in `Extraction/Construction.lean` and re-exports it through
`MIPStarRE/QPBT.lean`. That obligation and the conditional theorem names on
PR539 must be retained when integrating the original issue517 target proof.
No other worktree or PR was changed.

## Mathematical statement audit

The primary passage is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
Its decoder substitution at lines 1483-1492 is false for arbitrary polynomial
representatives, as explained in `docs/paper-gaps/qpbt_decoding-identity.tex`.
The support estimate is the blueprint repair `eq:qld-nonencoding-mass`,
separately stated in `lem:qld-nonencoding-mass-bound`.

- Paper assumptions: admissible parameters and a projective strategy winning
  with probability at least `1 - epsilon`; `lem:qld-4-7`, lines 1267-1274,
  constructs the projective polynomial-pair measurements with both directed
  point-consistency estimates.
- Lean assumptions: unchanged `AdmissibleParams`, `0 <= epsilon <= 1`,
  `0 <= deltaG`, `ProjectiveSetting P epsilon`, and the explicit supplied
  `GlobalPairWitness S deltaG`. The existing domain includes `1 <= d` and
  `m` dividing `q`; no new `d < q` condition is imposed. Zero error remains
  included. The witness supplies projectivity and the two consistency bounds.
- Paper conclusion: `lem:qld-construct-the-paulis` asserts two point-consistency
  conclusions and observable self-consistency for the constructed measurements.
  The repaired proof additionally needs small non-encoding marginal mass.
- Lean conclusion: for both player sides and Pauli bases, the actual marginal
  mass is at most `C * (deltaG + sqrt epsilon + md/q)`, with universal
  `C >= 1` preceding all parameter, strategy, and witness quantifiers.
- Verdict: exactly the original Lean signature and the separately stated
  conditional blueprint repair. Relative to the source construction, the
  supplied witness is an extra conditional premise. This does not complete
  the constructor or the source-facing joint theorem.

The proof compares each marginal with the encoding of the sum of original
and ideal ancillary Pauli outcomes. Perfect ancillary consistency preserves
the game defects under additive convolution. The consistency triangle gives
`deltaG + C * sqrt epsilon`, leaving `deltaG` outside the square root.
Schwartz-Zippel adds `md/q`, and positivity and completeness bound the
non-encoding mass. Exact register identities transport that mass to the
six-register state. These are the existing proofs, not newly assumed bridges.

## Focused verification

Primary `local/bin/worktree-setup.sh --no-build` and normal hook verification
passed. The actual branch toolchain is Lean/Mathlib v4.32.0.
Both modified Lean modules were freshly compiled with `lake env lean -o`
into this worktree's private `.lake/build/lib/lean` products. The support
module has no warnings. `Consistency.lean` reports its four inherited holes.
The files have 358 and 942 lines respectively, below the 1000-line guard.
The target signature is byte-identical to the original statement at
`ae124f8f09ee002444ac5b9711822c0f1daae142`; `git diff --check` passes.

The fresh query is `.lake/issue517-continuation-axioms.lean` in this worktree.
The target and ten reference, collision, transport, and support declarations
have exactly `propext`, `Classical.choice`, and `Quot.sound` in their axiom
closures. In contrast, the four unchanged declarations
`marginalPoly_sub_pointMeas_approx_zero`, `tildeM_consistent_pointMeas`,
`tildeM_consistent_pointMeas'`, and `tildeObs_selfConsistent` report `sorryAx`.
None is a dependency of the target. No full build, CI, review, dispatch,
publication, credential change, or main write was performed.

The first normal commit-hook run rejected the existing proof-level `leanok`
on the now-marked support declaration. Removing that marker resolves the
reported inconsistency without changing the theorem. The normal hooks check
blueprint syntax and declaration metadata. Blueprint rendering is not run:
the continuation authorization limits checks to focused Lean, axiom,
declaration checks, and normal commit hooks.

The remaining source obligation is to construct the witness from
`lem:qld-4-7`, including the zero-error case absent from the current
`exists_globalPairWitness` domain, and establish all three extraction
conclusions for that same witness. PR539's `Construction.lean` retains it.

## Cumulative accounting

This is a continuation of attempt 1, not a fourth independent attempt or a
budget reset. All previous checkpoints and independent worktrees remain
untouched. The historical audit is
`audits/2026-09-12_nonencoding-marginal-mass-517.md`.

The primary `results/telemetry/sessions.jsonl` records:

| Session | Wall seconds | Input tokens | Output tokens |
| --- | ---: | ---: | ---: |
| `prover-517-20260912-01` | 3750 | 14454635 | 36862 |
| `prover-517-20260912-02` | 831 | 1623859 | 8596 |

Together with the earlier audit's partial 5699-second prerequisite subtotal,
the known subtotal is 10280 seconds before this continuation. This excludes
other tensor, transport, integration, review, and admission costs; it is not
an episode total. Cached input is included in input, and reasoning is included
in output, so neither is added again. Incomplete earlier counters remain
unknown rather than zero.

Preserved runtime receipts under `/home/drx/.cache/mipstarre-dev/` are
`issue517-checkpoint.md`, `issue517-attempt2-validation/receipt.md`, and
`watchdog/third-attempts-20260912/517.{setup,worker}.log`. The third setup log
names `issue-517-independent-attempt3-20260912`; its worker log reports capacity
exhaustion with no reservation. No missing duration or usage is inferred.
The final dispatcher durations above supersede only the provisional elapsed
values in the attempt2 receipt, without overwriting that historical record.
MAIN owns this native continuation's rollout and completion accounting.
