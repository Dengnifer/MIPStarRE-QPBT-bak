---
title: Point consistency of the pulled-apart measurement
date: 2026-09-14
purpose: >
  Distinguish the proved conditional Alice estimate from the unconstructed
  source witness, record the repair of PR533 findings F1-F3, and retain prior costs.
issue: "#518"
pr: "#533"
status: source-construction-open
---

# Point consistency of the pulled-apart measurement

## Scope

This is the current-state audit of the repair based on PR533 head
`e371f2277c70aed116624161a1083fecc11b363d`. It covers the conditional interfaces
in `Extraction/Consistency.lean`, the shared `Extraction/Construction.lean`
source obligation and its QPBT re-export, the global-witness documentation,
Chapter 16 links, and the decoder gap note. The existing Alice proof and its
signature, apart from its conditional name, are preserved.

## Source of Truth

The primary source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`
(`lem:qld-4-7`) and `1463-1492` (`lem:qld-construct-the-paulis`). The former
constructs the global measurements; the latter uses those measurements for
the two point-consistency conclusions. Chapter 16 and
`docs/paper-gaps/qpbt_decoding-identity.tex` record the necessary restriction of
the decoder identity to encodings and the resulting error enlargement.

The shared source statement, module layout, and conditional names are adopted
from immutable PR539 commit `27f4c8110d0ff41fe834a8bb5b12bab72de44a33`, read with
`git show`. Its source theorem statement is preserved verbatim. Its unfinished
Alice proof and separately proved Bob component are not imported. The prose
about completed components is adapted to this branch. Review `5194177472` and
issue #518 were read through the primary `local/bin/gh_common.py` as data.
Audit format follows `audits/2026-04-29_audit-document-format.md`.

## Findings

F1 is repaired at the statement and attribution level. The proved theorem is
now `tildeM_consistent_pointMeas_ofGlobalPairWitness`; its explicit witness
premise remains visible, with an `**Unfaithful:**` marker and a named discharge
plan. The other two conditional interfaces use the shared names. The source
node links `exists_pulled_apart_consistency`, whose witness is an output and
whose constants precede all parameters and strategies. Its proof remains a
tracked obligation. Neither the source node nor the combined conditional node
has a completion marker. No paper theorem is claimed closed.

F2 is repaired by the YAML metadata and the six required sections of this
current-state audit. F3 is repaired by distinguishing current evidence from
the historical record below. In the current proof the mass bound comes from
`global_marginal_encoding_consistency` and
`right_mass_outside_encoding_le_evaluated_defect`, not from the unfinished
`nonencodingMarginalMass_le`. The Alice theorem and its defect comparison use
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
This axiom status proves the conditional implication; it does not provide an
inhabitant of the witness structure from the paper hypotheses.

### Statement Integrity

- Paper assumptions: an admissible projective strategy in the source setting,
  with error including zero; Lemma `qld-4-7` produces the global measurements.
- Conditional Lean assumptions: universal `C >= 1`, then `P`,
  `0 <= epsilon <= 1`, `deltaG >= 0`, `S : ProjectiveSetting P epsilon`, and
  explicitly supplied `w : GlobalPairWitness S deltaG`. The same quantifiers,
  hypotheses, and signature are retained under the conditional name.
- Paper conclusion: both point orientations and observable self-consistency
  for the same constructed measurements, at a universal enlarged error.
- Conditional Lean conclusion: Alice point versus Bob pulled-apart average
  consistency, with the original uniform point distribution, answer sum,
  register ordering, and `deltaConstructPaulis C epsilon deltaG m d q`.
- Conditional verdict: **extra assumptions** relative to the paper, namely
  the supplied global witness. Signature preservation is not source closure.
- Source-facing Lean assumptions: `P`, `0 <= epsilon <= 1`, and the projective
  strategy, with universal `a`, `b`, and `C` quantified before them. There is
  no witness input and no new bridge premise.
- Source-facing Lean conclusion: an output witness at `deltaQld a b ...`,
  both point estimates, and every observable estimate for that same witness.
  Verdict: **faithful boundary hypotheses**, with the explicitly documented
  decoder correction and error enlargement of the shared design. The proof
  remains open; its statement is not a completion certificate.

For `exists_globalPairWitness`, the paper assumes the source strategy setting
including zero error, while Lean assumes `epsilon > 0`. Both conclusions
assert projective global polynomial-pair measurements with both evaluated
consistency estimates and universal constants. The verdict is **extra
assumptions**, specifically a documented positive-error scope restriction;
even that restricted construction still has a proof hole. The structure
`GlobalPairWitness` records the conclusion data and is not an existence proof.

## Required Action

The remaining named obligations relevant to this repair are:

- `exists_globalPairWitness`: construct the global measurements and their
  consistency fields from the strategy. Its existing domain is `epsilon > 0`;
  the zero-error case required by the shared source theorem is still missing.
  The source-import dimension and tensor-code correspondence obligations in
  `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` remain open.
- `tildeM_consistent_pointMeas'_ofGlobalPairWitness`: the opposite orientation
  remains a direct `sorry` here, tracked by #47/#519. PR539's separate proof is
  future integration work, not part of this repair or its proof count.
- `tildeObs_selfConsistent_ofGlobalPairWitness`: the pulling-consistency and
  trace-postprocessing argument remains a direct `sorry`, tracked by #47.
- `marginalPoly_sub_pointMeas_approx_zero` and `nonencodingMarginalMass_le`:
  the two existing auxiliary obligations remain; neither is a dependency of
  the proved Alice theorem. Their existing source citations and tracking remain.
- `exists_pulled_apart_consistency`: the one new direct `sorry` is the narrowly
  scoped paper realignment shared with #519. Construct the witness, obtain
  all three conditional estimates for it, and take their common maximum.

Keep #518 open. The future publisher must replace the published PR body's
`Closes #518` and obsolete theorem name with a description of the conditional
repair and `Addresses #518`, then obtain fresh exact-head CI and independent
review before a merge gate. This session neither publishes nor resolves the
GitHub finding checkboxes. MAIN records the native rollout when terminal.

## Validation

The primary `worktree-setup.sh --no-build` and hook-installation check passed.
The clean starting head was rechecked against GitHub. All `opus-*` claims in
`watchdog/meta-dispatched.txt` were inspected; none claimed #518/PR533, and no
process had the assigned worktree as its working directory before mutation.

Focused `lake env lean` checks passed for `Combining/Witnesses.lean`,
`Combining/Apply.lean`, `Extraction/Consistency.lean`, and
`Extraction/Construction.lean`, with fresh branch-local artifacts. The warnings
are the retained proof holes and the one new source obligation. The QPBT
re-export also type-checks. The checkout actually pins Lean/Mathlib v4.32.0.
The three renamed statements and their proof bodies were compared with the
starting head: byte-identical apart from the names. The source theorem and its
`sorry` body were compared with immutable PR539: byte-identical.

The fresh axiom transcript `.lake/issue518-repair-axioms.log` verifies only
`propext`, `Classical.choice`, and `Quot.sound` for the Alice theorem, its
defect comparison, the global encoding-reference consistency estimate, and the
right non-encoding mass estimate. It separately verifies `sorryAx` for the
opposite orientation, observable self-consistency, global-witness constructor,
and joint source obligation. The four old direct holes in `Consistency.lean`
remain and `Construction.lean` contains exactly one new tracked source hole.
The proof-integrity scan finds no new axiom or bypass.

`blueprint_lean_sync.py --update-lean-decls` resolves the source links, including
the four new names; its 13 unrelated header-only completion warnings remain.
The generated declaration list is ignored by Git. `leanblueprint web` passes;
the log `.lake/issue518-repair-blueprint-web.log` retains bibliography warnings.
Whitespace checks pass, both extraction files satisfy the 100-character width
limit, and their lengths are 1000 and 71 lines respectively. Normal commit
hooks apply to this repair. No full build, CI, review, router dispatch, child,
lane tail, or publication is part of this continuation.

After the focused QPBT and root re-export checks, the existing declaration
checker was run through `lake env .lake/build/bin/checkdecls blueprint/lean_decls`
without invoking a build: all 1681 generated declarations resolved.

## Review Use

Review F1 against the source and conditional nodes separately. Verify the
unchanged Alice proof, the shared joint source statement, and the absence of
false completion markers. Review F2/F3 against this current-state section;
the historical status claims below describe earlier heads only. In particular,
their references to `sorryAx` and `nonencodingMarginalMass_le` are superseded.
The joint source obligation, global-witness constructor, and two unfinished
conditional components must not be counted as discharged by the Alice proof.

### Cumulative Issue 518 Costs

The primary session registry was reread without modification. All five prior
issue518 prover attempts, including independent worktrees, remain charged:

| Session suffix (20260912) | Recorded seconds | Input tokens | Cached input | Output tokens | Reasoning tokens |
| --- | ---: | ---: | ---: | ---: | ---: |
| 01, failed | 2532 | unknown | unknown | unknown | unknown |
| 02, failed | 59 | unknown | unknown | unknown | unknown |
| 03 | 4740 | 2414233 | 2211584 | 7790 | 1422 |
| 04 | 4985 | 3197631 | 3042944 | 9966 | 2088 |
| 05 | 2422 | 1511164 | 1312640 | 9868 | 2595 |

The sum of recorded session wall times is 14738 seconds, not elapsed calendar
time or measured active proof time; some attempts overlapped. Usage for the
failed sessions is unknown, not zero. Cached and reasoning columns retain the
registry's categories rather than being added to other token counts. The
prerequisite history below is also retained, without resetting any gap budget.
This owner-authorized native continuation has a separate 25-minute bound;
MAIN will add its actual rollout usage and time, without rewriting prior rows.

## Historical Record Through the Previous Head

The remainder is the preserved earlier audit. Its unqualified status claims,
old declaration names, and validation observations refer only to the historical
heads described there. They are superseded by the current-state audit above.

Issue #518; session `prover-518-20260912-01`; base
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

### Historical Mathematical Result

For a supplied global polynomial-pair witness with point-consistency error
`deltaG`, the theorem
`tildeM_consistencyDefect_le_deltaG_add_nonencoding` proves

\[
  \operatorname{Defect}(M_{\mathrm A},\widetilde M_{\mathrm B})
  \leq \delta_G + \nu_{\mathrm B,W},
\]

where `nu` is `nonencodingMarginalMass w .bob W`. This theorem does not use
the unproved estimate for that mass. Its axiom closure contains only
`propext`, `Classical.choice`, and `Quot.sound`.

The source is Item 1 of `lem:qld-construct-the-paulis`, specifically
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
The matching blueprint entry is in `ch16_qpbt_extraction.tex`. The correction
to the source's unrestricted decoder identity is already documented in
`docs/paper-gaps/qpbt_decoding-identity.tex` and is retained here.

For a fixed point `u`, expand the definition of the pulled-apart measurement
and regroup its factors on `A`, `BB'`, and `B''`. The convolution formula for
the expanded point measurement identifies the resulting overlap with

\[
  \sum_g \langle\widehat\psi,
    (\widehat S^W_g)_{\mathrm{BB}'}
    (\widehat M^W_{\operatorname{Dec}(g)\cdot\operatorname{ind}_m(u)})
      _{\mathrm{AB}''}\widehat\psi\rangle.
\]

For encoding outcomes, the decoded value equals `g(u)`. For every other
outcome, both overlaps are nonnegative, and the overlap at `g(u)` is at
most the marginal mass of that outcome, by completeness of the expanded
point measurement. Summing gives the loss `nu`. The given witness supplies
the evaluated overlap bound after averaging over `u`.

The auxiliary module `Extraction/PointConsistency.lean` proves the exact
operator identity, its consistency-defect formulation, and this pointwise
comparison. The existing marginal postprocessing lemmas complete the averaged
estimate in `Extraction/Consistency.lean`.

The body of `tildeM_consistent_pointMeas` now applies that estimate and the
existing theorem `nonencodingMarginalMass_le`. If the latter supplies constant
`C`, the target uses `C + 1`: with
`T = deltaG + sqrt epsilon + md/q`, one has `deltaG <= T` and hence
`deltaG + C*T <= (C+1)*T`.

### Historical Statement Integrity

- Paper assumptions: the projective setting and the global measurement
  supplied by `lem:qld-4-7`, with its point-consistency estimate.
- Lean assumptions: the original `AdmissibleParams`,
  `0 <= epsilon <= 1`, `0 <= deltaG`, `ProjectiveSetting P epsilon`, and
  supplied `GlobalPairWitness S deltaG`, for either `PauliKind`.
- Paper conclusion: average consistency of Alice's original point measurement
  with Bob's pulled-apart measurement, after absorbing errors into `deltaS`.
- Lean conclusion: the same register ordering and uniform point distribution,
  bounded by `deltaConstructPaulis C epsilon deltaG P.m P.d P.q` for a
  universal constant. All public quantifiers and the error definition are
  unchanged.
- Verdict: exact preservation of the assigned Lean statement and its existing
  explicit error contract. This is a conditional use of a supplied witness;
  it does not prove the source-facing construction of that witness. The
  non-encoding mass estimate remains an unproved prerequisite.

A byte comparison of the target signature against the base succeeds. No
other existing theorem, definition, or proof body is changed. No blueprint
completion marker is added: the combined source lemma is not certified by
this reduction.

### Historical Provenance and Prior Costs

The search covered all saved Git refs and the complete history of
`Extraction/Consistency.lean`. No completed proof of this target was found.
The reused `sum_marginalPoly_eval_mul` and
`marginalPoly_pointMeas_consistent_bob` originate in
`ba454653ecaa2d92821e9210b15e248c13b9c744` and its subsequent integration.
Their current implementations are reused through the local API.
The saved encoding-support construction at
`55ae74879dbf4452d04fb5c698e9f7636197dcf4` was also inspected; no divergent
branch was copied. The decoder algebra is reused from the current base.

The pre-session registry contains these related prerequisite efforts:

| Issue | External Sessions | Recorded Seconds | Recorded Output Tokens |
| --- | ---: | ---: | ---: |
| #243, marginal agreement | 4 | 4895 | 52393 |
| #245, register transport | 3 | 3432 | 62189 |
| #258, encoding support | 4 | 4972 | 68870 |
| #261, supported-mass comparison | 4 | 2669 | 68192 |
| Total | 15 | 15968 | 251644 |

Two additional historical native observations for #261 have unknown wall time
and usage; they are not counted as zero-cost sessions in the table. These
are prerequisite efforts, not fifteen prior attempts at this exact target.
The current session adds to this history; it does not reset any mathematical
gap budget. Its dispatcher records its actual time and token usage. Its
60-minute bound starts at `2026-09-12T05:00:49Z`. No subagent was launched.

### Historical Validation and Remaining Work

Focused compilation of both changed Lean files passes with Lean/Mathlib
v4.32.0, the versions actually pinned in this checkout. The new module has no
warnings; `Consistency.lean` reports only its four unchanged direct holes.
The proof-integrity scan finds no added hole, axiom, or bypass. Whitespace,
new-module line width, and the worktree hook-installation check pass.

Fresh branch-private artifacts were used for the axiom audit. The three main
auxiliary lemmas and `tildeM_consistencyDefect_le_deltaG_add_nonencoding`
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
`tildeM_consistent_pointMeas` additionally depends on `sorryAx` through
`nonencodingMarginalMass_le`, tracked by #517 and #47. The target's direct
hole is removed, but its axiom closure is not yet free of proof debt.

The four retained direct holes are `marginalPoly_sub_pointMeas_approx_zero`,
`nonencodingMarginalMass_le`, `tildeM_consistent_pointMeas'`, and
`tildeObs_selfConsistent`. Only the mass estimate is used by the target's new
proof. These declarations belong to other packets and are untouched.

Publication, exact-head local CI, and independent review are subsequent
workflow gates. This session does not launch a reviewer or merge the PR.
Issue #518 should remain open while #517 leaves the target's axiom closure
incomplete. The audit script is in the session's private checks directory
under `~/.cache/mipstarre-dev/sessions/`.

### Historical First Published CI Run

PR #533 first tested `16ddc770ad0ed4511d1e63bea6a3d661997aec6a`.
The full build passed. Build-mode linting reported a flexible-tactic warning
in the new register calculation; the subsequent correction makes the same
simplification close its goal. The original file's `open scoped Classical`
warning predates this packet.

The blueprint-sync gate failed in the isolated model-policy dispatch fixture:
the invoking session's `MIPSTARRE_HARDNESS_REASON` was inherited by a routine
dispatch test. The model variables had been unset, but this associated
classification setting had not. The corrected invocation also unsets
`MIPSTARRE_JOB_CLASS` and `MIPSTARRE_HARDNESS_REASON`; no workflow code or
model policy is changed. The failed exact-head evidence remains on GitHub.
The isolated fixture passes with that environment, and the corrected auxiliary
module passes a focused check with `linter.mathlibStandardSet=true`.

### Historical Failover Continuation

Session `prover-518-20260912-03` continues the same assignment. The first
session ended at 05:43:01Z after exhausted HTTP 503 retries; its dispatcher
records 2532 seconds, failure, and unknown token usage. These observations
remain unchanged and are not treated as zero cost. The separate failed
session `prover-518-20260912-02` records another 59 seconds and unknown usage
in the independent-attempt worktree. No descendant is launched here.

The continuation found new mathematical evidence in saved PR #543, commit
`e36fd1aa056782007917b0d6c5e19b85ea28179b`: the encoding-supported reference
comparison and non-encoding mass estimate have proofs without `sorryAx`.
Five necessary modules are recovered byte-for-byte from that commit:
`PairStateConsistencyTransport`, `PolynomialCollision`, `SupportMass`,
`DistanceTheorems.TensorConsistency`, and `NonencodingSupport`. Their earlier
provenance is retained in their documentation and in the #517 audit at that
commit. The encoding measurement and tensor API are already present in the
current base, so no replacement of those files is needed. The corresponding
Alice-side application in commit `6521816f` concerns issue #519 and is not
the target of this packet.

The target now uses the Bob-side reference estimate directly. It bounds the
non-encoding mass by `deltaG + C * sqrt epsilon + md/q`, adds the witness
error using the previously proved defect comparison, and absorbs the result
in `deltaConstructPaulis (C + 1)`. The separately owned declaration
`nonencodingMarginalMass_le` is unchanged and is no longer a dependency of
the target. The original signature, error definition, uniform distribution,
and player ordering remain unchanged. The statement-integrity verdict is
exact preservation of the assigned conditional theorem; construction of the
supplied global witness remains outside this result. No blueprint completion
marker is added for the other assertions of the source lemma.

Focused compilation of all five recovered modules and `Consistency.lean`
passes. A fresh artifact audit reports exactly `propext`, `Classical.choice`,
and `Quot.sound` for `tildeM_consistent_pointMeas` and its defect comparison.
The four unrelated direct holes remain unchanged. The signature matches the
assigned base byte-for-byte; the hook-installation check, whitespace check,
and recovered-module proof-integrity scan pass.

The cumulative active-work limit requires a publication checkpoint: fresh
exact-head full CI and independent review remain the next gates. Earlier
green CI at `3d412206` is historical evidence, not validation of this change.
