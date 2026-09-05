# Issue 118 integration baseline

Session `orc-118-20260906-02`, September 6, 2026 (local date).

## Pinned prerequisites before integration

The GitHub API, accessed through `local/bin/gh_common.py`, reports:

- Issue 201: `7d0af711c5c6769151e41cf091288855fdb409b0`.
- Issue 117: `6b4b75d408be5399a1867166bffcc3aa56de6e4b`.
- Initial issue 118 head: `691b67159f9ead45b9de144df3bd46e015430e70`.

Both prerequisite objects are already present locally. PR 205 remains open
at the issue 201 SHA; its ongoing corrections are not part of this session.
The inherited audit, obstruction brief, and dirty telemetry are preserved in
the diagnostic commit before any merge. The mathematical handoff remains
`audits/2026-09-06-issue118-point-error-dependency.md`; this integration does
not repeat or supersede that audit.

The existing hook configuration points to the primary checkout's guarded
hooks. Branch-local hook restoration must retain the incoming merge-loss
guard, not downgrade to the old two-hook layout. No hook bypass, full build,
push, PR merge, or independent review is authorized by this integration.

## Completed history reconciliation

- `ba43c81ccee4` preserves all three inherited dirty paths and this SHA record.
- `9ca86675acbfb553da359e5d2a9127e727db9fa2` merges
  `516758b8fe4bba2fd06669c2325aa65132a0ab84`, the common ancestor of the
  pinned issue 201 tip and the locally recorded GitHub main. This is the
  committed main-history prerequisite containing the merge-loss guard.
- `425bf138b4726aa4e490aa8880dd4e413af50c83` merges the pinned issue 201 tip.
- The pinned issue 117 tip was already an ancestor of the initial issue 118
  head. Its `Points.lean` and `Points/` implementation remain identical to
  that prerequisite; no redundant merge or sibling-branch change was needed.

The main-history merge is separate because a direct side-branch merge would
stage 2,398 workflow-layer lines against a 1,000-line gate. Applying the
documented main-history exemption to the actual main ancestor leaves only
the branch's own workflow changes budgeted. The subsequent issue 201 merge
adds 256 lines of inherited briefs and passes the ordinary side-branch gate.
No budget override, hook skip, reference substitution, or history rewrite was
used. Both merge commits pass the pending-index and reference-transaction
merge-loss guards. The main-history commit also passes all 485 script tests.

`core.hooksPath` now points to this worktree's `.githooks`, using worktree-only
configuration. The complete incoming hook layout, including
`reference-transaction` and its merge-loss checker, passes
`scripts/install_git_hooks.sh --check`. Shared configuration is unchanged.

## Resolution record

The recursive main-history merge had nine real conflicted paths, rather than
the larger provisional conflict list printed while Git constructed its four
merge bases. Conditional-linearity and transport conflicts retain the
incoming documentation, public level-monotonicity lemma, and existing
mathematical implementations. The duplicate coordinate norm lemmas are
removed from `Transport/SeedFiber.lean` because the incoming history places
them in `State.lean`. Chapter 13 retains the incoming typed-family nodes.
Telemetry retains both appended histories, and the gap register retains the
issue 118 claims row together with the incoming rows.

`Apply.lean` and `Lines.lean` combine incoming error-contract and
source/auxiliary documentation with the current proofs and imports, rather
than replacing those proofs with the incoming placeholders. The subsequent
issue 201 merge has only one conflict, in the `Lines.lean` docstring.

After comment removal and whitespace normalization, `Lines.lean`,
`Apply.lean`, and `Witnesses.lean` have exactly the initial Lean tokens.
`Claims.lean` and `Points.lean` are byte-identical to the initial head.
In particular, `subline_remove_X_factor` and `subline_Z_term_near_one`
(claims 17-2 and 17-3) retain their statements and proofs. The imported
`IsPolyErr₂` change is exactly issue 201's additive error contract, not a new
choice by this session.

The incoming-only files `DirectLowDegree/SeedIndexedSoundness.lean`,
`DirectLowDegree/Transport/PointAgreement.lean`, and
`DirectLowDegree/Transport/Simultaneous.lean` are byte-identical to the pinned
issue 201 versions. Their re-export imports are retained.

### Downstream tensor-lemma name reconciliation

Fresh-artifact validation exposed one API conflict not reported by Git:
`WinImplications.msVarObsA_anticommutator_le` still referenced
`MagicSquareRigidity.heteroKron_add_left`. Issue 201 moves this lemma from
`Rigidity/GroundSlice.lean` to the shared `Games/Defs.lean` namespace. The
consumer now uses that shared declaration. A search for the other removed
qualified names found the analogous use of
`MagicSquareRigidity.heteroKron_sub_right` in
`ProjectiveSetting.exists_twistedCommutator_avg_le`; it likewise uses the
shared declaration. These are two identifier-only proof changes. They do not
restore the duplicate lemmas or modify PR 205's implementation.

The next fresh check found the exact duplicate declaration
`MIPStarRE.QPBT.phaseSign_mul_self` in `ExpandedCommutation.lean` and the
incoming `Algebra/Pauli.lean`. Both have the identical statement
`phaseSign t * phaseSign t = 1` for `t : ZMod 2`. The downstream duplicate
is removed, retaining the canonical algebra declaration and all its callers.
This is the binary eigenvalue identity in paper chapter 4, lines 1052--1096;
there is no conflicting mathematical statement to adjudicate.

Two further duplicate public declarations are likewise supplied by the
incoming `Games/DistanceTheorems/Support.lean`: `DistanceCalculus.stateQForm_finset_sum`
and `DistanceCalculus.stateQForm_nonneg`. Their copies in
`Observables/LineMeasurement/LinePointOverlap.lean` and
`Combining/Lines/ConsistencyPositivity.lean` are removed. The sum identity
has the same state, finite set, operator family, and equality, up to the
implicit index-type binder's name and position; the positivity lemma has
exactly the same hypotheses and conclusion. All callers and blueprint names
continue to refer to the retained shared declarations. These are algebraic
integration repairs, not new proof assumptions or discarded source results.

Statement integrity for these two repairs: the first helper still assumes a
Magic Square strategy with success at least `1 - ε` and `0 ≤ ε`, and concludes
the same squared anticommutator bound `1183680 * ε`. The second still assumes
`ProjectiveSetting P ε` with `0 ≤ ε`, on either player side, and concludes the
same averaged twisted-commutator bound with universal constant times `sqrt ε`.
The cited source is `eq:pts-obs-commutation` and its Magic Square argument in
paper chapter 14, lines 309--362. Verdict: the existing supporting estimates,
their assumptions, and their conclusions are unchanged; only the names of
the tensor identities used in their proofs are reconciled.

The repairs are committed as `57332c393bf345208117d05eb1dbfe878f4e8bcd`,
with the normal statement-integrity and proof-debt gates passing.

## Final validation

The initial `lake env lean` checks of `Lines.lean`, `Claims.lean`, and
`Apply.lean` passed against the pre-existing cache. They were followed by
fresh-artifact validation, rather than treated as sufficient evidence for
the integrated dependencies.

A private copy of the worktree's compiled library under
`/tmp/issue118-lean-validation/lib` supplies unchanged cached dependencies.
Changed and missing modules in the selected dependency closure, and their
affected consumers through points, lines, claims, and Apply, are recompiled
sequentially with the worktree's Lean executable and `-o` targeting only that
private library. There are 225 distinct successful module checks after the
repairs above. Initial attempts with the removed tensor-lemma name and the
two duplicate declarations failed, and their failures remain in `run.log`;
the corresponding per-module logs record the successful rechecks. The
initial empty-overlay lookup failure was resolved by copying the unchanged
library, since Lean resolves the module prefix to the first matching root.

- `Points.lean`, `Lines.lean`, `Claims.lean`, `Apply.lean`, `Sandwich.lean`,
  and all three protected incoming-only transport files pass with the fresh
  dependency artifacts.
- Fresh QPBT and project-root import checks pass with no diagnostics. These
  are import checks, not a full project build.
- Running `scripts/Checkdecls.lean` with `lean --run` against those fresh
  imports resolves all 1,786 declarations in `blueprint/lean_decls`, without
  invoking a Lake executable build.
- Axiom inspection of `exists_pasting_error`,
  `exists_combinedPointsWitness`, `subline_remove_X_factor`, and
  `subline_Z_term_near_one` finds only `propext`, `Classical.choice`, and
  `Quot.sound`. In particular, none depends on `sorryAx`.
- `exists_combinedLinesWitness` still depends on `sorryAx`, through the
  existing line-construction obligation. The direct scan finds the same
  one hole in `Lines.lean` and three in `Apply.lean`, and none in the four
  integration-repaired files, `Points.lean`, `Claims.lean`, or the pasting
  implementation files.
- `check_source_statement_changes.py` reports no changed source-labelled
  public headers for either the combining interfaces or the repaired files.
  The claims and point construction remain byte-identical to the initial
  head; the three protected incoming-only files remain byte-identical to the
  pinned issue 201 tip. Both merge-loss guards pass on the committed merges.
- `leanblueprint web` exits zero. It reports the two already-unresolved
  labels `lem:qld-sublines-restricted-blocks` and
  `lem:qld-sublines-seed-blocks`, whose uses and absent definitions also occur
  at the initial head. It also reports bibliography warnings because
  `web.bbl` is unavailable. These are not new integration failures and are
  not repaired here. The hook's blueprint convention check passes.

The default `.lake` products, the hot main cache, and sibling caches are not
rewritten. While the temporary validation library remains available, the
next mathfix can reuse the fresh dependencies for a targeted check with:

```sh
LEAN_PATH="/tmp/issue118-lean-validation/lib:$(lake env printenv LEAN_PATH)" \
  "$(lake env which lean)" MIPStarRE/QPBT/Combining/Lines.lean
```

The run log, per-module logs, axiom report, and import/declaration-check logs
are under `/tmp/issue118-lean-validation/`; the blueprint log is
`/tmp/issue118-blueprint-web.log`. These temporary artifacts are not committed
runtime state. No full build, subagent, independent review, push, PR merge,
or modification of a sibling branch was performed.

## Remaining point-to-line obligations

These are the earlier mathematical audit's handoff, not a new audit or a
claim that the unrestricted helper has a counterexample.

1. Replace the unsupported quantitative interface of
   `exists_combinedLinesWitness_ofPointsWitness` by an internal construction
   retaining the supplied point error `δQ`. Its current output bound is
   independent of that unrestricted input.
2. Derive both marginal comparisons corresponding to `eq:pasting-q1` and
   the required self-consistency estimate from the actual fields
   `CombinedPointsWitness.self_consistent`, `consistent_XZ`, and
   `consistent_ZX`, with their quantitative dependence intact. Instantiate
   `HasConditionalCollisionBound` with the line-evaluation collision bound
   `md/q`, and check all projectivity and probability hypotheses of the
   one-sided `exists_pasting_error`.
3. Construct the paired-line measurements, including all opposite-placement
   consistency fields and the axis-degree condition of `CombinedLinesWitness`.
   Specialize the internal estimate to the constructed points supplied by
   `exists_combinedPointsWitness`, whose chosen error is `K * ε^(1/8)`.
   Preserve the public statement of `exists_combinedLinesWitness`; do not add
   an assumed point-error bound or an unproved marginal identity to it.
4. Adapt the conditional extended-line consumers in `Apply.lean` without
   erasing the point-error dependence. The established extended-line estimate,
   the stronger printed estimate, and transport from the directly indexed,
   completed-answer game to the source game remain separate obligations.
   `exists_globalPairWitness` remains the downstream construction obligation.

The two `_ofPointsWitness` extended-line constructors and
`exists_globalPairWitness` retain their existing direct proof holes; the
line helper retains its one existing hole. No new hole or mathematical
assumption is introduced by the resolutions. PR 205's ongoing corrections
remain with that PR; this baseline includes only its pinned committed head.
