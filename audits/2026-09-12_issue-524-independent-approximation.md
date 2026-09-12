# Issue 524: independent approximation theorem

Session `prover-524-20260912-02` starts from pinned main
`230e7fdd30cf8aff509a4fa8c8137a12c970d638` on
`issue-524-independent-attempt2-20260912`. It proves approximation on nonempty
answer alphabets. It does not attempt the false unrestricted target or repeat
the empty-answer counterexample of the first attempt.

## Result and source

For a symmetric game `G` with a nonempty answer alphabet, the new declaration
`MIPStarRE.QPBT.exists_symmetric_projective_strategy_approx` proves

```lean
∀ δ : ℝ, 0 < δ → ∃ S : SymmetricStrategy G,
  S.toStrategy.IsProjective ∧ G.toGame.value - δ < S.toStrategy.value
```

The strategy's finite coordinate type is part of `S`, so its dimension may
depend on `δ`. The strict-bound theorem
`exists_symmetric_projective_strategy_of_lt_value` also supplies a symmetric
projective strategy above any specified strict lower bound on the game value.

The source is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`:
`def:tensor-product-value` at lines 40-57, `lem:symmetric-strat` at 94-99,
and its proof at 101-130. The proof begins by choosing a strategy for each
strictly larger error and preserves its value through dilation and
symmetrization. It supplies no optimal finite-dimensional strategy.

The two generic helpers live in `Games/StrategyApproximation.lean`, imported
by `StrategyClasses.lean`. An explicit unit state on singleton local spaces
and distinguished-answer measurements establish nonemptiness of the strategy
type. This deterministic strategy is used only for nonemptiness. Mathlib's
`exists_lt_of_lt_csSup` then extracts a strategy above a strict lower bound
from the actual `Game.value` definition. Finally the existing given-strategy
construction preserves its value. No proposed compactness, uniform dimension
bound, or attainment hypothesis is introduced.

The separate blueprint node `lem:symmetric-strat-approximate` states exactly
the nonempty-domain approximation theorem and carries statement and proof
completion tags. The original `lem:symmetric-strat` node, public Lean
signature, proof hole, and unfaithfulness marker are preserved.

## Reuse and prior attempts

The all-ref history search covered local main, saved branch refs and remote
refs. It found no completed exact-attainment proof or existing approximation
declaration. The reused given-strategy construction was introduced by
`7c4145458d506bb03fa0311840cbb85df70bf6f9`; review commit
`ca4ac693b6ae98e420f7e6600517bacec7efe8d3` explicitly retained the attainment
obligation. The target file on current local main matched the pinned version
when inspected. No divergent branch was copied.

The immutable first-attempt checkpoint is commit
`f2f30dc0dbff1fa5dab63e55f48dc2a19b55f1eb`, PR #540, especially
`audits/2026-09-12_issue-524-symmetrization-obstruction.md` and the dispatcher
receipt `prover-524-20260912-01.last.md`. They were read without modifying
that worktree. Its empty-answer result establishes a separate obstruction;
it is not a nonattainment example for a nonempty answer alphabet.

Costs remain cumulative, with scopes distinguished:

- The first checkpoint records issue-98 prover work of 10,019 session-wall
  seconds and PR-158 review work of 5,031 seconds, totaling 15,050 seconds.
  Those sessions include other strategy-transformation results. Their final
  resumed-thread token observation is 70,606,980 input, 68,905,856 cached
  input, 260,735 output, and 111,167 separately reported reasoning tokens;
  earlier cumulative observations on that thread must not be added again.
- The completed first issue-524 attempt now has a dispatcher record:
  2026-09-12 05:31:24Z to 05:45:49Z, 865 seconds; 3,380,024 input tokens,
  including 3,227,008 cached input, 14,446 output, and 3,736 separately
  reported reasoning tokens. The directly linked historical session-wall
  total before this attempt is therefore 15,915 seconds. Token categories
  are not added together; cached input is a subset of input.
- The broader issue-173 paper-gap work remains separate: at least 2,939
  session-wall seconds, covering multiple gaps, as recorded by the first
  checkpoint. It is not wholly attributable to issue #524.
- This independent attempt started at 05:58:04Z with a 60-active-minute cap.
  Its own completed duration and usage belong to dispatcher record
  `prover-524-20260912-02`, not to the first attempt. At this pre-publication
  checkpoint they are pending, not zero. Earlier costs are not reset.

## Validation and statement audit

Focused checking of both Lean files succeeds. The only warning in
`StrategyClasses.lean` is its existing target proof hole. All four new
declarations, as well as the reused
`exists_symmetric_projective_strategy_of_strategy`, have axiom closure
`propext`, `Classical.choice`, and `Quot.sound` only. The original target
still depends on `sorryAx`. The checks compiled the changed modules before
importing them for the axiom inspection.

`leanblueprint web`, declaration-list synchronization, the hook installation
check, and `git diff --check` succeeded. The standalone web pass reported a
missing generated bibliography; the full CI render regenerates that file.
Full-build and publication evidence must be read from the PR's exact-head
CI statuses, not inferred from these focused checks.

| Component | Paper-facing target | This change |
| --- | --- | --- |
| Assumptions | Symmetric game, nonnegative error, value equal to one minus error | Preserved verbatim |
| Conclusion | One symmetric projective strategy at least at that value | Preserved verbatim, still unproved |
| Auxiliary domain | The proof implicitly needs an inhabited strategy class | Explicit nonempty answer alphabet; strategy existence is constructed |
| Auxiliary conclusion | The proof uses each strictly larger error separately | For every positive tolerance, a finite strategy above value minus tolerance |

Verdict: no source-statement change. The independently proved auxiliary is
exact against its new blueprint node and faithfully expresses the source's
approximation argument on its explicitly stated nonempty domain. It is not
advertised as the printed attainment theorem.

The remaining mathematical prerequisites are the separately reviewed domain
correction from PR #540 and a justified resolution of finite-dimensional
attainment. These proofs supply no such resolution: exchanging
`∀ δ > 0, ∃ S` with `∃ S, ∀ δ > 0` is not justified. The next workflow gate
is exact-head CI followed by independent review, dispatched by the owner.
This session neither launches a reviewer nor merges the PR.
