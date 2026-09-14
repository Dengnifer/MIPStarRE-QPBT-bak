# Issue 520: continuation of the saved third attempt

## Admission and predecessors

This is a continuation of `prover-520-20260912-03`, not an independent retry.
Admission was recorded at 2026-09-14 06:16:33Z, with a 25-minute limit ending
at 06:41:33Z. The owner assigned the existing worktree
`.worktrees/issue-520-independent-attempt3-20260912`, initially clean at
`c2176cc3dc2c0a6fa467122f3a983c4178dd5f36`.

The predecessor receipt is
`/home/drx/.cache/mipstarre-dev/sessions/prover-520-20260912-03.last.md`.
The predecessor audit is
[`2026-09-12-issue-520-character-consistency.md`](2026-09-12-issue-520-character-consistency.md).
The first two attempts retain their recorded 2679 and 43 wall seconds,
totaling 2722 seconds. The third attempt previously checkpointed near 25
minutes; that approximate duration is not replaced by an invented exact
number. All continuation costs are additional. Token totals remain for MAIN
to record from the native rollout; unknown predecessor totals are not zero.

Primary `worktree-setup.sh --no-build` and the hook installation check passed.
The setup preserved the populated private build directory. GitHub reads used
the primary `gh_common.py`. Live issue #520 was open without assignees or
comments; no open `opus-fix` claims were returned. Issue #517 remained open
and its delegate worktree was not inspected or edited. Issue #516 was closed
in favor of #393 / PR #399. PR #399 and PR #539 retained the heads below.
No router dispatch, child, CI, review, full build, lane operation, publication,
primary edit, or credential/configuration change was performed.

## Verified published support

PR #399 at `80493b09cf559a4d24ef6b74c6b54d9ec1179567` contains
`marginalPoly_sub_pointMeas_approx_zero`. Its exact prerequisite section was
checked independently in the ignored `.lake/Issue520PR399.lean`, ending with
an axiom inspection. The result uses only `propext`, `Classical.choice`, and
`Quot.sound`. It is verified available support, not a missing theorem.
The duplicate #516 closure also records an independent earlier check.
No divergent branch or absorption proof was copied into the production tree.

The following necessary support was preserved from PR #539 at
`ca866da402947c9ee7e1dd5e935a2782fe0d1602`:

- `PolynomialCollision.lean` is the complete published 71-line module.
- `PointConsistency.lean` contains only the initial placement/convolution
  section, through `pointMeasExp_effect_eq_sum_sub`.
- `PointConsistencyPrime.lean` contains only its initial placement section.

The latter two are prefixes of the published modules with their enclosing
sections closed. Their quantitative decoder/mass arguments were not copied.
The existing `PlacementSupport.lean` source has the same blob as PR #539.
The copied lemmas were checked against this checkpoint's dependencies.

PR #539's source-alignment commit is
`27f4c8110d0ff41fe834a8bb5b12bab72de44a33`. Its conditional target is
`tildeObs_selfConsistent_ofGlobalPairWitness`; its separate source-facing
`Construction.lean` obligation is `exists_pulled_apart_consistency`.
Neither source interface was edited or replaced here. The saved checkpoint
still has the older name `tildeObs_selfConsistent`, with its original hole.
The published conditional name and **Unfaithful:** marker must be retained
when integrating this support into that newer interface; the separate source
construction, including its zero-error case, remains unproved.

## Mathematical progress

The source read first was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1476-1662`,
especially `eq:qld-pulling-cons` and the transition to `eq:qld-pulling-12`.
The corresponding blueprint is `lem:qld-construct-the-paulis`, Item 2.
The decoder restriction was checked against
`docs/paper-gaps/qpbt_decoding-identity.tex`.

For an outcome `(g,h)`, put `p = g - g_h`, where `g_h` is the existing
bounded multilinear encoding. The new `pullingMeas` measures the polynomial
marginal and the last ideal Pauli register, then returns `p`. The measurement
is projective, and

    Dec(p) = Dec(g) - h.

Thus equal difference polynomials have the same decoded scalar label for
every register vector. Postprocessing `pullingMeas` by
`p -> Dec(p) . u` recovers `tildeM` exactly. This uses decoder linearity and
`Dec(g_h) = h`, not the false reverse identity for arbitrary `g`.

Let E be the consistency defect of Alice's and Bob's `pullingMeas`, each
postprocessed by polynomial evaluation at a uniformly random field point.
The proved collision and postprocessing comparison is

    uniform field-measurement defect of tildeM <= E + m*d/q.

It specializes the existing codeword-collision calculus using the published
Schwartz--Zippel bound; the coefficient of `m*d/q` is one. Composing with the
saved character conversion proves, for each fixed basis coordinate j,

    uniform observable squared distance <= 4 * (E + m*d/q).

Both displays are actual six-register expressions using `S.psiHat` and
`S.placeSide`, not hypothetical bounds supplied as arguments.

The evaluated difference-measurement effect is exactly

    sum_g S_g tensor tau_{g(u)-a}(ind(u)).

The new overlap identities for both player orderings therefore give the
witness's expanded-point overlaps without a decoder correction. In
`PullingDefect.lean`, both quantitative consequences are proved:

    Cons(pullingMeas_A evaluated at u, original point_B) <= deltaG,
    Cons(original point_A, pullingMeas_B evaluated at u) <= deltaG.

These use the original `AA'`--`BA''` and `BB'`--`AB''` placements and uniform
field-point average. They do not require the issue #517 mass bound.

## Remaining comparison

Observable self-consistency is not closed. It remains to combine the two
proved point comparisons with point self-consistency on the same six-register
state, using agreement and squared-distance triangle inequalities. Applying
agreement to the resulting projective evaluated measurements will bound E.
The final arithmetic must absorb this bound and `m*d/q` into the unchanged
`deltaConstructPaulis` scale. In particular, one should use the squared-distance
triangle route to retain linear dependence on `deltaG`, rather than introduce
a square root of that witness error. No unproved comparison was added as a
hypothesis, and no new unfinished dependency was substituted for the target.

The longer source derivation through complement absorption also remains
available; its absorption prerequisite is verified at PR #399 as above.
There is no claim of mathematical non-derivability here. The remaining work
is a quantitative formal comparison, separate from the source's construction
of the global witness.

## Statement integrity

Paper assumptions: a passing projective strategy and the global measurements
constructed in `lem:qld-4-7`, with the source's absorbed construction error.
Lean target assumptions: admissible P, epsilon in [0,1], nonnegative deltaG,
`ProjectiveSetting P epsilon`, a supplied `GlobalPairWitness S deltaG`, W,
and the fixed coordinate `j : Fin P.model.basisDim`.
Paper conclusion: self-consistency uniformly over the full Pauli register.
Lean target conclusion: the same squared observable distance bounded by
`deltaConstructPaulis C epsilon deltaG P.m P.d P.q`, with one universal C
preceding the strategy and parameter quantifiers.

Verdict: target signature, constant quantifiers, uniform law, coordinate, and
placements are unchanged. The supplied witness remains an extra conditional
premise relative to the source construction; this continuation does not
discharge it. The new auxiliary comparisons have no additional hypotheses
on that witness and are not advertised as the source theorem. No blueprint
entry was marked proved and no new proof hole or axiom was introduced.

## Validation

Focused Lean checks passed for the copied support, the three new pulling
modules, and the updated `MIPStarRE/QPBT.lean` re-export. The stale checkpoint
`DistanceTheorems.olean` lacked the existing
`tensorMeasurement` declaration; a focused recompile of that source restored
`EncodingSupport` without source edits or a full build.

Fresh axiom checks cover projectivity, exact decoded postprocessing, the
collision comparison, the evaluated convolution, both overlap identities,
the observable reduction, and both point-consistency bounds. Each uses only
`propext`, `Classical.choice`, and `Quot.sound`. The inherited observable
target still uses `sorryAx` and is not reported as proved. The diagnostic
checks are reproducible from `.lake/Issue520Axioms.lean`; no diagnostic
commands occur in production modules. All new production files are below
the 1000-line limit. The final receipt records the commit/hook outcome and
continuation end time.
