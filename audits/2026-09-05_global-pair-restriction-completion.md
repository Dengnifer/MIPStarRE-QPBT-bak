# Global polynomial-pair restriction and completion

## Scope

Issue #119 concerns the passage from extended low-degree measurements to the
global polynomial-pair measurement in `lem:qld-4-7`. This packet proves the
algebraic restriction and projective completion on a fixed measurement space.
It does not prove the quantitative existence theorem. The construction uses
`eq:qld-sgg-completeness` and the final completion paragraph of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`, lines
1375–1380 and 1402–1404. The three scalar claims and their corrected error
remain unchanged from inherited commit `691b671`.

## Prerequisite integration

Merge `25f4d28` incorporates local main, including PR153 (`22a4268`), into
the issue branch. Both parent histories, including their telemetry, remain
reachable. Conflict inspection compared the two tips and the conflicted
three-way merge, whose synthesized base included earlier merge resolutions.

| Conflict | Classification and resolution |
| --- | --- |
| `Combining/Apply.lean` | Documentation: retain main's distinction between directly indexed obligations and source statements, and retain the inherited existential assembly proofs. |
| `Transport/Correspondence.lean` | Documentation around the answer equivalence: retain main's constructor-preserving description and unchanged public equivalence. |
| `Transport/Questions.lean` | Upstream terminology/API rename from mature-LDT names to LDT names, including `ldtDiagonalLineOf`; preserve main's complete version. The revision is present in upstream review repair `834dc01`. |
| `Transport/SeedFiber.lean` | Upstream relocation of norm lemmas to the state infrastructure, recorded in `e8e8048`; remove the duplicate local declarations by retaining main's version. |
| `Games/CondLinear.lean` | Documentation citations: retain main's citations and definitions. |
| `Games/CondLinearTheorems.lean` | Documentation citations: retain main's text and its upstream public API. |
| `ch13_qpbt_test.tex` | Upstream separation of typed-family and distribution-equality support statements: retain main's mathematical content and completion status. |
| `qpbt-gap-register.md` | Retain main's updated linearity and Magic Square entries and the inherited subline-claims entry outside the conflicting region. |

After resolution, the transport/game directories and chapter 13 have no diff
against the merged main. `Claims.lean` and
`qpbt_subline-claims-line-marginal.tex` have no diff against `691b671`.
No game definition or theorem hypothesis was redesigned.

## Mathematical construction

Write `c(f,g) = alpha f(x) + beta g(z)`. Algebraic substitution with
`(alpha,beta) = (1,0)` and the unused block zero recovers `f`; the opposite
substitution recovers `g`. These are substitutions into a polynomial ring,
not an appeal to equality of polynomial functions on a finite field. Hence
`c` is injective without a degree-versus-field-size restriction.

The existing degree lemma embeds bounded pairs into bounded extended
polynomials. For any extended-polynomial POVM `T`, restricting its effects
along this embedding produces a submeasurement `R`. Its missing operator is
exactly the sum of the effects indexed outside the image. If `T` is
projective, each retained effect is projective.

Fix an arbitrary pair `p0`. `Function.extend` supplies a relabeling that
inverts the embedding on its range and sends all other outcomes to `p0`.
Postprocessing `T` by this map is a complete measurement. The proved effect
formula identifies it with `R` plus the missing operator at `p0`, and
projectivity follows from the existing projective-postprocessing theorem.
The specified pair is solely a completion outcome; it does not replace any
measurement or consistency obligation by a default witness.

## Statement-integrity audit

- Paper assumptions for this local construction: bounded polynomial outcomes,
  a projective extended-polynomial measurement, and an arbitrary completion
  pair. The surrounding admissible domain has degree at least one.
- Lean assumptions: the same admissible parameters and measurement, with
  finite matrix-carrier and decidable-equality instances. The injectivity
  lemma is proved more generally over a commutative semiring.
- Paper conclusion for this local construction: restriction is a projective
  submeasurement; its missing operator is the sum of noncombined effects;
  adding that operator at one outcome gives a projective measurement.
- Lean conclusion: exactly these operator identities and projectivity facts.
- Verdict: faithful boundary hypotheses for the measurement construction;
  the purely algebraic injectivity lemma is more general. The public
  statement of `exists_globalPairWitness` is unchanged.

The new blueprint support node states only these qualitative facts. The
source-labelled global-pair theorem remains `notready`; no quantitative
claim is certified by the support node.

## Proof debt and validation boundary

The three direct holes in `Apply.lean` remain:

1. `exists_extendedLinesWitness_ofPointsWitness`: the line construction with
   the printed estimate, documented in
   `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
2. `exists_extendedLinesWitness_established_ofPointsWitness`: the independent
   #118 combined-line construction, with the established auxiliary estimate
   and the same gap note. This packet does not duplicate that work.
3. `exists_globalPairWitness`: construct the extended-game strategy, derive
   the noncombined-outcome mass bound `eq:qld-g-non-separable`, transfer
   consistency to the completed pair measurement, and absorb the errors.
   The direct-game/soundness discrepancy is recorded in
   `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. PR153 supplies
   transport estimates, not these remaining measurement constructions.

The existential line assemblies still depend on `sorryAx`. The new exact
restriction/completion results do not discharge any of the above holes.
No pasting theorem or #201 file is modified.

Initial axiom inspection found that the cached `combinePoly_mem_polyFunc`
still contained `sorryAx` despite its completed inherited source proof.
Focused recompilation of `Combining/Defs.lean` into this worktree's own
`.lake/build` removed that stale dependency. Subsequent kernel axiom checks
for the missing-operator identity, completion effect formula, and completion
projectivity list only `propext`, `Classical.choice`, and `Quot.sound`.
No hot-cache file was written and no full project build was run.

The focused check of `Apply.lean` succeeds, reporting only its three retained
direct holes. `Claims.lean` contains no `sorry` or `axiom` tokens, but its
focused check cannot yet complete with this worktree's inherited cache:
`OrderedPoints.olean` was initially absent. After compiling that module, the
next dependency, `Points/Placement.lean`, reports unknown
`aaBaBipartition`, `reindexOp_aaBaBipartition_left`, and related transport
declarations. Their source declarations are present in `ExpandedPlacement`
and `WinImplications`, but the imported objects are from the older main
snapshot. No inherited source was rewritten to compensate for this cache
mismatch. A source-aligned upstream dependency build is still required
before reporting a successful check of the preserved claims.

`leanblueprint web` exits successfully, with missing-bibliography warnings.
The LaTeX convention check passes. The repository-wide blueprint/Lean sync
checker still reports 231 issues, including the stale `blueprint/lean_decls`
inventory; it is not reported as green. The new support node has valid Lean
source references and no orphan completion tags. The declaration inventory
is outside this packet's assigned write scope.
