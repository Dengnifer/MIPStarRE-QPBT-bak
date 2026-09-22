# Tensor-code import: construction and remaining obligations

Session `prover-704-20260922-01`, assigned base
`429de7f0fa6ca621e4d42ac48f192e984eea49bb`. This is one explicitly admitted
3600-second continuation of #18/#173/#527, not a new cumulative budget.
The source-import row remains **OPEN**.

## Sources and scope

The primary passage is `lem:ld-soundness` and its proof in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.
Its domain and index encoding are at lines 33-35 and 214-219; its line laws
are at 230-287. The complete dimension-divisibility note was read, including
the independent direct proof and the remaining source-law subline assertions.

The cited result was checked against the actual arXiv:2111.08131v3 source,
downloaded from `https://arxiv.org/src/2111.08131v3`. The runtime copy is
`~/.cache/mipstarre-dev/prover-704-20260922-01/vidick_2022.tex`:
Figure 1, lines 1290-1336; Definition 4.5 and Figure 2, lines 1759-1788;
Definition 4.6, lines 1794-1817; Theorem 4.7 (`thm:main-bipartite`),
lines 1821-1837. The source was not added to or substituted for a repository
mirror. The primary QPBT mirror was present and remained unchanged.
The downloaded TeX SHA-256 is
`73a71fbd5bc0eb38b73a5e9ab112bdf7c94fb1a11ea8ef2a03c2a9545e7383c0`.

The active Lean tree contains neither the tensor-code test interface nor a
proof of Theorem 4.7. The archived March tensor-code audits describe that
older track; they do not supply the missing theorem. No archived blueprint
or active independent low-degree proof was changed.

## Distribution and projectivity

Write a direct sample as `(u,i,w)`, where the three components are independent
and uniform, and write `p_i` for the projection zeroing coordinates before
`i`. After reversing coordinates, the tensor-code subcube pair has the law
of `(u,z)`, where `z_j=u_j` for `j<i` and `z_j=w_j` otherwise. The bijection
`(u,i,w) -> (u,i,w-u)` identifies this with `(u,u+p_i(w))`. It retains every
index, including all indices compatible with the same visible pair. The
pair alone is sent to the prover. Zero directions are retained as repeated
points. `tensorPairDistribution_eq_diagonal` proves this exact equality.

Translation `(u,i,w) -> (u+p_i(w),i,w)` is also bijective and preserves the
canonical diagonal-line description. `diagonal_endpoint_distribution`
proves that either endpoint, together with that full line description, has
the source diagonal-line/point law. No conditioning on a nonzero direction
or approximate uniformity is needed for either identity.

For a visible pair `p`, let `F_p` be the finite fiber of samples yielding
`p`. Every fiber is nonempty: index zero and the difference of the two
reversed points provide a sample. A shared register ranges over the finite
product `R = product_p F_p`. Its uniform marginal at `p` is the uniform
law on `F_p`, as proved by `pairRegister_marginal`. This is the posterior
law induced by uniform source sampling, not a uniform choice of compatible
indices. Thus independently averaging the two provers' measurements is
unnecessary. Projective measurements can instead be placed in blocks
indexed by `R`, with the two registers in their maximally correlated state.

`pairMeasurement` evaluates the source diagonal polynomial at the two
affine parameters for `u` and `u+p_i(w)`. They can be chosen as `t` and
`t+1`, where `u = lineRep(p_i(w),u) + t p_i(w)`. The universal evaluation
convention of the formal source game implies both checks even when the
direction is zero. Answers of the wrong source type already fail its
predicate; any fixed completion of their target answer is legitimate only
with this rejection comparison proved explicitly.

`correlatedPairState_norm` proves normalization of the explicitly constructed
state. `correlatedPairState_born` proves that two block diagonal effects have
Born weight equal to the uniform average of the original weights in matching
blocks. This extends the finite-register calculation already used by the
seed lift to the dependent pair register; its proof uses the existing EPR
normalization identity and finite matrix sums.

`weighted_source_rejection_le` bounds the source branch loss with tensor
weights by `3/2 * (1-S.value)`. It uses the existing exact seed lift, includes
the three synchronous source branches, and assumes no reduction certificate.
The result is explicitly about a reweighted source loss. No claim identifies
it with the value of a completed tensor-code strategy.

## Numerical proposal for main

The printed choice `K=m^3 d` is invalid at `m=1,2,3` for every positive
`d`, and at `m=4,d=1,2`. On the source domain, `m` is a power of two, so
the failing dimensions are `1,2` and those two degree values at `4`.
The minimal pointwise increase that keeps the printed value whenever it
is legal is

`K* = max(m^3 d, 12m(d+1))`.

For positive integers `m,d`, one has `d+1 <= 2d` and `m <= m^3`, hence

`12m(d+1) <= K* <= 24m^3 d`, and `m^3 d <= K*`.

Consequently `exp(-b K*/m^2) <= 2^(-bmd)` for every `b>=0`, since
`log 2 <= 1`. This handles all dimensions uniformly, including every
small-dimensional case. A prefactor `(m(d+1)K*)^c` is at most
`48^c (md)^(4c)` for `c>=0`. Therefore the usual explicitly quantified
polynomial bound in Theorem 4.7 is absorbed into
`a(md)^a (epsilon^b + q^(-b) + 2^(-bmd))` by increasing the universal
prefactor/exponent and, if necessary, decreasing the positive error exponent
to at most one. This is a proposal about an auxiliary proof parameter, not
an alteration of the verifier or an application of an assumed soundness
statement. Main must separately accept the proposal before it replaces the
printed instantiation in a completed import.

The Reed--Solomon application additionally needs the nontrivial regime
`d<q`, where its distance is `q-d` and interpolation parameter is `d+1`.
For `d>=q`, the target consistency bound is at least one (take universal
`a>=1`, `0<b<=1`), so unit bounds handle the conclusion without claiming a
Reed--Solomon code of negative or zero distance. Tensor-code codewords are
functions; the source conclusion uses polynomial representatives. Their
evaluation identification, and its injectivity in the nontrivial regime,
must also be supplied.

## Complete consumer comparison

The proposed change to the auxiliary parameter preserves the entire error
family, its universal quantifiers, and concavity in `epsilon`. It changes
no question distribution, answer alphabet, simultaneity parameter, or
source theorem hypothesis. Thus all consumers can keep their statements:

| Source use | Required conclusion and effect of the proposal |
| --- | --- |
| Chapter 8, 413-458, `lem:ld-soundness` | Both point/polynomial relations and global agreement for every simultaneity parameter. A one-coordinate tensor reduction alone does not prove the general case. |
| Chapter 11, 1401-1404, `def:pcpparams` | Universal soundness constants may be enlarged; parameter choices already depend on them. |
| Chapter 11, 2444-2507, `claim:ar-3` | Single-polynomial relations and Jensen averaging require the same concave error family. |
| Chapter 11, 2580-2615 | Individual proof measurements and a simultaneous measurement at `(q,m',d,m'+6)` require all three conclusions and general simultaneity. |
| Chapter 11, 2708-2717 and 2957-2985 | Subsequent square-root bounds and the final answer-reduction error use the same polynomial/power error family. |
| Chapter 14, 1063-1116, `lem:qld-sublines` | An import on the valid seed domain does not define the seed-indexed game at dimension `2m+2`. |
| Chapter 14, 1267-1298, `lem:qld-4-7` | The printed route still requires the undefined extended source law, the preceding combined-line strategy, and both mixed consistency conclusions. |
| Chapter 14, 1423, 1465-1492, 1584, 1627, 1671 | Pulling apart, extraction, and final Pauli soundness consume the polynomial-pair conclusion, already proved by the independent direct route. |

Blueprint chapter 13 keeps the printed tensor-code proof obligations separate
from the completed `lem:ld-soundness-formalized` and the general-simultaneity
support. Chapter 15's subline, combined-line, and global-pair nodes preserve
the source/direct-law distinction. Chapter 16's soundness proof retains that
scope record. The active Lean consumers are `exists_ld_soundness`,
`exists_direct_ld_soundness`, `exists_globalPairWitness`, and the extraction
modules `Construction` and `SourceUnitary`; these existing declarations are
unchanged and need no new hypothesis.

Theorem 4.7's displayed conclusions are asymmetric: Alice's points versus
Bob's global measurement, Alice's global line restriction versus Bob's lines,
and global agreement. The source asks for both point directions. This must
be derived for the same pair of global measurements, using the global
relation, point synchronicity, and the consistency triangle inequality (or
a fully justified symmetric construction). Applying the theorem twice does
not by itself identify the two resulting global measurements.

## Remaining targets

1. Complete the tensor-code strategy, including point and axis families and
   their codeword outcomes, using the proved normalized shared state and
   the pair family for each prover.
2. Compose the proved joint disintegration and block Born-weight identities.
   Establish the two endpoint checks and pair synchronicity from the actual source game.
   Then prove the weighted rejection bound, including invalid answers.
3. Formalize the required Reed--Solomon instance of Theorem 4.7 from proved
   inputs, including its quantitative constants. There is no such theorem
   available to apply in this tree; no `Statement` assumption is introduced.
4. Derive both mixed conclusions for the same global measurements, remove
   the shared registers, and recover global agreement on the original spaces.
   Separate compression does not preserve global/global consistency.
5. Supply the representative/codeword identification and the trivial large
   degree branch, accept the auxiliary-parameter proposal, and absorb the
   actual theorem's quantitative bound. Compose the established general
   simultaneity construction without changing its theorem.

These are prospective construction/proof targets, not extra hypotheses or
new declarations with proof holes. The independent direct and seed-indexed
soundness results remain credited and complete. None of these targets
resolves the separate `2m+2` seed-index obstruction.
Suggested names for subsequent constructions are `tensorCodeStrategyOfLd`,
`tensorCodeStrategyOfLd_rejection_le`, `exists_reedSolomonTensor_soundness`,
and `tensorCodeSoundness_to_source`. None is declared or assumed here.

## Statement integrity

No paper-labelled theorem statement or existing proof was changed. The
paper assumes admissible positive `(q,m,d,k)`, with `m` dividing `q`, a
projective source strategy, and value at least `1-epsilon`. Its conclusion
is the two mixed and one global consistency relations, with the same
universal `deltaLd` error. The existing Lean theorem retains exactly these
inputs and conclusions, through its previously completed independent proof.
Verdict for that theorem: faithful boundary encoding, unchanged.

The new pair-law identities assume only `DirectLdParams`; the visible
question omits the hidden index. The register is constructed rather than
assumed. The projectivity lemma assumes only projectivity of the supplied
source measurements, and the normalized state comes from any source strategy.
The Born identity assumes arbitrary block operators and is exact. The
scalar weight lemma starts from `LdParams`, so the source divisibility
condition is retained, not imposed at an extended dimension. The parameter
lemmas assume positive natural `m,d`, and the exponential lemma additionally
assumes `b>=0`. Their conclusions are exactly the auxiliary statements
displayed above; they are not advertised as source soundness.

The pointwise completion of wrong-type answers is confined to the explicit
readout definition. Its loss comparison remains an open target; no theorem
uses completion to discard a precondition or to claim game equivalence.

## Cumulative provenance

The preserved #527 audit at
`ac7cd808:audits/2026-09-12-issue-527-ld-soundness.md` credits
`5c40a3b8` (one-coordinate seed soundness), `14aad87d` (general direct
simultaneity), `e1d8eaa2` (error absorption), and `8d593835` (reconciliation).
Its six #134/#210 prover sessions total 13,231 recorded seconds. The three
#527 sessions add 3,861, 64, and 1,726 seconds, including the failed service
attempt and the third session's pre-tool delay. That subtotal is 18,882
seconds, excluding other related work, reviews, owner sessions, and unknown
times. It is a lower bound, not the entire cost of the gap.

The checked-in #18 rows retain 510, 1,928, 401, 1,675, and 0 seconds;
the #173 rows retain 1,853 and 1,086 seconds. These are separate historical
records, not grounds to reset the inherited budget. Resumed usage counters
can overlap and null usage is unknown, not zero. The PR #542 preservation,
its independent review and merge as PR #600, and the subsequent audits
remain recorded in `audits/2026-09-18_seed-indexed-soundness-faithfulness-542.md`
and the original telemetry. This session does not rewrite any of those
records or assert that the displayed subtotals include every predecessor.

## Validation

All six new leaves, the collection module, and `MIPStarRE/QPBT.lean` pass
focused `lake env lean` checks. The ten new theorems and the unchanged
`exists_ld_soundness`, `exists_direct_ld_soundness`, and
`exists_globalPairWitness` each have exactly the axiom closure
`propext`, `Classical.choice`, `Quot.sound`. The new Lean files contain no
proof holes, explicit axioms, forbidden proof-integrity tokens, or debug
commands. Whitespace and the 100-character Lean line check pass.
Both the QPBT and repository root umbrellas were checked into branch-private
oleans. Running the existing checker with
`lake env lean --run scripts/Checkdecls.lean blueprint/lean_decls` resolves
all 2141 declarations; the prebuilt checker executable was absent.

Blueprint synchronization and LaTeX conventions pass. Synchronization
reports only the pre-existing four orphan marks in chapter 16 and two
statement/proof mark differences. After generating the bibliography with
`texra-blueprint bbl`, the final `leanblueprint web` run passes with no
warnings or errors in its log. The edited gap note builds to a 16-page PDF
with `latexmk`; its structural style check and `paper-gaps check` pass,
the latter retaining the repository's existing missing-verdict-marker
warnings. Each proof milestone was committed with normal hooks.

One pending commit was cancelled when its focused check exposed a mismatch
between two finite-type instances; the proof was repaired and checked before
the normal hooks were rerun and the checkpoint committed. No broken
checkpoint, hook bypass, unproved declaration, or retained unfinished Lean
file resulted. The final receipt records the exact head and log locations.
No full build, CI publication, independent review, or merge was attempted;
those gates belong to main under this assignment.
