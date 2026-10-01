<!-- scout: scout-palomar-faithfulness-route-20261002-01 2026-10-02 -->
## Mathlib scouting report — 2026-10-02

**Decision for MAIN:** pursue a compact statement module that **retains the existing fixed field model and its proved self-dual normal-basis construction**, and proves exact bridges from compact game and measurement definitions to the four existing theorems. Preserve the existing declarations and their public statements.

Replacing the field carrier by `GaloisField` is mathematically possible without additional theorem hypotheses, but **does not by itself eliminate the basis-construction dependency**. It adds substantial transport work. The retained-field route has a justified target of approximately **900–1,000 lines and 50–75 KiB**, subject to implementation and measurement. This is a route recommendation, not approval of a completed Challenge.

All project findings below concern immutable snapshot `97dc6e049b0ce966be18bf8801e14b30c0081919`. The installed Mathlib revision matches that snapshot’s pin, `81a5d257c8e410db227a6665ed08f64fea08e997`.

### Mathematical source

The primary source is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`:

| Result | Source | Statement to preserve |
|---|---|---|
| `lem:pauli-completeness` | Lines 1229–1234 | Every admissible Pauli test admits a value-one SPCC strategy. |
| `lem:ld-soundness` | Lines 413–440 | Universal constants precede all parameters and successful projective strategies; two polynomial measurements satisfy all three consistency bounds. |
| `thm:pauli` | Lines 1431–1445 | Successful arbitrary strategies admit local isometries and a unit auxiliary state, with the state norm and both Pauli operator-family errors bounded by the displayed error function. |
| `cor:pauli-binary` | Lines 1469–1491 | The same conclusion in binary coordinates, retaining field-valued outcome indexing. |

Additional essential passages:

- `references/qpbt-paper/04_preliminaries.tex:702–725`: existence of the self-dual normal basis; lines 769–773 fix its choice.
- The same file, lines 1180–1228: exact EPR and Pauli-projector transport using that basis.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:215–221`: the coordinate selector uses the integer encoding of the seed.
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:26–37,176–180,232–269`: finite-dimensional strategies, SPCC, consistency defect, and **summed squared** operator errors.

The paper uses positive integers; the existing positive-parameter fields are faithful boundary conditions. See also `docs/paper-gaps/qpbt_anticommuting-probability.tex:76–91`.

**Quantitative distinction:** the registered soundness statements bound an **unsquared state norm** and two **sums of squared operator norms**. A compact interface must preserve this distinction.

### Relevant Mathlib definitions

- `GaloisField` — `Mathlib/FieldTheory/Finite/GaloisField.lean:70` — finite-field carrier; does not select the required self-dual basis.
- `PMF.uniformOfFintype` — `Mathlib/Probability/Distributions/Uniform.lean:284` — exact uniform source law.
- `PMF.map` — `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:47` — compact push-forward question distribution.
- `Matrix.PosSemidef` — `Mathlib/LinearAlgebra/Matrix/PosDef.lean:59` — sufficient positivity field for a compact POVM record.
- `Matrix.kronecker` — `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:274` — existing tensor placement.
- `MvPolynomial.restrictDegree` — `Mathlib/RingTheory/MvPolynomial/Basic.lean:173` — **exact existing polynomial-representative domain**, with individual degree bounded by `d`. Prefer this to constructing another polynomial representation.

### Relevant Mathlib lemmas and theorems

- `GaloisField.algEquivGaloisFieldOfFintype` — `Mathlib/FieldTheory/Finite/GaloisField.lean:166` — adaptable: supplies an algebra equivalence from the existing finite field, but has no basis-alignment guarantee.
- `IsGalois.normalBasis` — `Mathlib/FieldTheory/Galois/NormalBasis.lean:121` — adaptable: normality alone does not supply self-duality.
- `Module.Basis.map_equivFun` — `Mathlib/LinearAlgebra/Basis/Defs.lean:251` — exact coordinate identity when the **existing basis is transported** through a linear equivalence.
- `Algebra.trace_eq_of_algEquiv` — `Mathlib/RingTheory/Trace/Basic.lean:174` — exact trace preservation under field transport.
- `PMF.map_apply`, `PMF.map_comp` — `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:54,67` — exact push-forward calculations.
- `Matrix.nonneg_iff_posSemidef` — `Mathlib/Analysis/Matrix/Order.lean:60` — exact bridge between compact matrix positivity and the project’s matrix order.
- `Fintype.sum_equiv` — `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:722` — preserves outcome sums under bijections.
- `LinearIsometryEquiv.piLpCongrLeft` — `Mathlib/Analysis/Normed/Lp/PiLp.lean:865` — coordinate transport preserving norms exactly.
- `MvPolynomial.map_eval` — `Mathlib/Algebra/MvPolynomial/Eval.lean:380` — evaluation commutes with coefficient transport.
- `MvPolynomial.degrees_map_of_injective` — `Mathlib/Algebra/MvPolynomial/Degrees.lean:196` — degree preservation for an injective coefficient map.

**Miss:** searched finite-field, normal-basis, trace, and basis modules using self-duality, normality, and trace-pairing formulations; no usable Mathlib self-dual normal-basis existence theorem was found. The project already supplies this result.

### Relevant MIPStarRE declarations

**Existing proved targets**

| Declaration | Snapshot location |
|---|---|
| `MIPStarRE.QPBT.exists_spcc_value_one` | `MIPStarRE/QPBT/Test/Completeness.lean:267` |
| `MIPStarRE.QPBT.exists_ld_soundness` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` |
| `MIPStarRE.QPBT.pauli_soundness` | `MIPStarRE/QPBT/Test/Soundness.lean:110` |
| `MIPStarRE.QPBT.pauli_soundness_qubit` | `MIPStarRE/QPBT/Test/QubitForm.lean:461` |

Their source files contain proof bodies and no direct proof holes or axiom declarations. This is a source inspection, not a newly executed transitive axiom audit.

**Field construction and transport**

- `MIPStarRE.QPBT.exists_self_dual_normal_basis_gal` — `MIPStarRE/QPBT/Algebra/FieldBasis.lean:323` — proved group-algebra construction.
- `MIPStarRE.QPBT.exists_selfDualNormalBasis` — same file:396 — proved existence over any finite binary extension of odd degree.
- `MIPStarRE.QPBT.exists_fixed_field_model` — same file:496 — proved existence, including natural binary encoding.
- `MIPStarRE.QPBT.fixedFieldModel` — same file:552 — `Classical.choice` from that existence statement.
- `MIPStarRE.QPBT.binTrace_mul_eq_dotProduct` — `MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean:138` — exact trace/coordinate pairing identity.
- `MIPStarRE.QPBT.pauliProj_reindex_quditQubitLabelEquiv` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:674` — proved exact projector transport.
- `MIPStarRE.QPBT.qubit_state_error_to_qubit`, `MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit`, `MIPStarRE.QPBT.qubit_operator_distance_b_to_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:356,376,395` — **exact error equalities**, already supporting the binary corollary.

**Compact-interface bridges already available**

- `MIPStarRE.LDT.Distribution.toPMF_map` — `MIPStarRE/LDT/Basic/Distribution.lean:203` — exact compatibility of project and Mathlib push-forwards.
- `MIPStarRE.LDT.Distribution.toPMF_apply_toReal` — same file:188 — recovers the original real weight exactly.
- `MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum` — `MIPStarRE/LDT/Basic/DistributionPMF.lean:61` — exact expectation bridge.
- `MIPStarRE.QPBT.consistencyDefect_uniform_question_equiv`, `MIPStarRE.QPBT.consistencyDefect_outcome_equiv` — `MIPStarRE/QPBT/Games/Consistency.lean:34,54` — exact question/outcome relabeling.
- `MIPStarRE.LDT.Preliminaries.polyFunc` — `MIPStarRE/LDT/Preliminaries/Polynomials.lean:27` — already an abbreviation for Mathlib’s restricted-degree submodule.
- `MIPStarRE.QPBT.ldSpaceSplit` — `MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean:41` — existing equivalence between ambient coordinates and point/seed/direction products.

**Useful near-match for the main remaining algebraic simplification**

- `MIPStarRE.QPBT.lineRepMap` — `MIPStarRE/QPBT/Algebra/Lines.lean:86` — presently imports the general canonical-complement construction.
- `MIPStarRE.QPBT.IsReducedRowEchelon.canonicalComplement_eq_nonpivot_indices` — `MIPStarRE/QPBT/Algebra/RowEchelon.lean:103` — identifies the complement needed to prove the compact one-dimensional formula.

### Suggested approach

**1. Preserve the fixed choice rather than introduce another one.**

Create one Mathlib-only statement module containing the shared field declarations and the compact interface. Relocate the necessary original field declarations, retaining their fully qualified names, types, and selector. Existing modules import this shared module; the four source theorem statements remain unchanged.

In particular, retain:

- `MIPStarRE.LDT.FieldModel`;
- `MIPStarRE.QPBT.FixedFieldModel`, including natural encoding, self-duality, and normality;
- the proved existence construction and `MIPStarRE.QPBT.fixedFieldModel`.

Replacing an existence proof of the **same proposition over the same type** does not change the selector by proof irrelevance. Creating a second, structurally similar record and independently choosing an inhabitant does **not** provide that guarantee.

Compile the entire statement prelude as one module on the library side before producing the single-file Challenge. Do not concatenate previously compiled module fragments and expect their auxiliary names to match. The existing comparator documentation expressly records this problem at `docs/comparator.md:150–177`.

**2. Use a compact vocabulary with transparent meanings.**

The following are proposed interface components, not declarations already implemented:

| Component | Lean-level content |
|---|---|
| Parameters | Preserve the existing numerical records and fields exactly: `q,m,d,k` for LD; `q,m,d` for Pauli; the same admissibility and positivity conditions. |
| POVM | Effects `α → Matrix I I ℂ`, positivity of each effect, and `∑ a, effect a = 1`. The existing redundant submeasurement inequality follows internally. |
| Strategy | Two finite local index types, a unit vector in `EuclideanSpace ℂ (I × J)`, and two POVM families. |
| Symmetric strategy | One local index type, a swap-invariant unit state, and one measurement family. |
| Game | Finite question/answer types, a `PMF` on question pairs, and the explicit Boolean win predicate. |
| Value | Finite weighted sum of the original Born probabilities using `(μ xy).toReal`. |
| SPCC | Projectivity everywhere; consistency everywhere; commutation on positive-weight question pairs; symmetry supplied by the symmetric-strategy record. |
| Polynomial outcomes | `Fin k → ↥(MvPolynomial.restrictDegree (Fin m) F d)`. |
| Extraction witness | Auxiliary finite index types, two local linear isometries, and a unit auxiliary vector. No error assumption or bound in this record. |
| Errors | Separate state norm, Alice operator sum, and Bob operator sum. |

Use one generic extraction-witness structure, instantiated with either the field register or the binary register. Keep the error expressions separate.

**3. Compact the games without restricting strategies.**

Represent ambient question vectors by products of their existing blocks. Preserve the **full** question carriers, including unused coordinates.

Use a global three-case answer sum for LD and a global seven-case answer sum for Pauli, matching the existing constructors exactly. A question-dependent answer type that permits only correctly shaped answers would restrict the quantified strategies.

Define question laws directly:

- LD: uniform on all nine ordered type pairs and the ambient seed space, then apply the two question maps.
- Pauli: uniform on the existing ordered-edge subtype and ambient seed space, then apply the two question maps.

The existing Pauli ordered carrier has 86 elements: 26 loops and both orientations of 30 non-loop edges. Uniform sampling of undirected edges followed by a fair orientation coin gives different loop weights.

Replace the general line projection in the compact vocabulary by this explicit formula:

\[
\operatorname{rep}(u,v)=
\begin{cases}
u,&v=0,\\
u-(u_j/v_j)v,&j=\min\{i:v_i\ne0\}.
\end{cases}
\]

Prove its equality with the existing canonical representative in the Solution bridge. The zero-direction identity is the source convention. Preserve the universally quantified line-incidence win conditions, including that case.

Keep every win-predicate branch, answer-shape rejection, gamma gate, and off-edge default. Direct finite products/sums can express the indicator vector and low-degree encoding.

**4. Preserve all four theorem interfaces.**

The compact aliases should have these quantifier orders and conclusions:

| Result | Required interface |
|---|---|
| Completeness | `∀ P, ∃ S : SymmetricStrategy ..., IsSPCC S ∧ value S = 1`. |
| LD soundness | `∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧ ∀ L ε, 0 < ε → ∀ S, IsProjective S → 1 - ε ≤ value S → ∃ GA, ∃ GB, C₁ ≤ δ ∧ C₂ ≤ δ ∧ C₃ ≤ δ`. |
| Pauli soundness | `∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ P ε, 0 ≤ ε → ∀ S, 1 - ε ≤ value S → ∃ w, stateNorm ≤ δ ∧ (∀ W, errorA W ≤ δ) ∧ (∀ W, errorB W ≤ δ)`. |
| Qubit soundness | The preceding interface with binary output registers and projectors indexed by the **original field outcomes through the fixed coordinate map**. |

Copy the two error functions exactly:

\[
\delta_{\rm ld}=a(dmk)^a\left(\varepsilon^b+q^{-b}+2^{-bmd}\right),\qquad
\delta_{\rm qld}=a(md)^a\left(\varepsilon^b+q^{-b}+2^{-bmd}\right).
\]

Keep the existing Lean argument orders and real-power expressions. The bridges reuse the supplied `a,b` unchanged.

For LD, preserve the existing point-answer postprocessing that sends wrong-form answers to zero. For both Pauli conclusions, preserve the **raw prescribed-answer effects**. Those two conventions differ in the registered statements and cannot be unified for convenience.

**5. Field-transport decision.**

Let `F` be the current selected field and let `e : F ≃ₐ[ZMod 2] GaloisField 2 n`.

Transporting the current basis by `e` gives exact coordinate compatibility through `Module.Basis.map_equivFun`; trace preservation gives self-duality. This needs no additional hypothesis or outer quantifier. However, its definition still refers to the current chosen basis, so it does not remove that closure.

Choosing an independent basis on `GaloisField` requires more:

- A field equivalence need not preserve the natural binary encoding used by `chiIndex`.
- The seed can instead be transported by the separate bijection
  `encodingNew.symm ∘ encodingOld`, while points, directions, coefficients, and trace multipliers use the field equivalence.
- Binary register transport must then account for the coordinate change
  `κNew ∘ e ∘ κOld.symm`. Self-duality makes it preserve the trace pairing, but all projector and game identities still need proofs.

These are viable mathematical proof directions, not existing complete transport theorems. They also still require a proved self-dual basis on the new field. **Do not treat `GaloisField` plus an arbitrary normal basis as a substitute.**

### Gaps to fill

The retained-field route requires the following **proved Solution-side obligations**, never additional Challenge hypotheses.

| Obligation | Required exact statement |
|---|---|
| Canonical line representative | The explicit least-nonzero-coordinate formula equals the current `lineRepMap`, including `v = 0`. Use the one-row normalized RREF and the existing nonpivot-complement theorem. |
| Question distributions | Each compact PMF equals the push-forward of the existing question distribution under the chosen question equivalence. |
| Win predicates | Boolean equality after question and answer transport, preserving malformed answers and all gate branches. |
| Strategy conversion | Conversions in both directions preserve state and effects under the declared index equivalences. |
| Value and strategy classes | Exact value equality; projectivity equivalence; SPCC equivalence, including commutation on positive-weight support. |
| Polynomial outcomes | Exact bounded-polynomial carrier and evaluation compatibility. Using Mathlib’s existing subtype avoids a new polynomial equivalence. |
| LD conclusions | Exact equality of each of the three consistency defects, including the wrong-form-to-zero postprocessing and uniform point law. |
| Ideal states | Exact equality or coordinate transport of the shuffled auxiliary–EPR state, with its actual normalization. |
| Ideal projectors | Exact matrix equality for both Pauli kinds and both player placements. |
| Errors | Equality of the state norms, hence also their squares, and equality of both summed squared operator errors evaluated on the ideal state. Preserve the final **unsquared** state-bound statement. |
| Final aliases | Apply each existing theorem and transport its witnesses; introduce no constant adjustment or inequality-based replacement. |

Do not replace bounded polynomial representatives by polynomial functions: evaluation can identify distinct representatives when the degree reaches the field size, and these statements assume no `d < q`.

**Statement-integrity verdict**

- **Assumptions:** the proposed route preserves the paper’s positive numerical domain, fixed binary-field convention, finite-dimensional strategies, success inequalities, and the LD-only projectivity assumption.
- **Conclusions:** it preserves value-one SPCC completeness, all three LD consistency conclusions, and both soundness conclusions with their fixed outcome indexing and ideal-state convention.
- **Bounds:** exact transport introduces no coefficient, degree, exponent, square-root, or normalization loss.
- **Established:** the source interfaces, field construction, relevant Mathlib infrastructure, and existing qudit–qubit error identities.
- **Still requiring proof:** the compact definitions’ equivalence to those interfaces. No final compact Challenge has been reviewed or certified.

**Size evidence and expectation**

I independently reproduced the attached report’s stripped count using an in-memory nested-comment/string-aware scan:

| Existing closure component | Code-bearing lines | UTF-8 bytes |
|---|---:|---:|
| Field construction | 407 | 18,287 |
| Field-model base | 13 | 397 |
| General subspace construction | 183 | 7,443 |
| Distribution auxiliary layer | 130 | 5,950 |
| LD game | 153 | 6,006 |
| Pauli game | 324 | 13,721 |
| Four theorem headers | 94 | 4,642 |
| **Whole union** | **2,278** | **98,148** |

A practical allocation is approximately 420 lines for retained field foundations, 35 for parameters, 65 for probability/measurement/strategy definitions, 195 for game definitions, 30 for polynomial consistency, 80 for witnesses and errors, 55 for theorem headers, and 85 for documentation and scaffolding: **about 965 lines**.

This is an implementation budget, not a measured artifact. It depends on removing the general projection and distribution machinery, sharing the quantum definitions, and using compact answer sums. The prior 600–850-line estimate is optimistic if the 407-line field construction is retained. The preferred 300-line size is not a credible target for this route.

### Searched

Read root `AGENTS.md`, both scout prompts from committed `main`, the full owner briefing including §9, local workflow documentation, `docs/api_surface.md`, the relevant finite-field and soundness audits, paper passages, blueprint entries, comparator documentation, and snapshot definitions.

Searched Mathlib by module, declaration name, and mathematical shape: finite-field isomorphism, normal/self-dual bases, trace pairing, basis coordinates, PMF push-forwards, finite-sum reindexing, restricted-degree polynomials, PSD matrices, projections, and Euclidean coordinate isometries. Searched local field, line/RREF, probability, measurement, strategy, polynomial, and qubit-transport APIs.

`gh_common.py issue-view 743` failed because the sandbox prohibits network sockets. Live issue-comment deduplication remains unchecked; this report adds the field-choice judgement, exact bridge obligations, and revised size budget to the attached prior scout.

No files, branches, commits, builds, GitHub writes, external checkouts, or workers were created. The next implementation milestone is the compact line-representative identity plus the shared fixed-field prelude; final size, comparator closure equality, and independent Astra review remain required.
