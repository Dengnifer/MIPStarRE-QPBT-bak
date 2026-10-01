<!-- scout: scout-palomar-faithfulness-route-20261002-02 2026-10-02 -->
## Mathlib scouting report — 2026-10-02

**Decision for MAIN: use the named-definition route for exactly `MIPStarRE.QPBT.fixedFieldModel`.** Its existing type contains the required mathematical contract, and the official comparator supports leaving its Challenge value unspecified while checking the existing Solution construction, including its complete axiom dependencies.

This revises the predecessor’s recommendation to retain the construction inside the Challenge. Keep that construction unchanged in the Solution. The compact game definitions and exact equivalence proofs remain necessary.

This is a source-supported route decision, **not certification of an implemented Challenge**. Project findings refer to snapshot `97dc6e049b0ce966be18bf8801e14b30c0081919`.

### Mathematical source

- `references/qpbt-paper/04_preliminaries.tex:662–680,702–725,769–773` — admissible sizes are \(q=2^k\) with odd \(k\); field elements use the natural binary encoding of coordinates in a fixed self-dual normal basis.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229–1234,413–440,1431–1445,1469–1491` — respectively `lem:pauli-completeness`, `lem:ld-soundness`, `thm:pauli`, and `cor:pauli-binary`.

The proposed separation asks the Solution to supply the already constructed family of valid field models. All four results continue to use that same fixed family. Their quantifiers, strategy domains, game definitions, outcome indexing, and error expressions remain unchanged.

The existing construction formalizes mathematical existence, not the polynomial-time algorithm assertion of `lem:efficient_basis`. This limitation already appears in its docstring.

### Relevant Mathlib definitions

- `Module.Basis` — `Mathlib/LinearAlgebra/Basis/Defs.lean:90` — exact basis structure retained in the field contract.
- `Algebra.trace` — `Mathlib/RingTheory/Trace/Defs.lean:71` — exact trace used by the self-duality requirement.
- `GaloisField` — `Mathlib/FieldTheory/Finite/GaloisField.lean:70` — carrier used by the existing Solution construction.

### Relevant Mathlib lemmas and theorems

- `Fintype.card_congr` — `Mathlib/Data/Fintype/Card.lean:67` — the stored equivalence \(K\simeq\mathrm{Fin}\,q\) enforces cardinality \(q\); no extra cardinality assumption is needed.
- `GaloisField.card` — `Mathlib/FieldTheory/Finite/GaloisField.lean:131` — supplies the cardinality calculation in the existing construction.
- `IsGalois.normalBasis` — `Mathlib/FieldTheory/Galois/NormalBasis.lean:121` — adaptable near-match for normality, but does not supply self-duality.

The earlier self-dual-basis finding is unchanged: searches of finite-field, normal-basis, basis, and trace APIs found no usable Mathlib replacement for the project’s complete self-dual normal-basis construction. **No replacement is needed for this route.**

### Relevant MIPStarRE declarations

| Declaration | Snapshot location | Status and relevance |
|---|---|---|
| `MIPStarRE.LDT.FieldModel` | `MIPStarRE/LDT/Basic/ParametersBase.lean:212` | Stores carrier, field structure, finiteness, decidable equality, and equivalence to `Fin q`. Retain unchanged. |
| `MIPStarRE.QPBT.IsAdmissibleSize` | `MIPStarRE/QPBT/Algebra/FieldBasis.lean:26` | Exactly `∃ k : ℕ, Odd k ∧ q = 2 ^ k`. Retain its value. |
| `MIPStarRE.QPBT.FixedFieldModel` | Same file:448 | Full algebraic and encoding contract. Retain unchanged. |
| `MIPStarRE.QPBT.exists_selfDualNormalBasis` | Same file:396 | Existing proved self-dual normal-basis existence theorem. |
| `MIPStarRE.QPBT.exists_fixed_field_model` | Same file:496 | Existing proved construction of the complete record. |
| `MIPStarRE.QPBT.fixedFieldModel` | Same file:552 | Existing selector, obtained by `Classical.choice` from that construction. Register this definition alone. |
| `MIPStarRE.QPBT.LdParams.model` | `MIPStarRE/QPBT/Test/LowDegreeGame.lean:61` | Uses the global selector. |
| `MIPStarRE.QPBT.AdmissibleParams.model` | `MIPStarRE/QPBT/Test/PauliBasisTest.lean:65` | Uses the same global selector. |

The complete `FixedFieldModel` contract retains:

- the inherited finite field and equivalence to `Fin q`;
- its algebra structure over `ZMod 2`;
- an odd basis dimension and `q = 2 ^ basisDim`;
- an actual basis;
- `representation_natural`, identifying the integer encoding with the little-endian binary coordinate sum;
- `selfDual`, expressed through `Algebra.trace`;
- `normal`, expressed through a Frobenius generator.

The four existing proved targets remain:

- `MIPStarRE.QPBT.exists_spcc_value_one` — `MIPStarRE/QPBT/Test/Completeness.lean:267`.
- `MIPStarRE.QPBT.exists_ld_soundness` — `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82`.
- `MIPStarRE.QPBT.pauli_soundness` — `MIPStarRE/QPBT/Test/Soundness.lean:110`.
- `MIPStarRE.QPBT.pauli_soundness_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:461`.

Source scans found no direct proof holes or axiom declarations in the construction or these four files. This session did not rerun their transitive axiom audit.

### Suggested approach

**Policy support.** Palomar expressly permits `definition_names` to identify definitions with unspecified Challenge values supplied by the Solution. It requires an explanation of the intended value and the constraints imposed by the compared results; mechanical acceptance does not settle mathematical faithfulness. Document this definition as the fixed valid-field choice, with the full contract above. [Palomar submission standard, §2.3](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#23-comparator-configuration)

**Verified behavior at the project’s official comparator pin.** I inspected the clean local checkout at `07bc4ea40f2266dcb861820a2ec1fa3244ed307f`, including implementation and test fixtures.

- `Comparator.definitionHoleMatches` — `Comparator/Compare.lean:61` — compares name, universe parameters, stored type, and safety. It does not compare the definition’s value or reducibility hints.
- `Comparator.compareAt` — same file:65 — requires both registered constants to be definitions.
- `Comparator.Compare.loop` — same file:36 — follows a registered definition’s type dependencies without following its value. Unregistered dependencies undergo full constant comparison. [Pinned comparison implementation](https://github.com/leanprover/comparator/blob/07bc4ea40f2266dcb861820a2ec1fa3244ed307f/Comparator/Compare.lean)
- `Comparator.checkAxioms` — `Comparator/Axioms.lean:52` — independently roots its traversal at every registered Solution theorem **and definition**. The traversal examines types and values, including opaque proofs, and rejects unpermitted axioms. [Pinned axiom checker](https://github.com/leanprover/comparator/blob/07bc4ea40f2266dcb861820a2ec1fa3244ed307f/Comparator/Axioms.lean), [dependency traversal](https://github.com/leanprover/comparator/blob/07bc4ea40f2266dcb861820a2ec1fa3244ed307f/Comparator/Util.lean)
- `Comparator.verifyMatch` — `Main.lean:244` — performs comparison and axiom checking before NanoDa, when enabled, and Lean kernel replay. [Pinned verification driver](https://github.com/leanprover/comparator/blob/07bc4ea40f2266dcb861820a2ec1fa3244ed307f/Main.lean#L244)

The upstream `tests/projects/def_hole_axiom_issue/Solution.lean` fixture deliberately hides `sorryAx` inside a definition whose theorem can reduce without mentioning it. Its expected result is failure. I inspected that fixture; I did not execute it.

**Candidate stub and configuration.** Copy the existing `FieldModel`, `IsAdmissibleSize`, and complete `FixedFieldModel` declarations unchanged into the Mathlib-only Challenge prelude. Preserve required instances and accessors. Within its public declaration section, replace only the selector’s value:

```lean
namespace MIPStarRE.QPBT

noncomputable def fixedFieldModel (q : ℕ) (hq : IsAdmissibleSize q) :
    FixedFieldModel q := by
  sorry

end MIPStarRE.QPBT
```

This is a declaration fragment, not a standalone Challenge. The complete file still needs its `module` header, Mathlib import, retained contract definitions, concrete game/error definitions, and theorem statements.

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "MIPStarRE.QPBT.exists_spcc_value_one",
    "MIPStarRE.QPBT.exists_ld_soundness",
    "MIPStarRE.QPBT.pauli_soundness",
    "MIPStarRE.QPBT.pauli_soundness_qubit"
  ],
  "definition_names": [
    "MIPStarRE.QPBT.fixedFieldModel"
  ],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ],
  "enable_nanoda": true
}
```

The Solution imports the existing selector with its existing construction. It must not import the sorried Challenge or introduce another selector.

**Faithfulness judgment.** This is a supported separation between a mathematical object’s specification and its checked construction. The return type contains intrinsic finite-field and basis requirements, without embedding the four desired conclusions. The selector takes only the field size and its admissibility proof; no strategy, game, or error parameter is available for tailoring the choice. Completeness additionally supplies a successful strategy, keeping Pauli soundness substantive.

The comparator does **not** prove that the selected value equals the historical `Classical.choice` expression: it deliberately permits any implementation satisfying the type. Preservation of the exact existing choice therefore also rests on retaining that implementation in the pinned Solution, which final review must verify. This route adds no theorem hypothesis or quantifier and requires no field transport.

**Proof-only helper holes.** There is no blanket permission to erase their bodies:

| Helper’s position | Supported treatment without adding compared claims |
|---|---|
| Used only inside the registered selector’s construction or theorem proofs | Omit it from the Challenge entirely when no other comparison dependency reaches it. Its Solution proof remains checked. |
| Still reached through a compared definition, type, instance, or embedded proof | Retain its matching body. Replacing it with `sorry` fails full constant comparison. |
| Inline proof field in an ordinary compared definition | Its containing value is still compared; proof irrelevance does not make the comparator ignore it. |

At `07bc4ea…`, adding a helper to `theorem_names` does not exempt a separate dependency occurrence from full comparison. The newer `5756749…` implementation and the inspected native comparator exempt **registered** theorem targets, but neither exempts unlisted helpers. Thus neither supplies the requested unrestricted proof erasure without additional compared claims. [Newer comparison implementation](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Comparator/Compare.lean), [native implementation](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/src/lake/Lake/Check/Compare.lean)

### Gaps to fill

**Qualified size reduction.** An in-memory, nested-comment/string-aware scan reproduced the predecessor’s counts. Removing construction-only source ranges and replacing the selector body gives:

| Source surface | Code-bearing lines | UTF-8 bytes |
|---|---:|---:|
| Existing field mirror | 407 | 18,287 |
| Retained contract, selector, instances, accessors, and scaffolding | 32 | 1,615 |
| Existing complete union | 2,278 | 98,148 |
| Union after this field-only pruning | 1,903 | 81,476 |

The candidate saving is **375 lines and 16,672 bytes**, not all 407 lines. Nineteen construction-related declarations have no remaining textual occurrence in the other mirrored sources.

These are **source-level measurements**, not a regenerated kernel dependency graph or compiled artifact. Compiler-generated references and other dependency paths must be checked. Documentation and blank lines also count toward Palomar’s hard **1,000 physical lines and 100 KiB** limits.

Consequently:

1. Update closure extraction to follow only the registered selector’s **type** for Challenge comparison. The current `scripts/comparator/extract_closure.lean` follows all values.
2. Retain the predecessor’s compact-game route and exact bridge obligations. This field reduction alone still leaves approximately 1,903 stripped lines.
3. Replace the predecessor’s roughly 965-line planning allocation with roughly **590 lines**, subject to implementation and measurement.
4. Run the final comparator with all four theorem targets and the selector target, including independent kernel checking.
5. Obtain the required independent Astra review of the implemented Challenge against the paper and original statements.

**Bound strength:** this change introduces no numerical estimate or transport inequality. All constants, exponents, the unsquared state norm, and the separate squared operator-error sums must remain unchanged.

**Live verifier caveat:** the fetched Palomar runner now uses the toolchain-bundled comparator, and its fetched minimum is `v4.35.0-rc2`; this source snapshot uses `v4.32.0`. I inspected the native comparison and axiom-checking implementations and found the same named-definition support. MAIN must reconcile current toolchain admission separately; the historical comparator success does not establish present submission readiness. [Current toolchain policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json), [verification runner](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/scripts/verify_submission.py)

### Searched

Read root `AGENTS.md`, both scout prompts from committed `main`, the complete owner briefing including §9, the predecessor report, local workflow guidance, `docs/api_surface.md`, finite-field scouting notes, paper passages, blueprint definitions, snapshot field construction, theorem interfaces, and comparator documentation.

Inspected official comparator configuration parsing, definition matching, dependency traversal, axiom checking, kernel replay, and definition-hole fixtures. Cross-checked the newer comparator and native implementation. Searched Mathlib and local sources by finite-field cardinality, trace, normal/self-dual basis, selector uses, and references to the proposed omitted declarations.

`gh_common.py issue-view 743` failed because network sockets are prohibited in the shell sandbox. Live issue-comment deduplication remains unchecked.

No files, branches, commits, builds, submissions, GitHub writes, or workers were created. The next step is a measured Challenge extraction using this single registered definition, followed by the remaining compact-definition proofs and independent final review.
