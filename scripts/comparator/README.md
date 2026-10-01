# Comparator challenge generation

This directory generates the self-contained statement files `Challenge.lean`
used by companion repositories — for the low individual degree test,
[LDT-comparator](https://github.com/LionSR/LDT-comparator), and for the quantum
Pauli basis test,
[QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator) — to verify,
with the official
[leanprover/comparator](https://github.com/leanprover/comparator), that this
library proves the target theorems.  Background and trust model:
`docs/comparator.md`.

A generated challenge imports only Mathlib and, when split, its own mirror
modules.  It re-declares, verbatim and in dependency order, every declaration
in the kernel closure of its target statements, each with a provenance comment;
the targets themselves are stated with `sorry`.

## Challenges

Each challenge is one configuration file under `challenges/`:

| file | targets | expected copy | challenge repository |
|---|---|---|---|
| `challenges/ldt.json` | `MIPStarRE.LDT.Test.mainFormal` | `expected/Challenge.lean.expected` | [LDT-comparator](https://github.com/LionSR/LDT-comparator) |
| `challenges/qpbt.json` | four QPBT headline theorems | `expected/qpbt/` (one module per library module) | [QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator) |

The four QPBT targets are `MIPStarRE.QPBT.exists_spcc_value_one`,
`MIPStarRE.QPBT.exists_ld_soundness`, `MIPStarRE.QPBT.pauli_soundness`, and
`MIPStarRE.QPBT.pauli_soundness_qubit`.

A configuration names the Lean modules the extractor imports, the target
theorems whose statement closure it takes, the header and footer files wrapped
around the assembled body, the checked-in expected copy, and the per-challenge
elaboration-context tables (`extras`, `module_preludes`).  The schema, with the
meaning of every key, is documented at the top of `challenge_config.py`; unknown
keys are rejected, so a typo fails loudly rather than silently dropping context.

### Registered definition frontiers

The optional `definition_names` list implements the official comparator's
named-definition frontier.  Each registered name must resolve to a
repository-local definition.  Its full type and every dependency of that type
remain in the extracted closure, but its value is not traversed.  Every
unregistered definition value and theorem proof reached by the ordinary closure
is still traversed.

The assembler copies the registered declaration's source header, preserving its
name, universe parameters, binders, return type, and safety modifier, and
replaces only its generated Challenge value with `by sorry`.  Missing names and
names that are not definitions fail extraction.  The fifth closure-TSV column
records the definition safety checked from Lean metadata.

This Challenge hole is not a permission for an unchecked Solution axiom.  The
official comparator compares the registered definition's name, universes, type,
and safety while deliberately ignoring its Challenge value.  It separately
traverses the actual Solution definition value during the Solution axiom audit.
Thus the generated Challenge may contain `sorryAx` at the registered value, but
the checked Solution must still supply an implementation using only the
permitted axioms.  Registering one definition does not erase unrelated helper
proofs or values.

Neither checked-in challenge currently sets `definition_names`; omitting it or
setting it to `[]` preserves the historical extraction and both golden fixtures
byte-for-byte.

### Fixed-field prototype measurement

Issue #769 measured a temporary copy of the four-target QPBT configuration at
library base `9643b5ad12422babd3c7245bb0743e54395c30b5`.  The copy registered
only `MIPStarRE.QPBT.fixedFieldModel` and removed the two `FieldBasis` prelude
scopes that became correctly unmatched when the construction disappeared.  It
did not modify `challenges/qpbt.json` or either expected fixture.

The compiled-metadata extraction produced the same 31-file split layout.  The
checked-in tree has 3,956 physical lines and 181,818 bytes; the prototype has
3,509 physical lines and 161,038 bytes, a reduction of 447 lines and 20,780
bytes.  Its unique dependency inventory fell from 275 to 252: 19 ranged field-
construction declarations and four generated helpers disappeared, with no
prototype-only dependency.  The `FieldBasis` mirror fell from 551 lines and
25,746 bytes to 108 lines and 5,396 bytes.  No construction-only dependency
remained in the measured closure.

The prototype still retains `FieldModel`, `IsAdmissibleSize`, the complete
`FixedFieldModel` contract (cardinality, algebra, natural binary encoding,
self-duality, and normality), its instances and accessors, and the exact
`fixedFieldModel` type.  Only the generated Challenge value is unspecified.  In
the unchanged library Solution, the selector remains
`Classical.choice (exists_fixed_field_model q hq)`, so its construction is still
subject to the Solution axiom audit.

This old four-statement tree still exceeds Palomar's 1,000-line and 100-KiB hard
limits.  It is evidence for the definition frontier, not the final single-file
Challenge or a readiness claim; the compact statement/bridge work remains
separate.

`require_expected` distinguishes a challenge that must stay regenerated (`true`,
a missing expected copy is an error) from one still being developed (`false`,
a missing expected copy is reported and skipped).

Adding a challenge means adding a configuration file, a header and a footer —
no generator code changes and, for the machine-wide guard in `local/bin/ci.sh`,
no CI change either, because that guard passes no `--challenge` and therefore
checks every configuration it finds.

## Drift guard and regeneration

The repository keeps each generated challenge checked in under `expected/`.
The LDT copy has a final `.expected` suffix, which keeps that intentionally
monolithic fixture out of the 1000-line project-source guard; the QPBT copy is
a split directory. The PR CI guard regenerates every configured challenge in a
temporary directory and byte-compares it with the checked-in file or tree; it
never writes `Challenge.lean` at the repository root.

Run the deterministic guard from the repository root (requires a built
library).  With no `--challenge` every configured challenge is checked:

```sh
python3 scripts/comparator/check_challenge_drift.py --root .
python3 scripts/comparator/check_challenge_drift.py --root . --challenge qpbt
```

Add `--challenge <name>` (repeatable) to restrict the run to one challenge.

To update a checked-in expected copy after an intentional statement or
dependency change, run the exact maintenance command:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . --update
```

That command refuses a challenge whose configured header or footer file is not
in the tree, and reports it as an error while still updating the others: the
copy it would write omits those statements, and once such a copy exists the
`require_expected: false` skip no longer applies, so every later drift run
would report a challenge that states nothing as current.

The regeneration guard and the LDT preservation regression answer different
questions.  Regeneration checks that the fixture agrees with the current
library.  `ComparatorChallengeDriftTests.test_ldt_expected_matches_baseline`
also hashes `expected/Challenge.lean.expected` and requires the preserved LDT
digest
`e2680bf19bc3680b73356822b9d8dd84ce73304541a720cc7e83a680463c698b`.
Consequently, a QPBT-only change cannot silently update both the library and the
generated LDT fixture.

The module-conversion pilot changed the previous digest only because the
`FiniteMatrix` module and public-section headers shifted two generated source
line comments. The LDT challenge declarations and target statement were
unchanged.

For an intentional future LDT change, first regenerate from fresh built
metadata, audit the exact fixture diff, and verify it in LDT-comparator.  Then
update `LDT_BASELINE_SHA256` in
`scripts/tests/test_comparator_challenge_drift.py` explicitly in the same
reviewed change, with the mathematical reason for changing the LDT closure.

To generate a challenge somewhere else without touching the checked-in copy —
the usual loop while filling in a new challenge's context tables:

```sh
python3 scripts/comparator/check_challenge_drift.py --root . \
    --challenge qpbt --write /tmp/Challenge.lean
```

The update command performs the extraction and assembly pipeline below in a
temporary directory; the same steps run by hand, shown here for the QPBT
challenge, reproduce the same file:

```sh
# 1. render the extractor with this challenge's own import block.  A Lean module
#    header cannot be computed at elaboration time, so the checked-in
#    extract_closure.lean carries the LDT import block and every consumer
#    substitutes the challenge's `imports` into a copy of it; run unrendered on
#    a QPBT target it fails with "target not found", because no LDT module
#    imports QPBT.
python3 - <<'PY' > extract_closure_qpbt.lean
import sys
sys.path.insert(0, "scripts/comparator")
from challenge_config import load_challenges
from check_challenge_drift import EXTRACTOR, render_extractor
(challenge,) = load_challenges(["qpbt"])
sys.stdout.write(render_extractor(challenge, EXTRACTOR.read_text(encoding="utf-8")))
PY

# 2. extract the closure of the challenge's target statements (a Lean
#    metaprogram mirroring comparator's runForUsedConsts traversal).  The
#    targets reach the extractor in MIPSTARRE_COMPARATOR_TARGETS; with that
#    variable unset it closes the LDT main theorem:
MIPSTARRE_COMPARATOR_TARGETS="MIPStarRE.QPBT.pauli_soundness,MIPStarRE.QPBT.pauli_soundness_qubit,MIPStarRE.QPBT.exists_spcc_value_one,MIPStarRE.QPBT.exists_ld_soundness" \
  lake env lean extract_closure_qpbt.lean > closure.tsv
awk -F'\t' 'NF==4 || NF==5' closure.tsv > closure.clean.tsv

# 3. assemble the challenge body (topological order, namespace handling)
# `qpbt` is split, so the assembler writes a directory:
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv \
    --challenge qpbt --split-dir scripts/comparator/expected/qpbt
```

For the LDT challenge step 1 is a no-op — the checked-in extractor already
carries that challenge's import block — so `lake env lean
scripts/comparator/extract_closure.lean` with no environment variable set is
step 2 of the LDT pipeline as it stands.

Then copy the expected file, or the QPBT `Challenge.lean` and `Challenge/`
tree, into the matching comparator repository. Bump the `rev` pin in its
`lakefile.toml` and `lake-manifest.json` to the library commit from which it was
generated, and run its `./verify.sh` (its CI also runs on every push).

Comparator verification status is maintained in `docs/comparator.md`, including
the exact four-target run, merged-main library pin, real-landrun and nanoda
evidence, and trust qualifications.  This operational README documents
generation and deliberately does not duplicate mutable acceptance status.

## Maintenance notes

- A challenge's `extras`/`module_preludes` tables carry elaboration context
  (attribute commands, `CoeFun` instances, `variable`/`open` blocks) that the
  kernel closure cannot see.  Extend them if regeneration produces compile
  errors in that challenge's `Challenge.lean`; the assembler fails loudly if one
  of the challenge's own table keys no longer matches any extracted
  declaration.  The tables are per challenge, so an LDT key never constrains the
  QPBT closure or the other way round.
- A `module_preludes` entry is one scope, or a list of scopes each covering a
  line range (`first`/`last`) of its module: a module needs one scope per source
  section whose context differs.  A scope opened with `noncomputable section` in
  the source is marked `"noncomputable": true`, because the definitions inside
  such a section carry no `noncomputable` keyword of their own.
- The target statements in each footer mirror the theorems in the library:
  `challenge_footer.lean` mirrors
  `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`, and
  `challenge_qpbt_footer.lean` mirrors
  `MIPStarRE/QPBT/Test/Completeness.lean`,
  `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean`,
  `MIPStarRE/QPBT/Test/Soundness.lean`, and
  `MIPStarRE/QPBT/Test/QubitForm.lean`.  If a library statement changes, update
  the footer too - comparator fails with "theorem statement do not match" until
  the two agree.
- Declarations without a source range (compiler-generated congruence lemmas
  and `autoParam` helpers) are emitted as explanatory comments; they
  regenerate identically during elaboration of the challenge file.
- `extract_closure.lean` is an executable tracked Lean source.  The final
  dynamic source inventory in module-conversion packet #753 must include it and
  give it the module header required by that packet; it is not exempt merely
  because it is a generator rather than a library module.
- A configured header or footer file that is not in the tree is reported and
  omitted, so a challenge under development can be generated before its footer
  exists.  That omission is confined to `--write`: `--update` refuses such a
  challenge rather than checking in a copy without that part.
- A closure declaration cannot be `private`: a private name is qualified by its
  defining module, so the challenge file could never re-declare it under the
  library's name.  Closure members found to be private are made public in the
  library (see `docs/comparator.md`, "Environment alignment").


## Split (multi-module) challenges

A challenge whose JSON configuration sets `"split": true` is generated as one
Mathlib-only module per contributing library module instead of one file:

```
python3 scripts/comparator/assemble_challenge.py <closure.tsv> \
    --root . --challenge qpbt --split-dir <out>
```

`<out>/Challenge.lean` imports the parts under `<out>/Challenge/<library
path>.lean` and carries the header and the `sorry`-ed target statements; each
part imports Mathlib plus the mirrors of the library modules its source module
imports.  The layout is what makes Lean generate the same auxiliary
declarations, under the same names, as the library — see the "environment
alignment" section of `docs/comparator.md`.  The checked-in copy is a
directory, and `check_challenge_drift.py --challenge <name> [--update]`
compares or rewrites the whole tree.
