# Lean Module Conversion Pattern

This note records the module-system pattern verified on the
`MIPStarRE/Quantum/FiniteMatrix/` pilot under Lean and Mathlib v4.35.0-rc2. The
conversion preserves declaration names, types, bodies, proofs, unfolding, and
aggregate re-exports.

The rules below follow the Lean v4.32 sources in `Lean/AddDecl.lean` for
`@[expose]`, `Lean/Parser/Command.lean` for meta imports, and
`Lean/Environment.lean` for module import levels. Mathlib's
`Mathlib/SetTheory/Cardinal/Defs.lean` and `scripts/check-yaml.lean` provide the
corresponding library-leaf and executable patterns.

## Library Leaves

A library leaf begins with `module`, and every existing import becomes a
`public import` so that the old transitive import surface remains available:

```lean
module

public import MIPStarRE.Some.Dependency
```

After the module docstring, the existing declarations are placed in an exposed
public section:

```lean
@[expose] public section
```

Declarations are private by default in a module file. `public section` keeps
the existing declarations public, while `@[expose]` keeps definition bodies
available to module-system importers for unfolding and definitional reduction.
Explicit `private` declarations and `local` instances remain private or local.

## Aggregate Modules

An aggregate that only re-exports leaves needs `module` and `public import`
lines. It needs no public section because it declares nothing:

```lean
module

public import MIPStarRE.Some.FirstLeaf
public import MIPStarRE.Some.SecondLeaf
```

## Meta Code And Executables

Tactics, macros, command elaborators, and other compile-time APIs use
`public meta import` when downstream elaboration needs imported IR, and their
exported declarations belong in `public meta section`. Ordinary runtime
executables are not meta code merely because they inspect Lean syntax or
environments.

`scripts/Checkdecls.lean` therefore uses a private ordinary `import Lean`,
keeps its helper definitions private, and marks only its executable entry point
as `public unsafe def main`. This matches Lean's v4.32 executable pattern and
keeps `lake exe checkdecls` working without exporting implementation helpers.

## Comparator Sources

The comparator assembler must recognize module-header import modifiers when it
reconstructs the local import graph. Its import scanner accepts `public`,
`meta`, and `all` modifiers without copying those modifiers into generated
Mathlib-only challenge modules. Regeneration may update source line numbers in
provenance comments; it must not change challenge declarations or target
statements.

Comparator header and footer files are partial source templates and therefore
use the `.lean.in` suffix. Their bytes are inserted unchanged; the assembler is
responsible for adding module syntax. Split challenge goldens remain runnable
`.lean` files rather than archival `.lean.expected` files: each begins with
`module`, uses `public import`, and places declarations in an
`@[expose] public section`. This keeps the checked fixture identical to the
source compiled by the companion comparator repository.

The closure extractor is compile-time environment inspection. It begins with a
module header, renders each configured dependency as `meta import all`, and
runs in a private `meta section`. The `all` level is required because closure
construction inspects private and compiler-generated declarations as well as
definition values; ordinary imports do not retain that complete environment.

## Mechanical Audit

For the pilot, the following command removes only the module header, public
import modifier, and exposed public section, then byte-compares each
mathematical source with base commit
`97dc6e049b0ce966be18bf8801e14b30c0081919`:

```sh
python3 - 97dc6e049b0ce966be18bf8801e14b30c0081919 \
  MIPStarRE/Quantum/FiniteMatrix.lean \
  MIPStarRE/Quantum/FiniteMatrix/Basic.lean \
  MIPStarRE/Quantum/FiniteMatrix/BlockDiagonal.lean \
  MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean \
  MIPStarRE/Quantum/FiniteMatrix/Order.lean \
  MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean <<'PY'
from pathlib import Path
import subprocess
import sys

base, *paths = sys.argv[1:]
for path in paths:
    old = subprocess.check_output(["git", "show", f"{base}:{path}"], text=True)
    new = Path(path).read_text(encoding="utf-8")
    new = new.removeprefix("module\n\n")
    new = new.replace("public import ", "import ")
    new = new.replace("\n@[expose] public section\n", "")
    if new != old:
        raise SystemExit(f"FAIL {path}")
    print(f"PASS {path}")
PY
```

The verified result is one `PASS` line for each of the six files. Thus every
mathematical declaration statement and body is byte-identical after removing
the module and visibility syntax. All estimates and bounds are unchanged.

## Validation Order

1. Run `lake env lean` on converted leaves in import order.
2. Build each converted dependency target before checking a converted module
   that imports it; a source-only Lean check does not replace the cached
   `.olean` header.
3. Build and run converted executables independently.
4. Import each aggregate from a fresh module-system smoke file and check both
   public names and representative `rfl` unfoldings.
5. Regenerate comparator expectations, review the exact diff, and run the
   repository's normal PR CI once for the full build and axiom audits.

## Complete conversion (2026-10-02)

The complete conversion keeps all existing theorem hypotheses, conclusions,
quantifiers, and numerical bounds. Of the 722 mathematical source files,
665 are byte-identical to the compact-library base after removal of module
headers, public imports, and exposed public sections. The remaining 57 were
inspected individually: they export helper definitions used in exposed bodies,
mark metaprograms as meta, balance visibility sections, or place existing proof
terms inside `by exact` blocks so elaboration can use private proof data.
No mathematical assumption or estimate changes.

The historical PR549 native-check transcript is retained byte-for-byte as
`.lean.txt`; it is an archived diagnostic, not a current build target. Comparator
header/footer fragments similarly use `.lean.in`, while generated compilable
mirrors use real module headers. Historical JSONL captures are stored as gzip
or XZ archives to meet the source snapshot size limit. Each adopted archive was
decompressed and compared byte-for-byte with the current raw capture before
replacement. The telemetry reader accepts both representations.

Validation: the full `lake build` and `lake build MIPStarRE.QPBT.Test.AxiomAudit`
pass on Lean/Mathlib v4.35.0-rc2. All four original headlines, their compact
aliases, and the fixed-field selector have only the three standard axioms.
