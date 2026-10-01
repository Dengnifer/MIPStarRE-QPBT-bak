<!-- scout: scout-palomar-packet-map-20261002-01 2026-10-01 -->
## Mathlib scouting report — 2026-10-01

### Mathematical source
- This is mechanical dependency analysis, not a mathematical formalization task.
- Authority: owner briefing `briefing-palomar-20261001.md` §8 and current `HEAD` `97dc6e049b0ce966be18bf8801e14b30c0081919`.
- The attached task supplied no issue number. GitHub issue access was unavailable in the restricted sandbox.
- Effective toolchain is Lean/Mathlib v4.32.0, as pinned by `lean-toolchain` and `lakefile.toml`.

### Relevant Mathlib patterns
- `module`, `public import`, `@[expose] public section` — `Mathlib/Logic/Basic.lean:6-25`.
- `public meta import`, `public meta section` — `Mathlib/Tactic/Basic.lean:6-26`.
- Mathlib’s header linter identifies imports by parser syntax kind, not text regex — `Mathlib/Tactic/Linter/Header.lean`.

### Current graph
- 742 tracked Lean files: 704 under `MIPStarRE`, 37 under `scripts`, 1 telemetry artifact.
- Classification: 704 library sources, 31 generated Challenge modules, 3 standalone script/audit sources, and 4 nonstandalone comparator fragments.
- Parsed 1,942 imports: 1,849 tracked-local edges and 93 external imports.
- Every `MIPStarRE.*` and `Challenge.*` import resolves. No self-edge or file-level cycle exists; all 742 file SCCs are singletons. Maximum local-import rank is 123.
- Coarse directory grouping creates two large artificial SCCs:
  - 305 files across `LDT/{Commutativity,CommutativityPoints,ExpansionHypercubeGraph,GlobalVariance,MainInductionStep,MakingMeasurementsProjective,Pasting,Preliminaries,SelfImprovement,Tactic,Test}`.
  - 323 files across `QPBT/{Algebra,Combining,Extraction,Observables,Test}` plus `QPBT/ExplicitConstants.lean`.
- `QPBT/Games` also forms a 35-file coarse subdirectory SCC. These are directory-grouping cycles only.
- `MIPStarRE/Quantum/ControlledUnitary.lean` imports `QPBT/Games/DistanceTheorems/Support.lean`; it cannot belong to an initial all-Quantum packet.

### Packet plan
For exact ownership, define `r(f) = 0` when `f` has no tracked local import, otherwise `1 + max r(dependency)`, over the current `MIPStarRE` file DAG. The following assignment was checked to cover all 742 paths exactly once with zero forward dependency edges.

| Packet | Size | Exact ownership | Prerequisite |
|---|---:|---|---|
| P0 pilot | 7 | `Quantum/FiniteMatrix/*.lean` (5), `Quantum/FiniteMatrix.lean`, `scripts/Checkdecls.lean` | none |
| P1 foundation/LDT-1 | 142 | `LDT/Basic/*.lean`; the five nonpilot Quantum files other than `ControlledUnitary`; remaining LDT files with `r=0..20` | approved P0 |
| P2 LDT-2 | 109 | remaining LDT files with `r=21..33` | P1 |
| P3 LDT-3 | 85 | remaining LDT files with `r=34..81`, including `MIPStarRE/LDT.lean` | P2 |
| P4 QPBT-1 | 110 | QPBT/late set with `r=0..35`, including `QPBT/State.lean` and `Quantum/ControlledUnitary.lean` | P3 |
| P5 QPBT-2 | 110 | QPBT/late set with `r=36..82` | P4 |
| P6 QPBT-3 | 104 | QPBT/late set with `r=83..105` | P5 |
| P7 QPBT-4 | 38 | QPBT/late set with `r=106..123`, including `QPBT.lean` and `MIPStarRE.lean` | P6 |
| P8 generated/tools | 37 | 31 `scripts/comparator/expected/qpbt/**/*.lean`; four challenge fragments; `extract_closure.lean`; telemetry harness | P7 |

Here “QPBT/late set” means every file under `MIPStarRE/QPBT`, plus `MIPStarRE/QPBT.lean`, `MIPStarRE/Quantum/ControlledUnitary.lean`, and `MIPStarRE.lean`.

### Source hazards
- The four fragments `challenge_{header,footer}.lean` and `challenge_qpbt_{header,footer}.lean` are concatenated inputs. Footer files have no imports and cannot blindly receive standalone `module` headers. P8 must either rename them away from `.lean` or make assembly retain exactly one module header.
- The 31 expected Challenge files mirror module boundaries to preserve generated auxiliary names. Update the generator before regenerating them, after the library visibility pattern is final.
- Meta-sensitive files: all four `LDT/Tactic/*.lean`, both `LDT/Test/AxiomAudit.lean` and `QPBT/Test/AxiomAudit.lean`, `scripts/Checkdecls.lean`, `scripts/comparator/extract_closure.lean`, and the telemetry harness. They require deliberate `meta`/`public meta` treatment.
- The telemetry harness is historical evidence and defines a command elaborator; do not rewrite it mechanically without resolving its evidence-retention status.
- A raw `^import` scan is unsafe: `MIPStarRE/Quantum/FiniteMatrix.lean:11` contains an import-looking docstring line.

### Scanner updates
P8 should own these narrow compatibility changes, not a new workflow layer:

- `scripts/comparator/check_challenge_drift.py:38` — plain-import-only leading-block regex.
- `scripts/comparator/assemble_challenge.py:96-101,236-310` — plain import parser and generated headers.
- `scripts/comparator/challenge_config.py:136-137` — extractor header generation.
- `scripts/make_artifact.sh:445` — recognizes only `^import MIPStarRE`.
- Associated tests in `test_comparator_challenge_config.py`, `test_comparator_challenge_drift.py`, and `test_assemble_challenge.py`.

### Suggested minimal all-source scan
Use one comment/string-aware header scanner over `git ls-files '*.lean'`. It should recognize `module`, optional `public`/`meta` import modifiers, resolve both library and Challenge module roots, run SCC/rank checks, emit `packet<TAB>rank<TAB>path`, and assert: 742 assigned paths, no unresolved local import, no forward packet edge, and a `module` first command for every standalone source. Treat the four fragments through an explicit exception or rename policy.

### Searched
- All 742 tracked Lean files and their import headers.
- Current Mathlib module/public/meta examples.
- Comparator generation, drift tests, artifact packaging, tactics, axiom audits, executable scripts, generated expected sources, and telemetry Lean artifacts.
- No files were edited and no build or Lean compilation was run; the worktree remains clean.