<!-- scout: scout-palomar-module-scope-20261002-01 2026-10-02 -->
## Mathlib scouting report — 2026-10-02

### Mathematical source
- Palomar’s live submission instructions designate `PalomarPolicy/CONTRIBUTING.md` as binding and collect substantive-repository mappings in submission metadata. citeturn0view0
- `CONTRIBUTING.md` §2.1 applies the leading `module` command and 10,000-physical-line limit to every regular Lean file in both the submitted repository and separately declared substantive repositories. The external-dependency exemption does not apply once that repository is separately declared substantive. Section 3.2 requires a thin wrapper to map its declarations to an immutable substantive source revision. citeturn4view0
- Local evidence identifies QPBT-comparator as the wrapper generated from this repository and names its four target declarations: `scripts/comparator/README.md:3-29` and `docs/comparator.md:78-93`.
- **Verdict:** the requirements unequivocally apply to the complete pinned MIPStarRE-QPBT tree, not only `Challenge.lean`, `Solution.lean`, or `MIPStarRE/QPBT/`.

### Relevant Mathlib definitions
- No Mathlib theorem is involved. Lean’s module system makes declarations private by default, imports private by default, and public definitions irreducible outside their module unless exposed. The official initial porting recipe uses `public import` and `@[expose] public section`; later cleanup can narrow visibility. citeturn8view0
- `import all` is restricted to the same package and requires `allowImportAll`, so a separate QPBT-comparator package cannot use it to bypass missing public API. citeturn8view0

### Relevant Mathlib lemmas and theorems
- None. This is repository and module-scope analysis.

### Relevant MIPStarRE declarations
- Snapshot: `HEAD` = `14c43b47f4eb2bb005666c000f5880b60b400c8a`, dated 2026-10-01, subject `chore(telemetry): Close bounded error-bound report episode`.
- Toolchain at that commit: Lean and Mathlib `v4.32.0`.
- **Tracked regular Lean files:** 742, all mode `100644`; no Lean symlinks.
- Breakdown: 359 under `MIPStarRE/QPBT/`, 330 under `MIPStarRE/LDT/`, 11 under `MIPStarRE/Quantum/`, four root/aggregate files, 37 under `scripts/`, and one under `results/`.
- Total measured size: 251,114 physical lines and 12,064,250 bytes.
- **Valid module headers:** 0. **Files lacking them:** 742.
- The scanner skipped whitespace, `--` comments, and recursively nested `/- … -/` comments before inspecting the first token. Seven raw lines beginning with `module` were found, but all were inside comments.
- 740 files begin with `import`; the two comparator footer fragments begin with `namespace`.
- **Files over 10,000 lines:** 0. No file is exactly 10,000 lines.
- Largest files:
  - 1,000 — `MIPStarRE/QPBT/Combining/ExtendedLineGame/LinePointRejection.lean`
  - 990 — `MIPStarRE/QPBT/Games/StrategyClasses.lean`
  - 986 — `MIPStarRE/QPBT/Games/CondLinearTheorems.lean`
  - 979 — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Transfer.lean`
  - 973 — `MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean`
  - 969 — `MIPStarRE/QPBT/Games/Sandwich/Pasting/Assembly.lean`
  - 967 — `MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean`
  - 962 — `MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean`
  - 952 — `MIPStarRE/LDT/Pasting/Bernoulli/DegreeZero.lean`
  - 947 — `MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean`
- There are 1,942 header import commands across 740 files and zero `public import` commands.
- Five documented aggregate modules contain 214 imports that must remain re-exported unless the public API is intentionally changed: `MIPStarRE.lean` (3), `MIPStarRE/QPBT.lean` (115), `MIPStarRE/LDT.lean` (82), `MIPStarRE/Quantum.lean` (9), and `MIPStarRE/Quantum/FiniteMatrix.lean` (5).
- The registered declarations that must remain public are:
  - `MIPStarRE.QPBT.exists_spcc_value_one` — `MIPStarRE/QPBT/Test/Completeness.lean:267`
  - `MIPStarRE.QPBT.exists_ld_soundness` — `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82`
  - `MIPStarRE.QPBT.pauli_soundness` — `MIPStarRE/QPBT/Test/Soundness.lean:110`
  - `MIPStarRE.QPBT.pauli_soundness_qubit` — `MIPStarRE/QPBT/Test/QubitForm.lean:461`

### Suggested approach
This is a repository-wide module migration, not a line-limit repair. Add `module` to retained Lean sources, initially preserve cross-file behavior with public imports and exposed public sections, then narrow visibility incrementally. Preserve the five aggregate re-export surfaces and make the four registered theorems, together with every declaration occurring in their statement closures, publicly importable.

The 38 non-library Lean artifacts are also in policy scope. In particular, the two comparator footer fragments are not standalone modules; adding `module` directly may break concatenation. They should be generated from non-`.lean` resources or otherwise restructured, with generated expected trees regenerated consistently.

### Gaps to fill
- Minimum measured work: handle 742 module-header failures and classify 1,942 imports.
- Public-declaration and definition-exposure work cannot be counted reliably without compile-driven migration because existing proofs use extensive cross-file declarations and definitional unfolding.
- The time cost is therefore uncertain. No defensible hours estimate follows from the file count; the exact scope is large, but the dominant cost is resolving visibility errors rather than inserting headers.
- No file splitting is required for Palomar’s 10,000-line cap.

### Searched
Read `AGENTS.md`, both committed scout prompts, the owner briefing, Palomar’s live submission page, `PalomarPolicy/CONTRIBUTING.md` §§2.1 and 3.2, Lean’s module-system reference, the repository import roots, comparator documentation, and the four target declarations. Counts came from `git ls-tree -r -z HEAD` plus a byte-level comment-aware scanner. No build, edit, commit, GitHub write, submission, or agent protocol was used. Uncommitted telemetry/submission-note changes appeared concurrently in the worktree and were excluded because all measurements used the immutable `HEAD` tree.