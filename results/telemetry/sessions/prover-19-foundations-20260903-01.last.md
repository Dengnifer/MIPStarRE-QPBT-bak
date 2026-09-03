## What changed

Added [Extraction/Defs.lean](/tmp/mipstarre-19-foundations/MIPStarRE/QPBT/Extraction/Defs.lean) with 19 declarations:

- Heterogeneous extraction block, register, and auxiliary aliases.
- Six-register reassociation and ideal-state shuffles.
- Player, extracted-register, paired-operator, and state placement helpers.
- `bracketOp` and the proved definitional `postprocess_effect_eq_bracketOp` bridge.
- `tauDotProj` with projectivity and completeness obligations.
- `conjBy`, `idealExpState`, and `deltaExtract`.
- Reuses the existing `PlayerSide`, `SixReg`, `place`, `phaseSign`, and canonical `P.model`; no duplicate field, basis, polynomial, or witness interfaces.

Committed as `c867370789ab5c12f4c9a765c98e65d65dd35dd4`:

```text
feat(QPBT/Extraction): add extraction foundations

Addresses #19
```

## Evidence

- `lake env lean MIPStarRE/QPBT/Extraction/Defs.lean`: passed, with only the two expected `sorry` warnings.
- `rg -n "sorry|axiom"`: `sorry` at lines 214 and 226; no axioms.
- Forbidden bypass/debug token scan: clean.
- Maximum line-length scan: clean.
- `git diff --check`: passed.
- Pre-commit integrity hooks: passed.
- Worktree is clean and branch is ahead by one commit.
- Full `lake build` skipped because this isolated file is intentionally not re-exported; the direct Lean check exercises the complete unit.

## Statement integrity

Paper assumptions: admissible parameters, canonical fixed field model, Pauli basis `W`, register vector `u`, and scalar `a`.

Lean assumptions: the same data through `AdmissibleParams`, including its fixed model and finite decidable carriers.

Paper conclusion: `tauDotProj` is the dot-product coarse-graining of the Pauli projectors, and the resulting family is projective and complete.

Lean conclusion: exactly `IsProj (tauDotProj W u a)` and  
`∑ a, tauDotProj W u a = 1`.

Verdict: exact, with faithful finite-type boundary instances.

## Open obligations

- `tauDotProj_isProj`: prove that sums over fibers of the mutually orthogonal Pauli projectors are projectors.
- `sum_tauDotProj_eq_one`: prove fiberwise completeness from completeness of the generalized-Pauli projector family.

Both are faithful Stage 4.2 obligations tracked by issue #19. No paper-gap note was added because these are proof holes, not source discrepancies.

## Handoff

Review the heterogeneous register shuffles and the Alice/Bob cases of `placeSide` and `placeExtractedRegister` first. The next prover session can add the issue #18 witness-dependent marginals, pulled-apart measurements, observables, and swap unitaries on top of this file.