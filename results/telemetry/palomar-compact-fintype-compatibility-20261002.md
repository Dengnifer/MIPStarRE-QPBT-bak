# Palomar compact finite-enumeration compatibility, 2026-10-02

Issue #774 was repaired from local base
`2b6606fbf0c4b3530d9ed9ebb60525a3193c1377`.  No sub-session was started and
no prior author or review cost was reset.

## Source repair

Only the two failing generated finite enumerations changed in
`MIPStarRE/QPBT/Palomar/Definitions.lean`:

- `instFintypeLowDegreeType` now explicitly enumerates
  `{.point, .aline, .dline}`.
- `instFintypePauliKind` now explicitly enumerates `{.X, .Z}`.

The existing root instance names and constructor sets are preserved.  No game
carrier, verifier branch, quantifier, field contract, error, or bound changed.

## Regenerated artifact

The checked-in Challenge was regenerated from fresh compiled metadata with
`check_challenge_drift.py --challenge palomar --update`.

- Before: SHA-256
  `4600b1c3e2409edf2a68df53a2055516c99646e42750f966cf02e60437700de3`,
  992 physical lines, and 52,483 UTF-8 bytes.
- After: SHA-256
  `acb66991fbdbc80a9c5d0a7e522f572ba604e6c88b2907f9c43a477438ebe6f8`,
  989 physical lines, and 51,979 UTF-8 bytes.
- Delta: three fewer lines and 504 fewer bytes.

The complete generated diff has four localized hunks.  The two declaration
hunks replace derived `Fintype` with the explicit instances above.  The
provenance header drops only seven now-unreachable generated-enumeration rows:
the two `enumList` values, both `enumList_nodup` proofs, both
`enumList_getElem?_ctorIdx_eq` proofs, and the associated private generated
helper.  No other generated declaration changed.

## Statement and axiom identity

- The complete `FixedFieldModel` contract together with the registered
  `fixedFieldModel` signature is identical before and after; normalized block
  SHA-256: `f5eae490e9fec64712244e7e62d68ee1ae2febbf5f802c5614339299ddfea8c4`.
- The concatenated complete headers of `exists_spcc_value_one`,
  `exists_ld_soundness`, `pauli_soundness`, and `pauli_soundness_qubit` are
  identical; SHA-256:
  `e6735c8be85920568dddad577d22445f3a2999f3f9deb58004d5e63c151b0928`.
- The artifact still contains exactly five intended `sorry` bodies, one for
  the registered definition and four for the headline theorems, and declares
  no axiom.
- The focused QPBT axiom-audit build passed.  Each compact theorem alias and
  the actual `fixedFieldModel` value uses exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Compiler checks

- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`:
  standalone Challenge check exited 0 with only the five intended warnings.
- Lean 4.35.0-rc2, commit `11acb17ec6b07a8f9e9173e6845197929540936b`,
  with Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`: the read-only standalone
  check from issue #756's pinned worktree exited 0 with the same five warnings.

Renewed final faithfulness assessment is pending for the new artifact hash;
approval tied to the prior hash does not carry over.  Final supported-library
integration, native comparison, canonical CI, and independent whole-stack
review also remain pending.
