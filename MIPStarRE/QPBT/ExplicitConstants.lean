module

public import MIPStarRE.QPBT.Test.PauliBasisTest

/-!
# Explicit constants for the Pauli basis test

This module records the closed numerical witnesses obtained by following the
current quantitative proof of Pauli-basis-test soundness.  They are Lean-only
quantitative auxiliaries for the source theorem `thm:pauli`; no hypothesis or
conclusion of that theorem is changed.

## References

The proof follows `lem:qld-unitary` and the final isometry argument in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The fixed point-observable commutator coefficient. -/
def pauliBaselineCommutatorConstant : ℝ :=
  1024 * (172 + Real.sqrt 344)

/-- The fixed two-sided twisted-commutator coefficient. -/
def pauliBaselineTwistedConstant : ℝ :=
  2 * (2 * pauliBaselineCommutatorConstant + 4886363136 + 4)

/-- The coefficient of the combined-point error `ε^(1/8)`. -/
def pauliBaselinePointConstant : ℝ :=
  10560 * (344 + 3 * pauliBaselineTwistedConstant) +
    24 * pauliBaselineTwistedConstant + 11008

/-- The fixed combined-point error function. -/
def pauliBaselinePointError (ε : ℝ) : ℝ :=
  pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ)

/-- The coefficient of the combined-line error. -/
def pauliBaselineLineConstant : ℝ :=
  115 * (1 + Real.rpow (16 * pauliBaselinePointConstant + 8320) (1 / 8 : ℝ)) + 1

/-- The fixed combined-line error function. -/
def pauliBaselineLineError (ε ratio : ℝ) : ℝ :=
  pauliBaselineLineConstant *
    (Real.rpow ε (1 / 64 : ℝ) + Real.rpow ratio (1 / 4 : ℝ))

/-- The coefficient after constructing the extended-line measurements. -/
def pauliBaselineExtendedLineConstant : ℝ :=
  1 + 6 * (Real.sqrt pauliBaselinePointConstant +
    Real.rpow pauliBaselineLineConstant (1 / 4 : ℝ) +
    Real.rpow pauliBaselinePointConstant (1 / 4 : ℝ) + 1)

/-- The fixed extended-line error function. -/
def pauliBaselineExtendedLineError (ε ratio : ℝ) : ℝ :=
  pauliBaselineExtendedLineConstant *
    (Real.rpow ε (1 / 256 : ℝ) + Real.rpow ratio (1 / 16 : ℝ))

/-- The coefficient in the direct-game passing envelope. -/
def pauliBaselinePassingConstant : ℝ :=
  4 + 3 * Real.sqrt
    (pauliBaselinePointConstant + pauliBaselineExtendedLineConstant)

/-- The fixed direct-game passing error function. -/
def pauliBaselinePassingError (ε ratio : ℝ) : ℝ :=
  pauliBaselinePassingConstant *
    (Real.rpow ε (1 / 512 : ℝ) + Real.rpow ratio (1 / 32 : ℝ))

/-- The one-coordinate direct low-degree coefficient used by the current proof. -/
def pauliBaselineLowDegreeConstant : ℝ := 2500000000

/-- The one-coordinate direct low-degree power used by the current proof. -/
def pauliBaselineLowDegreePower : ℝ := 1 / 80000

/-- The scalar coefficient before the final projective-rounding absorption. -/
def pauliBaselineGlobalAbsorptionConstant : ℝ :=
  2 * (pauliBaselineLowDegreeConstant *
      (4 : ℝ) ^ pauliBaselineLowDegreeConstant *
        (Real.rpow pauliBaselinePassingConstant pauliBaselineLowDegreePower + 2) +
      Real.sqrt pauliBaselinePointConstant + 1) +
    pauliBaselineLowDegreeConstant +
    (33 / 32) * pauliBaselineLowDegreePower + 3

/-- The power before the eighth-root projective-rounding loss. -/
def pauliBaselineGlobalAbsorptionPower : ℝ := 1 / 40960000

/-- The coefficient of the rounded global-pair error. -/
def pauliBaselineGlobalPairConstant : ℝ :=
  1024 * pauliBaselineGlobalAbsorptionConstant

/-- The power of the rounded global-pair error. -/
def pauliBaselineGlobalPairPower : ℝ := 1 / 327680000

/-- The maximum coefficient needed by the current extraction construction. -/
def pauliBaselineExtractionConstant : ℝ := 2800

/-- The common projective-setting soundness coefficient. -/
def pauliBaselineProjectiveConstant : ℝ :=
  16 * pauliBaselineExtractionConstant ^ (2 : ℕ) *
    pauliBaselineGlobalPairConstant

/-- The common projective-setting soundness power. -/
def pauliBaselineProjectivePower : ℝ :=
  pauliBaselineGlobalPairPower / 16

/-- The coefficient in the explicit arbitrary-strategy Pauli soundness baseline. -/
def pauliSoundnessBaselineConstant : ℝ :=
  346 * 21 ^ (3 : ℕ) * pauliBaselineProjectiveConstant ^ (4 : ℕ)

/-- The power in the explicit arbitrary-strategy Pauli soundness baseline. -/
def pauliSoundnessBaselinePower : ℝ := 1 / 5242880000

end

end MIPStarRE.QPBT
