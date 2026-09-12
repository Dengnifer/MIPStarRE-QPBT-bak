import MIPStarRE.QPBT.Combining.OverlapGap

/-!
# Projection complements and ordered-product errors

This module gives an operator estimate for the point-evaluation comparison in
the combining argument. It keeps squared errors before any scalar majorization.

## References

This is a formalization-only auxiliary for the comparison in paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`,
near blueprint `lem:claim-17-3`. It does not construct extended-line measurements
or discharge the error contract in `lem:qld-4-13`; see issue #510.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

private theorem gram_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) :
    (A + B)ᴴ * (A + B) ≤ Aᴴ * A + Aᴴ * A + Bᴴ * B + Bᴴ * B := by
  apply Matrix.le_iff.mpr
  have heq : Aᴴ * A + Aᴴ * A + Bᴴ * B + Bᴴ * B - (A + B)ᴴ * (A + B) =
      (A - B)ᴴ * (A - B) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
    noncomm_ring
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self (A - B)

/-- The complement of a projection is controlled by a second projection and
an operator whose adjoint has range in the first projection. In the point
comparison, `W` is an ordered product ending in `R`. This operator inequality
uses squared errors and introduces no square root. It is an auxiliary for
paper `claim:17-3`, not an additional hypothesis of `lem:qld-4-13`. -/
theorem projection_complement_le_of_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q R W : Op ι) (hQ : IsProj Q) (hR : IsProj R) (hWR : W * R = W) :
    1 - R ≤ (1 - Q) + (1 - Q) +
      (Q - Wᴴ)ᴴ * (Q - Wᴴ) + (Q - Wᴴ)ᴴ * (Q - Wᴴ) := by
  have hQh : Qᴴ = Q := hQ.isSelfAdjoint.isHermitian.eq
  have hRh : Rᴴ = R := hR.isSelfAdjoint.isHermitian.eq
  have hRW : R * Wᴴ = Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, hRh] using congrArg Matrix.conjTranspose hWR
  have hsplit : (1 - R) * (1 - Q) + (1 - R) * (Q - Wᴴ) = 1 - R := by
    noncomm_ring [hRW]
  have hgram : (1 - R)ᴴ * (1 - R) = 1 - R := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hRh]
    noncomm_ring [hR.isIdempotentElem.eq]
  have hcontract (A : Op ι) :
      ((1 - R) * A)ᴴ * ((1 - R) * A) ≤ Aᴴ * A := by
    have hle : 1 - R ≤ (1 : Op ι) := sub_le_self _ hR.nonneg
    have h := star_left_conjugate_le_conjugate hle A
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      mul_assoc, ← mul_assoc (1 - R)ᴴ (1 - R), hgram, mul_one] using h
  have hQg : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQh]
    noncomm_ring [hQ.isIdempotentElem.eq]
  have hA := hcontract (1 - Q)
  rw [hQg] at hA
  have hB := hcontract (Q - Wᴴ)
  calc
    1 - R =
        ((1 - R) * (1 - Q) + (1 - R) * (Q - Wᴴ))ᴴ *
          ((1 - R) * (1 - Q) + (1 - R) * (Q - Wᴴ)) := by rw [hsplit, hgram]
    _ ≤ _ := gram_add_le _ _
    _ ≤ _ := add_le_add (add_le_add (add_le_add hA hA) hB) hB

end MIPStarRE.QPBT
