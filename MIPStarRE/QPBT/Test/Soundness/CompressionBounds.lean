import MIPStarRE.QPBT.Test.Soundness.RangeProjection

/-!
# Two-sided compression estimates

The two-sided compression of an operator family is controlled by its original
error and the distance to the range of an orthogonal projection. An opposite
register transpose family controls the second range projection on an EPR state.

## References

Formalization-only estimates supporting paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
See `docs/paper-gaps/qpbt_extraction-transfer.tex` and issue #529.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

/-- Isometry conjugation carries an orthogonal projection to an orthogonal
projection on the image of its range. -/
theorem isProj_conjIsometry {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {Q : Op ι} (hQ : IsProj Q) : IsProj (conjIsometry φ Q) := by
  constructor
  · change conjIsometry φ Q * conjIsometry φ Q = conjIsometry φ Q
    rw [conjIsometry_mul, hQ.isIdempotentElem.eq]
  · change star (conjIsometry φ Q) = conjIsometry φ Q
    simp [conjIsometry_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

/-- Left placement preserves a summed-square contraction, without completeness. -/
theorem left_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (N a) (1 : Op κ))ᴴ * heteroKron (N a) 1 ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.leftTensor (ι₂ := κ) (N a))ᴴ *
    MIPStarRE.LDT.leftTensor (N a) ≤ 1
  have h := MIPStarRE.LDT.leftTensor_mono (ι₂ := κ) hN
  simpa only [← MIPStarRE.LDT.leftTensor_finset_sum,
    MIPStarRE.LDT.leftTensor_one, MIPStarRE.LDT.leftTensor_conjTranspose,
    MIPStarRE.LDT.leftTensor_mul_leftTensor] using h

/-- Right placement preserves a summed-square contraction, without completeness. -/
theorem right_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op κ) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (1 : Op ι) (N a))ᴴ * heteroKron 1 (N a) ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.rightTensor (ι₁ := ι) (N a))ᴴ *
    MIPStarRE.LDT.rightTensor (N a) ≤ 1
  have h := MIPStarRE.LDT.rightTensor_mono (ι₁ := ι) hN
  simpa only [← MIPStarRE.LDT.rightTensor_finset_sum,
    MIPStarRE.LDT.rightTensor_one, MIPStarRE.LDT.rightTensor_conjTranspose,
    MIPStarRE.LDT.rightTensor_mul_rightTensor] using h

/-- Isometry conjugation preserves the summed-square contraction bound.
The resulting family need not sum to the identity on the enlarged space. -/
theorem sum_conjIsometry_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) ≤ 1 := by
  have heq (a : α) : (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) =
      isometryMatrix φ * ((N a)ᴴ * N a) * (isometryMatrix φ)ᴴ := by
    simp only [conjIsometry_eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (isometryMatrix φ)ᴴ (isometryMatrix φ),
      isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  simp_rw [heq]
  have hsum : (∑ a, isometryMatrix φ * ((N a)ᴴ * N a) * (isometryMatrix φ)ᴴ) =
      isometryMatrix φ * (∑ a, (N a)ᴴ * N a) * (isometryMatrix φ)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [hsum]
  calc
    _ ≤ isometryMatrix φ * (1 : Op ι) * (isometryMatrix φ)ᴴ := by
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hN).mul_mul_conjTranspose_same (isometryMatrix φ) using 1
      simp [Matrix.mul_sub, Matrix.sub_mul]
    _ ≤ 1 := by
      rw [Matrix.mul_one]
      exact isometryMatrix_mul_conjTranspose_le_one φ

private theorem norm_add_three_sq_le {ι : Type*} [Fintype ι]
    (x y z : EuclideanSpace ℂ ι) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (show ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ from norm_add₃_le) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

private theorem apply_sub_operator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (A - B) v =
      applyOperatorToState A v - applyOperatorToState B v := by
  simp [applyOperatorToState]

/-- Two-sided compression costs three times the original squared family error
and six times the squared state error. The mirror relation is only on the
comparison vector; no range assumption is imposed on that vector. -/
theorem sum_norm_compression_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T R : α → Op ι) (Q : Op ι) (hQ : IsProj Q)
    (hN : ∑ a, (N a)ᴴ * N a ≤ 1) (hR : ∑ a, (R a)ᴴ * R a ≤ 1)
    (theta delta : EuclideanSpace ℂ ι)
    (hfix : applyOperatorToState Q theta = theta)
    (hmirror : ∀ a, applyOperatorToState (T a) delta = applyOperatorToState (R a) delta)
    (hcomm : ∀ a, Q * R a = R a * Q) :
    ∑ a, ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (∑ a, ‖applyOperatorToState (N a - T a) delta‖ ^ 2) +
        6 * ‖delta - theta‖ ^ 2 := by
  have hcontract (v : EuclideanSpace ℂ ι) :
      ‖applyOperatorToState Q v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    simp [applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from hfix]
  have hrange : ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤ ‖delta - theta‖ ^ 2 := by
    have h := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [applyOperatorToState_sub, hvanish, sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hn := (sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrange
  have hr := (sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrange
  have hpoint (a : α) :
      ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
        3 * (‖applyOperatorToState (N a - T a) delta‖ ^ 2 +
          ‖applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
          ‖applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a =
        Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by
      noncomm_ring
    have hm : applyOperatorToState ((1 - Q) * T a) delta =
        applyOperatorToState (R a * (1 - Q)) delta := by
      rw [applyOperatorToState_mul, hmirror]
      rw [← applyOperatorToState_mul]
      congr 1
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    rw [hs]
    rw [apply_sub_operator, apply_sub_operator]
    rw [hm, applyOperatorToState_mul, applyOperatorToState_mul,
      sub_eq_add_neg, sub_eq_add_neg]
    have h := norm_add_three_sq_le
      (applyOperatorToState Q (applyOperatorToState (N a - T a) delta))
      (-applyOperatorToState Q (applyOperatorToState (N a * (1 - Q)) delta))
      (-applyOperatorToState (R a * (1 - Q)) delta)
    simp only [norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontract _) (hcontract _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

/-- Two summed-square contractions have squared distance at most four on a
unit vector, even when either family is only a submeasurement. -/
theorem sum_norm_sub_sq_le_four {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1)
    (hT : ∑ a, (T a)ᴴ * T a ≤ 1)
    (delta : EuclideanSpace ℂ ι) (hdelta : ‖delta‖ = 1) :
    ∑ a, ‖applyOperatorToState (N a - T a) delta‖ ^ 2 ≤ 4 := by
  have hn := sum_norm_mul_apply_le N 1 delta hN
  have ht := sum_norm_mul_apply_le T 1 delta hT
  simp only [Matrix.mul_one, applyOperatorToState_one, hdelta, one_pow] at hn ht
  have hp (a : α) : ‖applyOperatorToState (N a - T a) delta‖ ^ 2 ≤
      2 * (‖applyOperatorToState (N a) delta‖ ^ 2 +
        ‖applyOperatorToState (T a) delta‖ ^ 2) := by
    have h := parallelogram_law_with_norm ℂ
      (applyOperatorToState (N a) delta) (applyOperatorToState (T a) delta)
    rw [apply_sub_operator]
    nlinarith [sq_nonneg ‖applyOperatorToState (N a) delta +
      applyOperatorToState (T a) delta‖]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hp a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  linarith

end MIPStarRE.QPBT
