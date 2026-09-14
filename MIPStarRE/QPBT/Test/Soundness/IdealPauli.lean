import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Test.Soundness.CompressionBounds

/-!
# Ideal Pauli readouts and EPR transposition

The transpose of an operator on one half of the EPR state acts on the opposite
half. The fixed field model's Pauli projectors satisfy their proved transpose
identity, so no additional field or range hypothesis is needed here.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`;
EPR definition at `04_preliminaries.tex:946-955`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus MagicSquareRigidity

noncomputable section

variable (P : AdmissibleParams) {ιA' ιB' : Type}
  [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']

/-- The ideal state has the norm of its auxiliary factor. -/
theorem idealState_norm (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    ‖idealState P aux‖ = ‖aux‖ := by
  have heq : idealState P aux =
      reindexState prodShuffle.symm (vecTensor aux (eprState (PauliRegister P))) := rfl
  rw [heq, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, mul_one]

/-- Alice's ideal projector is the Pauli projector on her extracted register. -/
theorem pauliProjOnA_eq_tensor (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron (heteroKron 1 (pauliProj W h)) 1 := by
  ext i j
  simp [pauliProjOnA'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

/-- Bob's ideal projector is the Pauli projector on his extracted register. -/
theorem pauliProjOnB_eq_tensor (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron 1 (heteroKron 1 (pauliProj W h)) := by
  ext i j
  simp [pauliProjOnB'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

/-- Transpose transport on the EPR factor, with an arbitrary auxiliary state.
The transpose is retained explicitly for a general complex matrix. -/
theorem idealState_transpose (aux : EuclideanSpace ℂ (ιA' × ιB'))
    (M : Op (PauliRegister P)) :
    applyOperatorToState (heteroKron (heteroKron 1 M) 1) (idealState P aux) =
      applyOperatorToState (heteroKron 1 (heteroKron 1 Mᵀ)) (idealState P aux) := by
  ext p
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker, Matrix.one_apply,
    idealState, eprState, Fintype.sum_prod_type, mul_comm]

/-- The actual Pauli labels in the fixed field model satisfy same-label EPR
transport by the proved `pauliProj_transpose` identity. No reality premise or
additional characteristic restriction is assumed. -/
theorem idealState_pauli_mirror (aux : EuclideanSpace ℂ (ιA' × ιB'))
    (W : PauliKind) (h : PauliRegister P) :
    applyOperatorToState (pauliProjOnA'' P W h) (idealState P aux) =
      applyOperatorToState (pauliProjOnB'' P W h) (idealState P aux) := by
  rw [pauliProjOnA_eq_tensor, pauliProjOnB_eq_tensor]
  simpa only [pauliProj_transpose] using idealState_transpose P aux (pauliProj W h)

private def idealPauliMeasurement (W : PauliKind) :
    Measurement (PauliRegister P) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliProj W) (fun h => (posSemidef_pauliProj W h).nonneg)
    (sum_pauliProj_eq_one W)

/-- Alice's complete ideal Pauli family is a summed-square contraction. -/
theorem pauliProjOnA_sum_adjoint_mul_le_one (W : PauliKind) :
    ∑ h, (pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnA'' P W h ≤ 1 := by
  simp only [pauliProjOnA_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (leftPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))

/-- Bob's complete ideal Pauli family is a summed-square contraction. -/
theorem pauliProjOnB_sum_adjoint_mul_le_one (W : PauliKind) :
    ∑ h, (pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnB'' P W h ≤ 1 := by
  simp only [pauliProjOnB_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (rightPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))

end

end MIPStarRE.QPBT
