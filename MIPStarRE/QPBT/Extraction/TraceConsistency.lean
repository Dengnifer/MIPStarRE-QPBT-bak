import MIPStarRE.QPBT.Extraction.Observables
import MIPStarRE.QPBT.Observables.WinImplications.FactorTransport

/-!
# Trace postprocessing of the pulled-apart measurements

The binary trace map converts consistency of the pulled-apart measurements
into state-dependent distance of their observables, with a constant independent
of the field size. This calculation does not establish the preceding
pulling-consistency estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1550-1554`,
  the trace-postprocessing step in `lem:qld-construct-the-paulis`.
- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- Issue #520.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- The complete measurement with effects `tildeM`, from `eq:tilde_M` in
paper `14_analysis_of_the_pauli_basis_test.tex:1425-1435`. -/
def tildeMeasurement {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    Measurement (PauliScalar P) (ExtractionBlock P (S.LocalSpace side)) :=
  Measurement.ofSumEqOne (tildeM w side W u)
    (fun a => (tildeM_isProj w side W u a).nonneg)
    (sum_tildeM_eq_one w side W u)

/-- Regrouping the field outcomes by their binary trace recovers the
observable in `eq:def-tildewj`; no estimate or consistency premise is used. -/
theorem tildeObs_eq_trace_postprocess {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim) :
    tildeObs w side W u j =
      ∑ b : ZMod 2, phaseSign b •
        ((tildeMeasurement w side W u).postprocess
          (fun a => fixedBinTrace P.model (P.model.basis j * a))).effect b := by
  classical
  simp only [Measurement.postprocess_effect, Finset.smul_sum]
  calc
    _ = ∑ b : ZMod 2, ∑ a ∈ Finset.univ.filter
        (fun a => fixedBinTrace P.model (P.model.basis j * a) = b),
        phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
          tildeM w side W u a :=
      (Finset.sum_fiberwise Finset.univ
        (fun a => fixedBinTrace P.model (P.model.basis j * a))
        (fun a => phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
          tildeM w side W u a)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
      rfl

/-- Trace postprocessing bounds the observable distance by four times the
measurement inconsistency. This is the last step of
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1550-1554`, with its constant explicit.
It holds for any distribution of Pauli registers and any six-register state;
the pulling-consistency bound remains a separate obligation in issue #520. -/
theorem tildeObs_opDistSq_le_four_mul_consistencyDefect
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (j : Fin P.model.basisDim)
    (μ : Distribution (PauliRegister P))
    (ψ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    opDistSq μ
        (fun u => S.placeSide .alice (tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (tildeObs w .bob W u j)) ψ ≤
      4 * consistencyDefect μ
        (fun u a => S.placeSide .alice (tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (tildeM w .bob W u a)) ψ := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  let χ := reindexState e ψ
  let f : PauliScalar P → ZMod 2 :=
    fun a => fixedBinTrace P.model (P.model.basis j * a)
  let A := fun u => (tildeMeasurement w .alice W u).postprocess f
  let B := fun u => (tildeMeasurement w .bob W u).postprocess f
  let LA : PauliRegister P → Measurement (ZMod 2)
      (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    fun u => leftPlacedMeasurement (A u)
  let RB : PauliRegister P → Measurement (ZMod 2)
      (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    fun u => rightPlacedMeasurement (B u)
  have hobs := povm_to_obs_of_measurements μ LA RB phaseSign WinImplications.norm_phaseSign χ
  have hdist := opFamilyDistSq_le_two_mul_consistencyDefect μ LA RB χ
  have hpost := consistencyDefect_postprocess_le μ
    (tildeMeasurement w .alice W) (tildeMeasurement w .bob W) χ f
  have hleft (u : PauliRegister P) :
      (∑ b : ZMod 2, phaseSign b • (LA u).effect b) =
        heteroKron (tildeObs w .alice W u j) (1 : Op (ExtractionBlock P S.toStrategy.ιB)) := by
    rw [tildeObs_eq_trace_postprocess, WinImplications.heteroKron_left_sum_smul]
    rfl
  have hright (u : PauliRegister P) :
      (∑ b : ZMod 2, phaseSign b • (RB u).effect b) =
        heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA)) (tildeObs w .bob W u j) := by
    rw [tildeObs_eq_trace_postprocess, WinImplications.heteroKron_right_sum_smul]
    rfl
  simp only [hleft, hright, ZMod.card, Nat.cast_ofNat] at hobs
  have hbound : opDistSq μ
      (fun u => heteroKron (tildeObs w .alice W u j) 1)
      (fun u => heteroKron 1 (tildeObs w .bob W u j)) χ ≤
        4 * consistencyDefect μ
          (fun u a => heteroKron (tildeM w .alice W u a) 1)
          (fun u a => heteroKron 1 (tildeM w .bob W u a)) χ := by
    change opFamilyDistSq μ _ _ χ ≤ 2 * consistencyDefect μ
      (fun u b => heteroKron ((A u).effect b) 1)
      (fun u b => heteroKron 1 ((B u).effect b)) χ at hdist
    change consistencyDefect μ
      (fun u b => heteroKron ((A u).effect b) 1)
      (fun u b => heteroKron 1 ((B u).effect b)) χ ≤ _ at hpost
    change _ ≤ consistencyDefect μ
      (fun u a => heteroKron (tildeM w .alice W u a) 1)
      (fun u a => heteroKron 1 (tildeM w .bob W u a)) χ at hpost
    exact hobs.trans (by
      calc
        _ ≤ 2 * (2 * _) := mul_le_mul_of_nonneg_left hdist (by norm_num)
        _ ≤ 2 * (2 * _) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpost (by norm_num)) (by norm_num)
        _ = _ := by ring)
  have hdistance : opDistSq μ
      (fun u => heteroKron (tildeObs w .alice W u j) 1)
      (fun u => heteroKron 1 (tildeObs w .bob W u j)) χ =
        opDistSq μ
          (fun u => S.placeSide .alice (tildeObs w .alice W u j))
          (fun u => S.placeSide .bob (tildeObs w .bob W u j)) ψ := by
    unfold opDistSq opFamilyDistSq
    apply avgOver_congr
    intro u
    simp only [Fintype.sum_unique]
    change ‖applyOperatorToState
      (heteroKron (tildeObs w .alice W u j) 1 -
        heteroKron 1 (tildeObs w .bob W u j)) (reindexState e ψ)‖ ^ 2 = _
    rw [WinImplications.norm_applyOperatorToState_reindexState]
    rfl
  have hconsistency : consistencyDefect μ
      (fun u a => heteroKron (tildeM w .alice W u a) 1)
      (fun u a => heteroKron 1 (tildeM w .bob W u a)) χ =
        consistencyDefect μ
          (fun u a => S.placeSide .alice (tildeM w .alice W u a))
          (fun u a => S.placeSide .bob (tildeM w .bob W u a)) ψ := by
    unfold consistencyDefect
    apply avgOver_congr
    intro u
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b
    · simp only [hab, if_true]
    · simp only [if_neg hab, consistency_term_eq_stateQForm]
      change stateQForm (reindexState e ψ)
        (heteroKron (tildeM w .alice W u a) 1 *
          heteroKron 1 (tildeM w .bob W u b)) = _
      rw [WinImplications.stateQForm_reindexState]
      exact congrArg (stateQForm ψ) (WinImplications.reindexOp_mul e
        (heteroKron (tildeM w .alice W u a) 1)
        (heteroKron 1 (tildeM w .bob W u b)))
  rwa [hdistance, hconsistency] at hbound

end

end MIPStarRE.QPBT
