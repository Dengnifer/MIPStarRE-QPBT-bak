import MIPStarRE.QPBT.Extraction.Consistency
import MIPStarRE.QPBT.Extraction.PullingPointConsistency

/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue #520; the global witness is supplied, not constructed.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Place a complete measurement on its three-register extraction block. -/
private def pullingPlacedMeasurement {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide) {A : Type*} [Fintype A]
    (M : Measurement A (ExtractionBlock P (S.LocalSpace side))) :
    Measurement A (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  refine Measurement.ofSumEqOne (fun a => S.placeSide side (M.effect a)) ?_ ?_
  · intro a
    cases side
    · exact reindexOp_nonneg _ (kronecker_nonneg (M.pos a) Matrix.PosSemidef.one.nonneg)
    · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (M.pos a))
  · cases side
    · rw [← S.placeSide_alice_finset_sum, M.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]
    · rw [← S.placeSide_bob_finset_sum, M.sum_eq_one]
      change reindexOp _ (heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) = 1
      rw [heteroKron_one_one]
      ext row col
      simp [reindexOp, Matrix.one_apply]

private theorem pullingPlacedMeasurement_effect {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (side : PlayerSide) {A : Type*} [Fintype A]
    (M : Measurement A (ExtractionBlock P (S.LocalSpace side))) (a : A) :
    (pullingPlacedMeasurement S side M).effect a = S.placeSide side (M.effect a) := by
  rfl

/-- The Alice evaluation defect is bounded by the supplied global consistency
error, with no decoder correction or non-encoding mass term. -/
theorem pullingMeas_eval_point_consistent_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice
        (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let pulled := fun u => pullingPlacedMeasurement S .alice
    ((pullingMeas w .alice W).postprocess (fun g => evalPoly g u))
  let point := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let marginal := fun u => S.placedMeasurement .AA'
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
  have hp := consistencyDefect_eq_one_sub_overlap mu pulled point S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have hm := consistencyDefect_eq_one_sub_overlap mu marginal expanded S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have heq : consistencyDefect mu (fun u a => (pulled u).effect a)
      (fun u a => (point u).effect a) S.psiHat =
      consistencyDefect mu (fun u a => (marginal u).effect a)
        (fun u a => (expanded u).effect a) S.psiHat := by
    rw [hp, hm]
    apply congrArg (1 - ·)
    apply avgOver_congr
    intro u
    simp only [pulled, point, marginal, expanded, pullingPlacedMeasurement_effect,
      ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat (S.placeSide .alice
      (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pullingMeas_eval_mul_pointMeas]
    rw [← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .AA' W u
        (fun a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_alice w W
  change consistencyDefect mu (fun u a => (marginal u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hbound
  exact heq.le.trans hbound

/-- Bob's evaluation defect has the same bound, using the other consistency
field of the supplied witness and its `BB'`--`AB''` placements. -/
theorem pullingMeas_eval_point_consistent_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let pulled := fun u => pullingPlacedMeasurement S .bob
    ((pullingMeas w .bob W).postprocess (fun g => evalPoly g u))
  let point := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let marginal := fun u => S.placedMeasurement .BB'
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have hp := consistencyDefect_eq_one_sub_overlap mu point pulled S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have hm := consistencyDefect_eq_one_sub_overlap mu marginal expanded S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm
  have heq : consistencyDefect mu (fun u a => (point u).effect a)
      (fun u a => (pulled u).effect a) S.psiHat =
      consistencyDefect mu (fun u a => (marginal u).effect a)
        (fun u a => (expanded u).effect a) S.psiHat := by
    rw [hp, hm]
    apply congrArg (1 - ·)
    apply avgOver_congr
    intro u
    simp only [pulled, point, marginal, expanded, pullingPlacedMeasurement_effect,
      ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) * S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pointMeas_mul_pullingMeas_eval]
    rw [← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .BB' W u
        (fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_bob w W
  change consistencyDefect mu (fun u a => (marginal u).effect a)
    (fun u a => (expanded u).effect a) S.psiHat ≤ deltaG at hbound
  exact heq.le.trans hbound

end

end MIPStarRE.QPBT
