import MIPStarRE.QPBT.Extraction.PolynomialConsistency
import MIPStarRE.QPBT.Extraction.MarginalEvaluation

/-!
# Consistency of evaluated difference polynomials

The evaluated polynomial `g - g_h` has the same consistency with the opposite
point measurement as the polynomial marginal has with the expanded point
measurement. The triangle inequality through the two point measurements then
bounds its self-consistency. Polynomial collision and trace postprocessing
give the observable estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1496-1605`,
  `eq:qld-pulling-cons` and `lem:qld-construct-the-paulis`.
- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- Issue #520.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Equal diagonal agreement operators give equal consistency defects for
complete measurements. This is the completeness calculation in `fact:agreement`. -/
private theorem consistencyDefect_eq_of_sum_mul_eq
    {X α ι : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (μ : Distribution X)
    (A B C D : X → Measurement α ι) (ψ : EuclideanSpace ℂ ι)
    (h : ∀ x, (∑ a, (A x).effect a * (B x).effect a) =
      ∑ a, (C x).effect a * (D x).effect a) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ =
      consistencyDefect μ (fun x a => (C x).effect a) (fun x a => (D x).effect a) ψ := by
  unfold consistencyDefect
  simp only [consistency_term_eq_stateQForm]
  apply avgOver_congr
  intro x
  rw [point_defect_eq, point_defect_eq, ← stateQForm_finset_sum,
    ← stateQForm_finset_sum, h]

/-- Alice's evaluated difference polynomial is consistent with Bob's original
point measurement with exactly the supplied witness error. -/
theorem pulledPoly_eval_consistent_point_bob
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (((pulledPolyMeasurement w .alice W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ deltaG := by
  classical
  let A := fun u => S.sideMeasurement .alice
    ((pulledPolyMeasurement w .alice W).postprocess (fun g => MvPolynomial.eval u g.1))
  let B := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let C := fun u => S.placedMeasurement .AA'
    ((w.marginalPoly .alice W).postprocess (fun g => MvPolynomial.eval u g.1))
  let D := fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
  have heq := consistencyDefect_eq_of_sum_mul_eq
    (uniformDistribution (Fin P.m → PauliScalar P)) A B C D S.psiHat (fun u => by
      change (∑ a, S.placeSide .alice _ * S.placePlayer .bob _) =
        ∑ a, S.place .AA' _ * S.place .BA'' _
      rw [sum_pulledPoly_eval_mul_point_bob, sum_marginalPoly_eval_mul])
  exact heq.le.trans (marginalPoly_pointMeas_consistent_alice w W)

/-- Alice's original point measurement is consistent with Bob's evaluated
difference polynomial with exactly the supplied witness error. -/
theorem point_alice_consistent_pulledPoly_eval
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (((pulledPolyMeasurement w .bob W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a)) S.psiHat ≤ deltaG := by
  classical
  let A := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let B := fun u => S.sideMeasurement .bob
    ((pulledPolyMeasurement w .bob W).postprocess (fun g => MvPolynomial.eval u g.1))
  let C := fun u => S.placedMeasurement .BB'
    ((w.marginalPoly .bob W).postprocess (fun g => MvPolynomial.eval u g.1))
  let D := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have heq := consistencyDefect_eq_of_sum_mul_eq
    (uniformDistribution (Fin P.m → PauliScalar P)) A B C D S.psiHat (fun u => by
      change (∑ a, S.placePlayer .alice _ * S.placeSide .bob _) =
        ∑ a, S.place .BB' _ * S.place .AB'' _
      rw [sum_point_alice_mul_pulledPoly_eval, sum_marginalPoly_eval_mul])
  exact heq.le.trans (marginalPoly_pointMeas_consistent_bob w W)

set_option maxHeartbeats 800000 in
-- Four six-register measurement families occur in the squared-distance triangle.
/-- Evaluated difference polynomials are self-consistent through the two
original point measurements. The estimate is linear in the witness error and
game error, and uses no non-encoding support assumption. -/
theorem pulledPoly_eval_self_consistency_le
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u a => S.placeSide .alice (((pulledPolyMeasurement w .alice W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a))
      (fun u a => S.placeSide .bob (((pulledPolyMeasurement w .bob W).postprocess
        (fun g => MvPolynomial.eval u g.1)).effect a)) S.psiHat ≤
      12 * deltaG + 8 * (Fintype.card PauliEdge : ℝ) * epsilon := by
  classical
  let μ := uniformDistribution (Fin P.m → PauliScalar P)
  let A := fun u => S.sideMeasurement .alice
    ((pulledPolyMeasurement w .alice W).postprocess (fun g => MvPolynomial.eval u g.1))
  let B := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let C := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let D := fun u => S.sideMeasurement .bob
    ((pulledPolyMeasurement w .bob W).postprocess (fun g => MvPolynomial.eval u g.1))
  have hAB : opFamilyDistSq μ (fun u a => (A u).effect a)
      (fun u a => (B u).effect a) S.psiHat ≤ 2 * deltaG :=
    (opFamilyDistSq_le_two_mul_consistencyDefect μ A B S.psiHat).trans
      (mul_le_mul_of_nonneg_left (pulledPoly_eval_consistent_point_bob w W) (by norm_num))
  have hCD : opFamilyDistSq μ (fun u a => (C u).effect a)
      (fun u a => (D u).effect a) S.psiHat ≤ 2 * deltaG :=
    (opFamilyDistSq_le_two_mul_consistencyDefect μ C D S.psiHat).trans
      (mul_le_mul_of_nonneg_left (point_alice_consistent_pulledPoly_eval w W) (by norm_num))
  have hCB : consistencyDefect μ (fun u a => (C u).effect a)
      (fun u a => (B u).effect a) S.psiHat ≤ (Fintype.card PauliEdge : ℝ) * epsilon := by
    change consistencyDefect μ
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    rw [point_consistencyDefect_placePlayer_eq]
    exact point_self_consistency_le S W
  have hBC : opFamilyDistSq μ (fun u a => (B u).effect a)
      (fun u a => (C u).effect a) S.psiHat ≤
      2 * ((Fintype.card PauliEdge : ℝ) * epsilon) := by
    rw [opFamilyDistSq_symm]
    exact (opFamilyDistSq_le_two_mul_consistencyDefect μ C B S.psiHat).trans
      (mul_le_mul_of_nonneg_left hCB (by norm_num))
  have hBD := opFamilyDistSq_le_of_le_of_le μ
    (fun u a => (B u).effect a) (fun u a => (C u).effect a) (fun u a => (D u).effect a)
    S.psiHat _ _ hBC hCD
  have hAD := opFamilyDistSq_le_of_le_of_le μ
    (fun u a => (A u).effect a) (fun u a => (B u).effect a) (fun u a => (D u).effect a)
    S.psiHat _ _ hAB hBD
  have hproj (side : PlayerSide) (u : Fin P.m → PauliScalar P) :
      Measurement.IsProjective (S.sideMeasurement side
        ((pulledPolyMeasurement w side W).postprocess (fun g => MvPolynomial.eval u g.1))) :=
    S.sideMeasurement_isProjective side _
      (SandwichProduct.postprocess_isProjective _ (pulledPolyMeasurement_isProjective w side W) _)
  have hdef := consistencyDefect_le_opFamilyDistSq_of_projective μ A D S.psiHat
    (hproj .alice) (hproj .bob)
  exact hdef.trans (hAD.trans_eq (by ring))

end

end MIPStarRE.QPBT
