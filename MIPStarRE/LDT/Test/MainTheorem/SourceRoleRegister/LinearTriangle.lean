module

public import MIPStarRE.LDT.Preliminaries.Triangles.CompleteMeasurements
public import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Final

/-!
# Linear-triangle role-register construction

This module reruns the two complete-measurement consistency triangles in the
final low individual degree test construction with the linear-error inequality
from `Preliminaries.Triangles.CompleteMeasurements`.  It preserves the same
unsymmetrized polynomial measurements and the same completed projective
measurements as the existing source route.

## References

* `references/ldt-paper/inductive_step.tex`, lines 68-185.
* `references/ldt-paper/preliminaries.tex`,
  `prop:simeq-triangle-inequality` at lines 649-684.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Full-polynomial consistency from the source role-register witnesses using
the complete-measurement linear triangle.

The unsymmetrized point-consistency error is
`s = 2 * mainInductionError`.  The linear triangle gives evaluated polynomial
consistency at `6 * s + 9 * eps`; the existing Schwartz--Zippel step then adds
`m*d/q`. -/
theorem source_role_register_complete_polynomial_self_consistency_linear_triangle
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    let s : Error :=
      2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) s ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) s ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas) z := by
  let s : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
  change ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas) s ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) s ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas) z
  rcases sourceRoleRegisterUnsymmetrizedPointConsistency
      params strategy eps hpass k hk with ⟨G_A, G_B, hpointAGB, hGApointB⟩
  let pointA : IdxMeas (Point params) (Fq params) ιA :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB : IdxMeas (Point params) (Fq params) ιB :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let gAEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params G_A
  let gBEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params G_B
  have hpointAGBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas gBEval) s := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params G_B.toSubMeas) s
    simpa [s] using hpointAGB
  have hGApointBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas pointB) s := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) s
    simpa [s] using hGApointB
  have hpoint : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas pointB) (3 * eps) := by
    refine ⟨?_⟩
    change bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps
    simpa [ProjStrat.pointAgreementFailureProbability] using
      pointAgreementFailureProbability_le_three_mul params hpass
  have hevaluated : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas gBEval)
      (3 * (s + 3 * eps + s)) :=
    Preliminaries.consistency_triangle_three_heterogeneous strategy.state
      (uniformDistribution (Point params)) gAEval pointA pointB gBEval
      s (3 * eps) s hGApointBMeas hpoint hpointAGBMeas
  have hfullRaw :=
    Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
      params strategy.state strategy.isNormalized G_A.toSubMeas G_B.toSubMeas
      (3 * (s + 3 * eps + s)) hevaluated
  refine ⟨G_A, G_B, ?_, ?_, ?_⟩
  · simpa [s] using hpointAGB
  · simpa [s] using hGApointB
  · apply ConsRel.mono (δ := 3 * (s + 3 * eps + s) +
        (params.m * params.d : Error) / params.q)
    · dsimp [z]
      ring_nf
      exact le_rfl
    · exact hfullRaw

/-- Final projective polynomial measurements from the linear-triangle source
route, before the scalar envelope is imposed.

Writing `s = 2I`, the first complete-measurement triangle and
Schwartz--Zippel step give `z = 6s + 9eps + md/q`.  Orthogonalization,
completion to projective measurements, and the consistency estimate after
completion supply `c = orthonormalizeAndCompleteError z`,
`eta = z + sqrt(orthonormalizationError z)`, and `v = 6z + 6c`.  Both final
point conclusions then have error `3 * (s + eta + v/2)`, while full-polynomial
consistency has error `v/2`. -/
theorem source_role_register_final_point_consistency_linear_triangle
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    let s : Error :=
      2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
    let c : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError z
    let eta : Error :=
      z + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z)
    let v : Error := 6 * z + 6 * c
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (3 * (s + eta + v / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (3 * (s + eta + v / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (polynomialEvaluationFamily params Q_B.toSubMeas) (v / 2) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas) (v / 2) := by
  let s : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
  let c : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError z
  let eta : Error :=
    z + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z)
  let v : Error := 6 * z + 6 * c
  change ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (3 * (s + eta + v / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (3 * (s + eta + v / 2)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (polynomialEvaluationFamily params Q_B.toSubMeas) (v / 2) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas) (v / 2)
  rcases source_role_register_complete_polynomial_self_consistency_linear_triangle
      params strategy eps hpass k hk with ⟨G_A, G_B, hpointAGB, hGApointB, hfull⟩
  have hfullz : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) z := by
    simpa [z, s] using hfull
  rcases sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B z hfullz with ⟨P_A, hleft⟩
  rcases sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
      params strategy G_A G_B z hfullz with ⟨P_B, hright⟩
  rcases completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements
      (params := params) (strategy := strategy) (G_A := G_A) (G_B := G_B)
      (P_A := P_A) (P_B := P_B) (ζ := z) hfullz hleft hright with
    ⟨Q_A, Q_B, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩
  have hQQSDD :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) v := by
    simpa [v, c] using
      completedProjectiveConsistency_ofFullConsistency
        (params := params) (strategy := strategy) (G_A := G_A) (G_B := G_B)
        (Q_A := Q_A) (Q_B := Q_B) (ζ := z)
        hfullz hleftComplete hrightComplete
  have hQQEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (v / 2) :=
    Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
      (params := params) (ψ := strategy.state) Q_A Q_B hQQSDD
  let leftConst : IdxProjMeas Unit (Polynomial params) ιA := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ιB := fun _ => Q_B
  have hQQUnitApprox :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxProjMeas.toIdxSubMeas leftConst))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxProjMeas.toIdxSubMeas rightConst))
        (2 * (v / 2)) := by
    change SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (2 * (v / 2))
    convert hQQSDD using 1
    ring
  have hQQUnit : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) (v / 2) := by
    have hunit :=
      Preliminaries.approxToSimeq_heterogeneous strategy.state
        (uniformDistribution Unit) leftConst rightConst (v / 2) hQQUnitApprox
    change ConsRel strategy.state (uniformDistribution Unit)
      (IdxProjMeas.toIdxSubMeas leftConst)
      (IdxProjMeas.toIdxSubMeas rightConst) (v / 2)
    exact hunit
  have hleftLineEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas) eta := by
    simpa [eta] using
      Test.consRel_constPolynomialEvaluation_heterogeneous
        (params := params) strategy.state Q_A.toMeasurement G_B hleftLine169
  have hrightLineEval : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) eta := by
    simpa [eta] using
      Test.consRel_constPolynomialEvaluation_heterogeneous
        (params := params) strategy.state G_A Q_B.toMeasurement hrightLine169
  let pointA : IdxMeas (Point params) (Fq params) ιA :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB : IdxMeas (Point params) (Fq params) ιB :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let gAEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params G_A
  let gBEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params G_B
  let qAEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params Q_A.toMeasurement
  let qBEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params Q_B.toMeasurement
  have hpointAGBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas gBEval) s := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params G_B.toSubMeas) s
    simpa [s] using hpointAGB
  have hGApointBMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas pointB) s := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) s
    simpa [s] using hGApointB
  have hleftLineMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas gBEval) eta := by
    exact hleftLineEval
  have hrightLineMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas gAEval) (IdxMeas.toIdxSubMeas qBEval) eta := by
    exact hrightLineEval
  have hQQEvalMeas : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas qBEval) (v / 2) := by
    exact hQQEval
  have hAliceFinal : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas qBEval)
      (3 * (s + eta + v / 2)) :=
    Preliminaries.consistency_triangle_three_heterogeneous strategy.state
      (uniformDistribution (Point params)) pointA qAEval gBEval qBEval
      s eta (v / 2) hpointAGBMeas hleftLineMeas hQQEvalMeas
  have hBobRaw : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas pointB)
      (3 * (v / 2 + eta + s)) :=
    Preliminaries.consistency_triangle_three_heterogeneous strategy.state
      (uniformDistribution (Point params)) qAEval gAEval qBEval pointB
      (v / 2) eta s hQQEvalMeas hrightLineMeas hGApointBMeas
  have hBobFinal : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas qAEval) (IdxMeas.toIdxSubMeas pointB)
      (3 * (s + eta + v / 2)) := by
    apply ConsRel.mono (δ := 3 * (v / 2 + eta + s))
    · ring_nf
      exact le_rfl
    · exact hBobRaw
  exact ⟨Q_A, Q_B, hAliceFinal, hBobFinal, hQQEval, hQQUnit⟩

end ProjStrat

end MIPStarRE.LDT
