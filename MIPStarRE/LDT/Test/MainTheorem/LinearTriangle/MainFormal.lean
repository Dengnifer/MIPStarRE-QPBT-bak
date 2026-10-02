module

public import MIPStarRE.LDT.Test.MainTheorem.LinearTriangle.Scalars
public import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.LinearTriangle

/-!
# Improved main-formal bound from complete-measurement triangles

This module combines the complete-measurement linear triangle with the
existing source role-register construction.  It proves all three conclusions
of `thm:main-formal` with the capped error

`min 1 (10000 * k^(1/4) * m^(1/2) *
  (eps^(1/8192) + (d/q)^(1/8192) + exp (-k/(640000*m^2))))`.

The theorem is additive: the source-labelled `mainFormal` statement and its
error function are unchanged.

## References

* `references/ldt-paper/test_definition.tex:180-202` (`thm:main-formal`).
* `references/ldt-paper/inductive_step.tex`, lines 68-234.
* `references/ldt-paper/preliminaries.tex`,
  `prop:simeq-triangle-inequality` at lines 649-684.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Saturated branch for the linear-triangle error.

When the uncapped error is at least one, arbitrary projective polynomial
measurements satisfy all three conclusions because normalized bipartite
consistency defects are bounded by one.

**Lean-only:** This auxiliary closes the saturated branch of the quantitative
variant of `thm:main-formal`; the paper theorem and its three conclusions are
stated in `references/ldt-paper/test_definition.tex:180-202`. It is not an
additional source hypothesis. Issue #728. Discharge: proved here from the
universal normalized-consistency bound, using arbitrary projective polynomial
measurements once the capped error is `1`. -/
theorem main_formal_linear_triangle_trivial_witness
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (k : ℕ)
    (hlarge : 1 ≤ mainFormalLinearTriangleRawError params k eps) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialA : ProjMeas (Polynomial params) ιA :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  let trivialB : ProjMeas (Polynomial params) ιB :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  have herror : mainFormalLinearTriangleError params k eps = 1 := by
    unfold mainFormalLinearTriangleError
    exact min_eq_left hlarge
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals refine ⟨?_⟩
  all_goals rw [herror]
  all_goals exact
    bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _

/-- Small-error branch for the linear-triangle construction.

The witnesses are exactly those built by
`ProjStrat.source_role_register_final_point_consistency_linear_triangle`; the
scalar theorem `linear_triangle_source_errors_le_uncapped_error` absorbs its
literal point and full-polynomial errors into the new uncapped error. -/
theorem main_formal_linear_triangle_small_error_conclusion
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hsmall : mainFormalLinearTriangleRawError params k eps < 1) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) := by
  let s : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
  let c : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError z
  let eta : Error := z + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z)
  let v : Error := 6 * z + 6 * c
  have hepsNN : 0 ≤ eps := ProjStrat.eps_nonneg_of_passes hpass
  have hbounds :
      3 * (s + eta + v / 2) ≤ mainFormalLinearTriangleRawError params k eps ∧
        v / 2 ≤ mainFormalLinearTriangleRawError params k eps := by
    simpa [s, z, c, eta, v] using
      linear_triangle_source_errors_le_uncapped_error hepsNN hk0 hsmall
  have herror : mainFormalLinearTriangleError params k eps =
      mainFormalLinearTriangleRawError params k eps := by
    unfold mainFormalLinearTriangleError
    exact min_eq_right hsmall.le
  rcases ProjStrat.source_role_register_final_point_consistency_linear_triangle
      params strategy eps hpass k hk with ⟨Q_A, Q_B, hA, hB, _hEval, hFull⟩
  refine ⟨Q_A, Q_B, ?_, ?_, ?_⟩
  · rw [herror]
    exact ConsRel.mono hbounds.1 (by simpa [s, z, c, eta, v] using hA)
  · rw [herror]
    exact ConsRel.mono hbounds.1 (by simpa [s, z, c, eta, v] using hB)
  · rw [herror]
    exact ConsRel.mono hbounds.2 (by simpa [s, z, c, eta, v] using hFull)

/-- The complete-measurement linear-triangle improvement of `thm:main-formal`,
using the named capped error `mainFormalLinearTriangleError`.

This theorem has exactly the strategy, test-passing, large-`k`, and nonzero-`k`
hypotheses of `mainFormal`; it adds no bridge or construction input. -/
theorem main_formal_linear_triangle
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalLinearTriangleError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (mainFormalLinearTriangleError params k eps) := by
  let hpasses : strategy.PassesLowIndividualDegreeTest eps := ⟨hpass⟩
  by_cases hlarge : 1 ≤ mainFormalLinearTriangleRawError params k eps
  · exact main_formal_linear_triangle_trivial_witness params strategy eps k hlarge
  · exact main_formal_linear_triangle_small_error_conclusion
      params strategy eps hpasses k hk hk0
      (lt_of_not_ge hlarge)

/-- Explicit numerical form of the complete-measurement linear-triangle
improvement.

It constructs the same two projective polynomial measurements and proves the
same three consistency conclusions as `mainFormal`, with error

`min 1 (10000 * k^(1/4) * m^(1/2) *
  (eps^(1/8192) + (d/q)^(1/8192) + exp (-k/(640000*m^2))))`.

This is a Lean-only quantitative result derived from the source proof; it does
not replace the source-labelled theorem. -/
theorem main_formal_linear_triangle_bound
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params Q_B.toSubMeas)
            (min 1 (10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
              Real.rpow (params.m : Error) (1 / (2 : Error)) *
              (Real.rpow eps (1 / (8192 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error))
                  (1 / (8192 : Error)) +
                Real.exp (-((k : Error) /
                  (640000 * ((params.m : Error) ^ (2 : ℕ)))))))) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params Q_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (min 1 (10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
              Real.rpow (params.m : Error) (1 / (2 : Error)) *
              (Real.rpow eps (1 / (8192 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error))
                  (1 / (8192 : Error)) +
                Real.exp (-((k : Error) /
                  (640000 * ((params.m : Error) ^ (2 : ℕ)))))))) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily Q_A.toSubMeas)
            (constSubMeasFamily Q_B.toSubMeas)
            (min 1 (10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
              Real.rpow (params.m : Error) (1 / (2 : Error)) *
              (Real.rpow eps (1 / (8192 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error))
                  (1 / (8192 : Error)) +
                Real.exp (-((k : Error) /
                  (640000 * ((params.m : Error) ^ (2 : ℕ)))))))) := by
  simpa [mainFormalLinearTriangleError, mainFormalLinearTriangleRawError,
    stepEnvelope] using main_formal_linear_triangle params strategy eps hpass k hk hk0

/-! ### Comparison with the previous explicit error bound -/

/-- In the scalar unit regime, ten times the new uncapped error is bounded by the
previous `mainFormalError`.

The comparison uses `8192 ≤ 40000`, `640000 ≤ 2560000`,
`k^(1/4) ≤ k²`, and `m^(1/2) ≤ m⁴`. -/
theorem ten_mul_mainFormalLinearTriangleRawError_le_mainFormalError
    {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    10 * mainFormalLinearTriangleRawError params k eps ≤
      mainFormalError params k eps := by
  have hEnv : stepEnvelope params k eps (8192 : Error) (640000 : Error) ≤
      mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h)
      (n := (8192 : Error)) (N := (640000 : Error))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hkRoot : Real.rpow (k : Error) (1 / (4 : Error)) ≤
      ((k : Error) ^ (2 : ℕ)) := by
    have hrootToK : Real.rpow (k : Error) (1 / (4 : Error)) ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk
        (by norm_num : (1 / (4 : Error)) ≤ 1)
    exact hrootToK.trans h.k_le_k2
  have hmRoot : Real.rpow (params.m : Error) (1 / (2 : Error)) ≤
      ((params.m : Error) ^ (4 : ℕ)) := by
    have hrootToM : Real.rpow (params.m : Error) (1 / (2 : Error)) ≤
        (params.m : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hm
        (by norm_num : (1 / (2 : Error)) ≤ 1)
    exact hrootToM.trans h.m_le_m4
  have hNewEnv0 : 0 ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) :=
    stepEnvelope_nonneg (h := h)
  have hOldEnv0 : 0 ≤ mainFormalEnvelope params k eps := h.envelope_nonneg
  have hRoots :
      Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) ≤
        ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
    mul_le_mul hkRoot hmRoot (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (by positivity)
  have hProduct :
      Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) *
          stepEnvelope params k eps (8192 : Error) (640000 : Error) ≤
        ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
    mul_le_mul hRoots hEnv hNewEnv0 (by positivity)
  rw [mainFormalError_eq_envelope]
  unfold mainFormalLinearTriangleRawError
  calc
    10 * (10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
        Real.rpow (params.m : Error) (1 / (2 : Error)) *
        stepEnvelope params k eps (8192 : Error) (640000 : Error)) =
        100000 * (Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) *
          stepEnvelope params k eps (8192 : Error) (640000 : Error)) := by ring
    _ ≤ 100000 * (((k : Error) ^ (2 : ℕ)) *
          ((params.m : Error) ^ (4 : ℕ)) * mainFormalEnvelope params k eps) :=
      mul_le_mul_of_nonneg_left hProduct (by norm_num)
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) *
          ((params.m : Error) ^ (4 : ℕ)) * mainFormalEnvelope params k eps := by ring

/-- On the nonnegative-error domain of the theorem, the new capped error is no
larger than the capped previous explicit error bound. -/
theorem mainFormalLinearTriangleError_le_min_mainFormalError
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k) :
    mainFormalLinearTriangleError params k eps ≤
      min 1 (mainFormalError params k eps) := by
  by_cases hOldLarge : 1 ≤ mainFormalError params k eps
  · rw [min_eq_left hOldLarge]
    exact min_le_left _ _
  · have h := cascadeHypotheses_of_not_mainFormalError_ge_one hepsNN hk0 hOldLarge
    have hten := ten_mul_mainFormalLinearTriangleRawError_le_mainFormalError h
    have hraw0 := mainFormalLinearTriangleRawError_nonneg params k hepsNN
    have hraw : mainFormalLinearTriangleRawError params k eps ≤
        mainFormalError params k eps := by nlinarith
    rw [min_eq_right (le_of_not_ge hOldLarge)]
    exact (min_le_right _ _).trans hraw

/-- Strict improvement whenever the previous explicit error bound is nontrivial.

If `mainFormalError < 1`, the scalar unit regime holds and
ten times the uncapped new error is at most `mainFormalError`.  The exponential
summand makes the uncapped new error strictly positive, so the capped new error
is smaller than `min 1 mainFormalError`. -/
theorem mainFormalLinearTriangleError_lt_min_mainFormalError
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hOldSmall : mainFormalError params k eps < 1) :
    mainFormalLinearTriangleError params k eps <
      min 1 (mainFormalError params k eps) := by
  have hOldNotLarge : ¬ 1 ≤ mainFormalError params k eps := not_le.mpr hOldSmall
  let h := cascadeHypotheses_of_not_mainFormalError_ge_one hepsNN hk0 hOldNotLarge
  have hten := ten_mul_mainFormalLinearTriangleRawError_le_mainFormalError h
  have hrawPos : 0 < mainFormalLinearTriangleRawError params k eps := by
    have hkPos : 0 < (k : Error) := by exact_mod_cast hk0
    have hmPos : 0 < (params.m : Error) := by exact_mod_cast params.hm
    have hEnvPos : 0 < stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
      unfold stepEnvelope
      have hepsPow0 : 0 ≤ Real.rpow eps (1 / (8192 : Error)) :=
        Real.rpow_nonneg hepsNN _
      have hdq0 : 0 ≤ (params.d : Error) / (params.q : Error) :=
        div_nonneg (Nat.cast_nonneg _) params.q_cast_pos.le
      have hdqPow0 :
          0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (8192 : Error)) := Real.rpow_nonneg hdq0 _
      have hExpPos :
          0 < Real.exp (-((k : Error) /
            (640000 * ((params.m : Error) ^ (2 : ℕ))))) := Real.exp_pos _
      linarith
    unfold mainFormalLinearTriangleRawError
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos hkPos _))
        (Real.rpow_pos_of_pos hmPos _)) hEnvPos
  have hrawLtOld : mainFormalLinearTriangleRawError params k eps <
      mainFormalError params k eps := by nlinarith
  have hrawLtOne := hrawLtOld.trans hOldSmall
  rw [mainFormalLinearTriangleError, min_eq_right hrawLtOne.le,
    min_eq_right hOldSmall.le]
  exact hrawLtOld

end Test

end MIPStarRE.LDT
