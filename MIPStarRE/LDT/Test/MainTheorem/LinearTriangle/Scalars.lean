import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.CascadeBounds.SigmaZeta1
import MIPStarRE.LDT.Test.MainTheorem.SourceScalars

/-!
# Scalar bounds for the complete-measurement linear triangle

This module bounds the literal errors returned by the linear-triangle source
construction.  The small-error argument is organized around the new uncapped error
`mainFormalLinearTriangleRawError`; it does not assume that the older
`mainFormalError` is below one.

## References

* `references/ldt-paper/inductive_step.tex`, lines 68-234.
* `references/ldt-paper/preliminaries.tex`,
  `prop:simeq-triangle-inequality` at lines 649-684.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- The uncapped error obtained from the complete-measurement linear triangle.

This is the quantity
`10000 * k^(1/4) * m^(1/2) *
  (eps^(1/8192) + (d/q)^(1/8192) + exp (-k/(640000*m^2)))`.
It is a Lean-only quantitative improvement of the error in `thm:main-formal`;
the source theorem and its existing error function remain unchanged. -/
noncomputable def mainFormalLinearTriangleRawError
    (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
    Real.rpow (params.m : Error) (1 / (2 : Error)) *
    stepEnvelope params k eps (8192 : Error) (640000 : Error)

/-- The public linear-triangle error, capped by the normalized consistency
bound `1`. -/
noncomputable def mainFormalLinearTriangleError
    (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  min 1 (mainFormalLinearTriangleRawError params k eps)

/-- The uncapped linear-triangle error is nonnegative when `eps` is nonnegative. -/
theorem mainFormalLinearTriangleRawError_nonneg
    (params : Parameters) (k : ℕ) {eps : Error} (heps : 0 ≤ eps) :
    0 ≤ mainFormalLinearTriangleRawError params k eps := by
  have hE : 0 ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    unfold stepEnvelope
    have hdq : 0 ≤ (params.d : Error) / (params.q : Error) :=
      div_nonneg (Nat.cast_nonneg _) params.q_cast_pos.le
    exact add_nonneg (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdq _))
      (Real.exp_nonneg _)
  unfold mainFormalLinearTriangleRawError
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE

/-- In the non-saturated branch of the new error, the standing scalar regime
for the main-induction estimate follows from the theorem's boundary data.

If either `eps > 1` or `d/q > 1`, one summand of the new envelope is at least
one, while the prefactor is at least `10000`; hence the uncapped error cannot be
below one.

**Lean-only:** This scalar domain reduction supports the alternative error
cascade derived from the final construction in
`references/ldt-paper/inductive_step.tex:68-234`; it is not asserted as a
separate paper lemma and adds no hypothesis to `thm:main-formal`. Issue #728.
Discharge: proved here from the small-error assumption, since `eps > 1` or
`d/q > 1` would force the uncapped error to be at least one. -/
theorem cascade_hypotheses_of_mainFormalLinearTriangleRawError_lt_one
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : mainFormalLinearTriangleRawError params k eps < 1) :
    CascadeHypotheses params k eps := by
  have hk : (1 : Error) ≤ (k : Error) := Nat.one_le_cast.mpr hk0
  have hm : (1 : Error) ≤ (params.m : Error) := Nat.one_le_cast.mpr params.hm
  have hkr : 1 ≤ Real.rpow (k : Error) (1 / (4 : Error)) :=
    Real.one_le_rpow hk (by positivity)
  have hmr : 1 ≤ Real.rpow (params.m : Error) (1 / (2 : Error)) :=
    Real.one_le_rpow hm (by positivity)
  have hprefactor :
      1 ≤ 10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
        Real.rpow (params.m : Error) (1 / (2 : Error)) := by
    have hroots :
        1 ≤ Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) :=
      one_le_mul_of_one_le_of_one_le hkr hmr
    calc
      (1 : Error) ≤ 10000 := by norm_num
      _ ≤ 10000 * (Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error))) :=
        by simpa using
          mul_le_mul_of_nonneg_left hroots (by norm_num : (0 : Error) ≤ 10000)
      _ = 10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) := by ring
  have raw_ge_one_of_envelope_ge_one
      (henv : 1 ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error)) :
      1 ≤ mainFormalLinearTriangleRawError params k eps := by
    unfold mainFormalLinearTriangleRawError
    calc
      (1 : Error) ≤
          10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
            Real.rpow (params.m : Error) (1 / (2 : Error)) := hprefactor
      _ ≤ 10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
            Real.rpow (params.m : Error) (1 / (2 : Error)) *
            stepEnvelope params k eps (8192 : Error) (640000 : Error) :=
        by simpa using mul_le_mul_of_nonneg_left henv (by
          positivity : 0 ≤ 10000 * Real.rpow (k : Error) (1 / (4 : Error)) *
            Real.rpow (params.m : Error) (1 / (2 : Error)))
  refine
    { hk := hk
      hm := hm
      hepsNN := hepsNN
      hepsOne := ?_
      hdq := ?_
      hqPos := params.q_cast_pos }
  · by_contra hepsOne
    have hepsGt : 1 < eps := lt_of_not_ge hepsOne
    have hepsPow : 1 ≤ Real.rpow eps (1 / (8192 : Error)) :=
      Real.one_le_rpow hepsGt.le (by positivity)
    have hdqPowNN :
        0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8192 : Error)) :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) params.q_cast_pos.le) _
    have hExpNN :
        0 ≤ Real.exp (-((k : Error) /
          (640000 * ((params.m : Error) ^ (2 : ℕ))))) := Real.exp_nonneg _
    have henv : 1 ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
      unfold stepEnvelope
      linarith
    linarith [raw_ge_one_of_envelope_ge_one henv]
  · by_contra hdq
    have hqd : (params.q : Error) < (params.d : Error) := lt_of_not_ge hdq
    have hdqGt : 1 < (params.d : Error) / (params.q : Error) :=
      (one_lt_div params.q_cast_pos).2 hqd
    have hdqPow :
        1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8192 : Error)) := Real.one_le_rpow hdqGt.le (by positivity)
    have hepsPowNN : 0 ≤ Real.rpow eps (1 / (8192 : Error)) :=
      Real.rpow_nonneg hepsNN _
    have hExpNN :
        0 ≤ Real.exp (-((k : Error) /
          (640000 * ((params.m : Error) ^ (2 : ℕ))))) := Real.exp_nonneg _
    have henv : 1 ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
      unfold stepEnvelope
      linarith
    linarith [raw_ge_one_of_envelope_ge_one henv]

/-- Three square-root envelope steps turn the induction envelope with
denominators `(1024, 80000)` into the advertised `(8192, 640000)` envelope. -/
theorem stepEnvelope1024_rpow_eighth_le
    {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow (stepEnvelope params k eps (1024 : Error) (80000 : Error))
        (1 / (8 : Error)) ≤
      stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
  have h1 :
      Real.sqrt (stepEnvelope params k eps (1024 : Error) (80000 : Error)) ≤
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
    simpa [show (2 : Error) * 1024 = 2048 by norm_num,
      show (2 : Error) * 80000 = 160000 by norm_num] using sqrt_stepEnvelope_le (h := h)
      (n := (1024 : Error)) (N := (80000 : Error)) (by norm_num) (by norm_num)
  have h2 :
      Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)) ≤
        stepEnvelope params k eps (4096 : Error) (320000 : Error) := by
    simpa [show (2 : Error) * 2048 = 4096 by norm_num,
      show (2 : Error) * 160000 = 320000 by norm_num] using sqrt_stepEnvelope_le (h := h)
      (n := (2048 : Error)) (N := (160000 : Error)) (by norm_num) (by norm_num)
  have h3 :
      Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error)) ≤
        stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    simpa [show (2 : Error) * 4096 = 8192 by norm_num,
      show (2 : Error) * 320000 = 640000 by norm_num] using sqrt_stepEnvelope_le (h := h)
      (n := (4096 : Error)) (N := (320000 : Error)) (by norm_num) (by norm_num)
  have hE0 : 0 ≤ stepEnvelope params k eps (1024 : Error) (80000 : Error) :=
    stepEnvelope_nonneg (h := h)
  calc
    Real.rpow (stepEnvelope params k eps (1024 : Error) (80000 : Error))
        (1 / (8 : Error)) =
        Real.sqrt (Real.sqrt (Real.sqrt
          (stepEnvelope params k eps (1024 : Error) (80000 : Error)))) :=
      rpow_one_eight_eq_sqrt_sqrt_sqrt hE0
    _ ≤ Real.sqrt (Real.sqrt
          (stepEnvelope params k eps (2048 : Error) (160000 : Error))) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    _ ≤ Real.sqrt
          (stepEnvelope params k eps (4096 : Error) (320000 : Error)) :=
      Real.sqrt_le_sqrt h2
    _ ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) := h3

/-- Eighth-root extraction for the intermediate linear-triangle error.

The numerical certificate is `120010 ≤ (9/2)^8`. -/
theorem rpow_linear_triangle_scale_eighth_le
    {params : Parameters} {k : ℕ} {eps z : Error}
    (h : CascadeHypotheses params k eps)
    (hz0 : 0 ≤ z)
    (hz : z ≤ 120010 * ((k : Error) ^ (2 : ℕ)) *
      ((params.m : Error) ^ (4 : ℕ)) *
      stepEnvelope params k eps (1024 : Error) (80000 : Error)) :
    Real.rpow z (1 / (8 : Error)) ≤
      (9 / 2 : Error) * Real.rpow (k : Error) (1 / (4 : Error)) *
        Real.rpow (params.m : Error) (1 / (2 : Error)) *
        stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
  let E : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  let F : Error := stepEnvelope params k eps (8192 : Error) (640000 : Error)
  let r : Error := 1 / (8 : Error)
  have hE0 : 0 ≤ E := by
    simpa [E] using stepEnvelope_nonneg (h := h)
  have hF0 : 0 ≤ F := by
    simpa [F] using stepEnvelope_nonneg (h := h)
  have hEr : Real.rpow E r ≤ F := by
    simpa [E, F, r] using stepEnvelope1024_rpow_eighth_le h
  have hconst : Real.rpow (120010 : Error) r ≤ (9 / 2 : Error) := by
    have hmono := Real.rpow_le_rpow
      (show 0 ≤ (120010 : Error) by norm_num)
      (show (120010 : Error) ≤ (9 / 2 : Error) ^ (8 : ℕ) by norm_num)
      (show 0 ≤ r by positivity)
    calc
      Real.rpow (120010 : Error) r ≤
          Real.rpow ((9 / 2 : Error) ^ (8 : ℕ)) r := hmono
      _ = Real.rpow (9 / 2 : Error) ((8 : Error) * r) := by
        symm
        exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (9 / 2 : Error)) 8 r
      _ = (9 / 2 : Error) := by norm_num [r, Real.rpow_one]
  have hkpow :
      Real.rpow ((k : Error) ^ (2 : ℕ)) r =
        Real.rpow (k : Error) (1 / (4 : Error)) := by
    calc
      Real.rpow ((k : Error) ^ (2 : ℕ)) r =
          Real.rpow (k : Error) ((2 : Error) * r) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 r
      _ = Real.rpow (k : Error) (1 / (4 : Error)) := by norm_num [r]
  have hmpow :
      Real.rpow ((params.m : Error) ^ (4 : ℕ)) r =
        Real.rpow (params.m : Error) (1 / (2 : Error)) := by
    calc
      Real.rpow ((params.m : Error) ^ (4 : ℕ)) r =
          Real.rpow (params.m : Error) ((4 : Error) * r) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 r
      _ = Real.rpow (params.m : Error) (1 / (2 : Error)) := by norm_num [r]
  have hleftFactor :
      Real.rpow ((120010 : Error) * ((k : Error) ^ (2 : ℕ))) r =
        Real.rpow (120010 : Error) r *
          Real.rpow ((k : Error) ^ (2 : ℕ)) r :=
    Real.mul_rpow (x := (120010 : Error)) (y := ((k : Error) ^ (2 : ℕ)))
      (z := r) (by norm_num) (by positivity)
  have hrightFactor :
      Real.rpow (((params.m : Error) ^ (4 : ℕ)) * E) r =
        Real.rpow ((params.m : Error) ^ (4 : ℕ)) r * Real.rpow E r :=
    Real.mul_rpow (x := ((params.m : Error) ^ (4 : ℕ))) (y := E)
      (z := r) (by positivity) hE0
  have hfactor :
      Real.rpow (120010 * ((k : Error) ^ (2 : ℕ)) *
        ((params.m : Error) ^ (4 : ℕ)) * E) r =
        Real.rpow (120010 : Error) r *
          Real.rpow ((k : Error) ^ (2 : ℕ)) r *
          Real.rpow ((params.m : Error) ^ (4 : ℕ)) r * Real.rpow E r := by
    calc
      Real.rpow (120010 * ((k : Error) ^ (2 : ℕ)) *
          ((params.m : Error) ^ (4 : ℕ)) * E) r =
          Real.rpow (((120010 : Error) * ((k : Error) ^ (2 : ℕ))) *
            (((params.m : Error) ^ (4 : ℕ)) * E)) r := by
        congr 1
        ring
      _ =
          Real.rpow ((120010 : Error) * ((k : Error) ^ (2 : ℕ))) r *
            Real.rpow (((params.m : Error) ^ (4 : ℕ)) * E) r := by
        exact Real.mul_rpow (by positivity) (mul_nonneg (by positivity) hE0)
          (z := r)
      _ = (Real.rpow (120010 : Error) r *
            Real.rpow ((k : Error) ^ (2 : ℕ)) r) *
          (Real.rpow ((params.m : Error) ^ (4 : ℕ)) r * Real.rpow E r) := by
        exact congrArg₂ (fun a b : Error => a * b) hleftFactor hrightFactor
      _ = Real.rpow (120010 : Error) r *
          Real.rpow ((k : Error) ^ (2 : ℕ)) r *
          Real.rpow ((params.m : Error) ^ (4 : ℕ)) r * Real.rpow E r := by ring
  have hroot0 := Real.rpow_le_rpow hz0 hz (show 0 ≤ r by positivity)
  have hroot : Real.rpow z r ≤
      Real.rpow (120010 * ((k : Error) ^ (2 : ℕ)) *
        ((params.m : Error) ^ (4 : ℕ)) * E) r := by
    simpa [E] using hroot0
  rw [hfactor, hkpow, hmpow] at hroot
  calc
    Real.rpow z (1 / (8 : Error)) = Real.rpow z r := by rfl
    _ ≤ Real.rpow (120010 : Error) r *
          Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) * Real.rpow E r := hroot
    _ ≤ (9 / 2 : Error) * Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) * F := by
      have hkr0 : 0 ≤ Real.rpow (k : Error) (1 / (4 : Error)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hmr0 : 0 ≤ Real.rpow (params.m : Error) (1 / (2 : Error)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hEr0 : 0 ≤ Real.rpow E r := Real.rpow_nonneg hE0 _
      have hconstK := mul_le_mul_of_nonneg_right hconst hkr0
      have hconstKM := mul_le_mul_of_nonneg_right hconstK hmr0
      exact mul_le_mul hconstKM hEr hEr0
        (mul_nonneg (mul_nonneg (by norm_num) hkr0) hmr0)
    _ = (9 / 2 : Error) * Real.rpow (k : Error) (1 / (4 : Error)) *
          Real.rpow (params.m : Error) (1 / (2 : Error)) *
          stepEnvelope params k eps (8192 : Error) (640000 : Error) := by rfl

/-- The literal point and full-polynomial errors from the linear-triangle
construction are both bounded by the new uncapped error in its non-saturated
branch. -/
theorem linear_triangle_source_errors_le_uncapped_error
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : mainFormalLinearTriangleRawError params k eps < 1) :
    let s : Error :=
      2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
    let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
    let c : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError z
    let eta : Error := z + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z)
    let v : Error := 6 * z + 6 * c
    3 * (s + eta + v / 2) ≤ mainFormalLinearTriangleRawError params k eps ∧
      v / 2 ≤ mainFormalLinearTriangleRawError params k eps := by
  let s : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let z : Error := 6 * s + 9 * eps + (params.m * params.d : Error) / params.q
  let c : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError z
  let eta : Error := z + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z)
  let v : Error := 6 * z + 6 * c
  change 3 * (s + eta + v / 2) ≤ mainFormalLinearTriangleRawError params k eps ∧
    v / 2 ≤ mainFormalLinearTriangleRawError params k eps
  let h : CascadeHypotheses params k eps :=
    cascade_hypotheses_of_mainFormalLinearTriangleRawError_lt_one hepsNN hk0 hsmall
  let E : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  let K : Error := ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))
  have hE0 : 0 ≤ E := by simpa [E] using stepEnvelope_nonneg (h := h)
  have hK0 : 0 ≤ K := by positivity
  have hK1 : 1 ≤ K := by simpa [K] using h.k2_m4_ge_one
  have hI0 :
      0 ≤ MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) := by
    rw [← mainFormalScalarSigma_eq_mainInductionError]
    exact cascadeSigma_nonneg (mainFormalInductionNu_nonneg h)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hI :
      MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) ≤
        10000 * K * E := by
    rw [← mainFormalScalarSigma_eq_mainInductionError]
    calc
      cascadeSigma params k (mainFormalInductionNu params k eps) ≤
          10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E := by
        simpa [E] using cascadeSigma_tight_bound (h := h)
          (mainFormalInductionNu_bound h)
      _ = 10000 * K * E := by dsimp [K]; ring
  have hs : s ≤ 20000 * K * E := by
    dsimp [s]
    nlinarith
  have hepsToE : eps ≤ E := by
    have hepsRoot : eps ≤ Real.rpow eps (1 / (1024 : Error)) :=
      self_le_rpow_one_div h.hepsNN h.hepsOne (by norm_num)
    have hepsTerm : Real.rpow eps (1 / (1024 : Error)) ≤ E := by
      have hdqRoot0 :
          0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (1024 : Error)) := Real.rpow_nonneg h.dqNN _
      have hExp0 :
          0 ≤ Real.exp (-((k : Error) /
            (80000 * ((params.m : Error) ^ (2 : ℕ))))) := Real.exp_nonneg _
      change Real.rpow eps (1 / (1024 : Error)) ≤
        Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
          Real.exp (-((k : Error) /
            (80000 * ((params.m : Error) ^ (2 : ℕ)))))
      exact (le_add_of_nonneg_right hdqRoot0).trans (le_add_of_nonneg_right hExp0)
    exact hepsRoot.trans hepsTerm
  have hdqToE : (params.d : Error) / (params.q : Error) ≤ E := by
    have hdqRoot : (params.d : Error) / (params.q : Error) ≤
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) :=
      self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)
    have hdqTerm :
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤ E := by
      have hepsRoot0 : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
        Real.rpow_nonneg h.hepsNN _
      have hExp0 :
          0 ≤ Real.exp (-((k : Error) /
            (80000 * ((params.m : Error) ^ (2 : ℕ))))) := Real.exp_nonneg _
      change Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤
        Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
          Real.exp (-((k : Error) /
            (80000 * ((params.m : Error) ^ (2 : ℕ)))))
      exact (le_add_of_nonneg_left hepsRoot0).trans (le_add_of_nonneg_right hExp0)
    exact hdqRoot.trans hdqTerm
  have hEToKE : E ≤ K * E := by
    calc
      E = 1 * E := by ring
      _ ≤ K * E := mul_le_mul_of_nonneg_right hK1 hE0
  have hepsToKE : eps ≤ K * E := hepsToE.trans hEToKE
  have hmToK : (params.m : Error) ≤ K := by
    simpa [K] using m_le_k2m4_aux (h := h)
  have hmdqToKE :
      (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤ K * E :=
    mul_le_mul hmToK hdqToE h.dqNN hK0
  have hmdqToKE' :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤ K * E := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error) =
          (params.m : Error) * ((params.d : Error) / (params.q : Error)) := by ring
      _ ≤ K * E := hmdqToKE
  have hz : z ≤ 120010 * K * E := by
    dsimp [z]
    linarith [hmdqToKE']
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity [hs0, hepsNN, h.dqNN]
  have hroot : Real.rpow z (1 / (8 : Error)) ≤
      (9 / 2 : Error) * Real.rpow (k : Error) (1 / (4 : Error)) *
        Real.rpow (params.m : Error) (1 / (2 : Error)) *
        stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    apply rpow_linear_triangle_scale_eighth_le h hz0
    calc
      z ≤ 120010 * K * E := hz
      _ = 120010 * ((k : Error) ^ (2 : ℕ)) *
          ((params.m : Error) ^ (4 : ℕ)) *
          stepEnvelope params k eps (1024 : Error) (80000 : Error) := by
        dsimp [K, E]
        ring
  let X : Error := Real.rpow (k : Error) (1 / (4 : Error)) *
    Real.rpow (params.m : Error) (1 / (2 : Error)) *
    stepEnvelope params k eps (8192 : Error) (640000 : Error)
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity [stepEnvelope_nonneg (h := h)
      (n := (8192 : Error)) (N := (640000 : Error))]
  have hrootX : Real.rpow z (1 / (8 : Error)) ≤ (9 / 2 : Error) * X := by
    simpa [X, mul_assoc] using hroot
  have h2221 :
      2221 * Real.rpow z (1 / (8 : Error)) ≤
        mainFormalLinearTriangleRawError params k eps := by
    calc
      2221 * Real.rpow z (1 / (8 : Error)) ≤ 2221 * ((9 / 2 : Error) * X) :=
        mul_le_mul_of_nonneg_left hrootX (by norm_num)
      _ ≤ 10000 * X := by nlinarith
      _ = mainFormalLinearTriangleRawError params k eps := by
        unfold mainFormalLinearTriangleRawError
        simp only [X]
        ring
  have hzRoot0 : 0 ≤ Real.rpow z (1 / (8 : Error)) := Real.rpow_nonneg hz0 _
  have hzRootLt : Real.rpow z (1 / (8 : Error)) < 1 := by
    have hself : Real.rpow z (1 / (8 : Error)) ≤
        2221 * Real.rpow z (1 / (8 : Error)) := by nlinarith
    exact hself.trans_lt (h2221.trans_lt hsmall)
  have hz1 : z ≤ 1 := by
    rcases (Real.rpow_lt_one_iff hz0).mp hzRootLt with hzero | hneg | hlt
    · simp [hzero.1]
    · norm_num at hneg
    · exact hlt.1.le
  have hsToZ : s ≤ z / 6 := by
    dsimp [z]
    have hmdq0 : 0 ≤ (params.m : Error) * (params.d : Error) / (params.q : Error) := by
      positivity [h.dqNN]
    nlinarith
  have hzToRoot : z ≤ Real.rpow z (1 / (8 : Error)) :=
    self_le_rpow_one_div hz0 hz1 (by norm_num)
  have hquarterToRoot :
      Real.rpow z (1 / (4 : Error)) ≤ Real.rpow z (1 / (8 : Error)) :=
    rpow_le_of_denom_le hz0 hz1 (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (MakingMeasurementsProjective.orthonormalizationError z) =
      10 * Real.rpow z (1 / (8 : Error)) :=
    MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hz0
  have hpointExpand :
      3 * (s + eta + v / 2) =
        3 * s + 30 * z + 1800 * Real.rpow z (1 / (4 : Error)) +
          390 * Real.rpow z (1 / (8 : Error)) := by
    dsimp [eta, v, c]
    unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
    rw [hsqrt]
    unfold MakingMeasurementsProjective.orthonormalizationError
    simp only [← Real.rpow_eq_pow]
    ring_nf
  have hselfExpand :
      v / 2 = 9 * z + 600 * Real.rpow z (1 / (4 : Error)) +
        120 * Real.rpow z (1 / (8 : Error)) := by
    dsimp [v, c]
    unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
    rw [hsqrt]
    unfold MakingMeasurementsProjective.orthonormalizationError
    simp only [← Real.rpow_eq_pow]
    ring_nf
  constructor
  · rw [hpointExpand]
    apply le_trans (b := 2221 * Real.rpow z (1 / (8 : Error)))
    · nlinarith
    · exact h2221
  · rw [hselfExpand]
    apply le_trans (b := 2221 * Real.rpow z (1 / (8 : Error)))
    · nlinarith
    · exact h2221

end Test

end MIPStarRE.LDT
