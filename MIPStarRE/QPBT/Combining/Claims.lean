import MIPStarRE.QPBT.Combining.OrderedPoints
import MIPStarRE.QPBT.Combining.Points.Placement
import MIPStarRE.QPBT.Combining.OverlapGap
import MIPStarRE.QPBT.Combining.SubLineDeficit
import MIPStarRE.QPBT.Combining.UniformLinePoint
import MIPStarRE.QPBT.Combining.Witnesses

/-!
# Scalar claims for combining the Pauli bases

This module states the three scalar estimates used to compare the paired line
measurement with the joint and ordered point measurements.  The expectations
retain the subline law and the uniform affine parameter on each extended line
explicitly.  Line-polynomial evaluation uses the existing `Option` completion,
so no field value is substituted when an evaluation is undefined.

The second estimate is stated with the error `√m (δ_P^{1/4} + δ_Q^{1/4})` in
place of the source error `m δ_Line^{1/2}`: the source proof identifies the
`X`-marginal of the paired-line measurement with the `X`-line measurement
through the sandwich form of that measurement, which is a definition internal
to the proof of `lem:qld-xz-lines` and not a property recorded in its
conclusion; the estimate proved here uses only the consistency conclusion of
`lem:qld-xz-lines`.  See `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

The claims are `lem:claim-17-1`, `lem:claim-17-2`, and `lem:claim-17-3` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1140-1239`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Numerical support -/

/-- The fourth root of a real number, as a real power, is nonnegative. -/
theorem rpow_quarter_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / 4 : ℝ) := by
  change 0 ≤ x ^ (1 / 4 : ℝ)
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx,
      show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  · exact Real.rpow_nonneg hx _

/-- The square root of the inflated deficit bound is at most
`2 √m (δ_P^{1/4} + δ_Q^{1/4})`. -/
theorem sqrt_deficit_bound_le (m δP δQ : ℝ) (hm : 1 ≤ m) (hP : 0 ≤ δP)
    (hQ : 0 ≤ δQ) :
    Real.sqrt (2 * Real.sqrt (4 * m ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) ≤
      2 * Real.sqrt m * (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  have hm0 : 0 ≤ m := by linarith
  have hsqrtm : 1 ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  have h1 : Real.sqrt (4 * m ^ 2 * δP) = 2 * m * Real.sqrt δP := by
    rw [Real.sqrt_mul (by positivity), show (4 * m ^ 2 : ℝ) = (2 * m) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  have h2 : Real.sqrt (4 * δQ) = 2 * Real.sqrt δQ := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hquarter : ∀ x : ℝ, 0 ≤ x →
      Real.sqrt (Real.sqrt x) = Real.rpow x (1 / 4 : ℝ) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  have hsplit : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a,
      Real.sqrt_nonneg b]
  have hPa : 0 ≤ 2 * (2 * m * Real.sqrt δP) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) hm0) (Real.sqrt_nonneg _))
  have hQa : 0 ≤ 2 * (2 * Real.sqrt δQ) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hPb : Real.sqrt (2 * (2 * m * Real.sqrt δP)) =
      2 * Real.sqrt m * Real.rpow δP (1 / 4 : ℝ) := by
    rw [show 2 * (2 * m * Real.sqrt δP) = 2 ^ 2 * m * Real.sqrt δP by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), hquarter δP hP]
  have hQb : Real.sqrt (2 * (2 * Real.sqrt δQ)) = 2 * Real.rpow δQ (1 / 4 : ℝ) := by
    rw [show 2 * (2 * Real.sqrt δQ) = 2 ^ 2 * Real.sqrt δQ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), hquarter δQ hQ]
  rw [h1, h2]
  calc
    Real.sqrt (2 * (2 * m * Real.sqrt δP) + 2 * (2 * Real.sqrt δQ))
        ≤ Real.sqrt (2 * (2 * m * Real.sqrt δP)) +
          Real.sqrt (2 * (2 * Real.sqrt δQ)) := hsplit _ _ hPa hQa
    _ = 2 * Real.sqrt m * Real.rpow δP (1 / 4 : ℝ) +
          2 * Real.rpow δQ (1 / 4 : ℝ) := by rw [hPb, hQb]
    _ ≤ 2 * Real.sqrt m *
          (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
      have hQ4 : 0 ≤ Real.rpow δQ (1 / 4 : ℝ) := Real.rpow_nonneg hQ _
      nlinarith [hsqrtm, hQ4]

/-! ## The three claims -/

/-- Replacing the combined point measurement by the ordered `Z`-then-`X`
point product costs a square-root joint-point error.  This is
`lem:claim-17-1`, paper lines 1140--1145. -/
theorem subline_replace_by_ordered_product :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (((points.Q .bob x z).postprocess fun ab =>
                          (some ab.1, some ab.2)).effect
                            (evalOpt sample.2.1 x fX,
                              evalOpt sample.2.2 z fZ))).mulVec S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re))| ≤
          C * Real.rpow δQ (1 / 2 : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines
  classical
  have hside := sublines.avgOver_regrouped_eq lines
  have hprob : (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))).IsProbability :=
    Distribution.prod_isProbability _ _ sublines.isProbability
      (uniformDistribution_isProbability _)
  have hdist : opFamilyDistSq
      (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
          (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place .BA''
        (((points.Q .bob
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).postprocess fun ab =>
          (some ab.1, some ab.2)).effect (o.1, o.2)))
      (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
          (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place .BA''
        ((S.pointMeasExpOption .bob .Z
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption .bob .X
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
      S.psiHat ≤ 4 * δQ := by
    calc opFamilyDistSq
          (Distribution.prod sublines.D
            (uniformDistribution (DirectScalarQ P.extendedDirectLd))) _ _
          S.psiHat =
        avgOver (Distribution.prod sublines.D
            (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
          (fun s => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob
                  (projX (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))
                  (projZ (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction)))).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z
                      (projZ (directPointToPauli P
                        (s.1.1.base + s.2 • s.1.1.direction)))).effect ab.2 *
                    (S.pointMeasExp .bob .X
                      (projX (directPointToPauli P
                        (s.1.1.base + s.2 • s.1.1.direction)))).effect ab.1))
              S.psiHat‖ ^ 2) :=
        avgOver_congr _ _ _ fun s =>
          S.completedPair_norm_sq_sum_ZX points .BA'' _ _
      _ = avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
              (fun t => ∑ ab : PauliScalar P × PauliScalar P,
                ‖applyOperatorToState
                  (S.place .BA'' ((points.Q .bob
                      (projX (directPointToPauli P
                        (sample.1.base + t • sample.1.direction)))
                      (projZ (directPointToPauli P
                        (sample.1.base + t • sample.1.direction)))).effect ab) -
                    S.place .BA''
                      ((S.pointMeasExp .bob .Z
                          (projZ (directPointToPauli P
                            (sample.1.base + t • sample.1.direction)))).effect
                            ab.2 *
                        (S.pointMeasExp .bob .X
                          (projX (directPointToPauli P
                            (sample.1.base + t • sample.1.direction)))).effect
                            ab.1))
                  S.psiHat‖ ^ 2)) :=
        avgOver_prod _ _ _
      _ = avgOver (uniformDistribution
            ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
          (fun xz => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z xz.2).effect ab.2 *
                    (S.pointMeasExp .bob .X xz.1).effect ab.1))
              S.psiHat‖ ^ 2) :=
        SubLineWitness.avgOver_projX_projZ P sublines
          (fun xz => ∑ ab : PauliScalar P × PauliScalar P,
            ‖applyOperatorToState
              (S.place .BA'' ((points.Q .bob xz.1 xz.2).effect ab) -
                S.place .BA''
                  ((S.pointMeasExp .bob .Z xz.2).effect ab.2 *
                    (S.pointMeasExp .bob .X xz.1).effect ab.1))
              S.psiHat‖ ^ 2)
      _ ≤ 4 * δQ := points.orderedZX_dist_le .BA''
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq
    (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun s => S.placedMeasurement .AA'
      ((lines.T .alice s.1.2.1 s.1.2.2).postprocess (fun fs =>
        (evalOpt s.1.2.1 (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
          evalOpt s.1.2.2 (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.2))))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA''
      (((points.Q .bob
          (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))
          (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).postprocess fun ab =>
        (some ab.1, some ab.2)).effect (o.1, o.2)))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA''
      ((S.pointMeasExpOption .bob .Z
          (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
        (S.pointMeasExpOption .bob .X
          (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    S.psiHat hprob S.psiHat_norm (4 * δQ) hdist
  simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rw [hside (fun x z o1 o2 => ((points.Q .bob x z).postprocess fun ab =>
      (some ab.1, some ab.2)).effect (o1, o2)),
    hside (fun x z o1 o2 => (S.pointMeasExpOption .bob .Z z).effect o2 *
      (S.pointMeasExpOption .bob .X x).effect o1)]
  refine hgap.trans ?_
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4, Real.sqrt_eq_rpow]
  exact le_rfl

/-- Removing the trailing `X`-point factor costs the fourth root of the
inflated line and point consistency errors, with the source factor `√m`.  This
is `lem:claim-17-2`, paper lines 1168--1173, with the right-hand point being
the corrected lowercase `z` recorded in the blueprint, and with the error
`√m (δ_P^{1/4} + δ_Q^{1/4})` of the proof from the consistency conclusion of
`lem:qld-xz-lines` in place of the source error `m δ_Line^{1/2}`, whose
derivation uses the sandwich form of the paired-line measurement; see
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. -/
theorem subline_remove_X_factor :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let x := projX u
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ *
                          S.expPointEffectAtLineAnswer .bob .X sample.2.1 x fX)).mulVec
                            S.psiHat))).re)) -
          avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re))| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines
  classical
  have hside := sublines.avgOver_regrouped_eq lines
  have hprob : (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))).IsProbability :=
    Distribution.prod_isProbability _ _ sublines.isProbability
      (uniformDistribution_isProbability _)
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent .AA' .BA'' trivial)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S .AA' .BA'' trivial
        ((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q .bob s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent .AA' .BA'' trivial)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  simp only [← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
  rw [hside (fun x z o1 o2 => (S.pointMeasExpOption .bob .Z z).effect o2 *
      (S.pointMeasExpOption .bob .X x).effect o1),
    hside (fun x z o1 o2 => (S.pointMeasExpOption .bob .Z z).effect o2)]
  have hcs := abs_overlap_gap_le_sqrt_one_sub_of_isProj'
    (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun s => S.placedMeasurement .AA'
      ((lines.T .alice s.1.2.1 s.1.2.2).postprocess (fun fs =>
        (evalOpt s.1.2.1 (projX (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
          evalOpt s.1.2.2 (projZ (directPointToPauli P
            (s.1.1.base + s.2 • s.1.1.direction))) fs.2))))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA'' ((S.pointMeasExpOption .bob .X
        (projX (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA'' ((S.pointMeasExpOption .bob .Z
        (projZ (directPointToPauli P
          (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2))
    (fun (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd)
        (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
      S.place .BA''
        ((S.pointMeasExpOption .bob .Z
            (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption .bob .X
            (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
    S.psiHat hprob S.psiHat_norm
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
    (fun s o => S.place_AA'_mul_place_BA''_comm _ _)
    (fun s o => S.place_AA'_mul_place_BA''_comm _ _)
    (fun s o => ProjectiveSetting.place_mul S .BA'' _ _)
  refine hcs.trans ?_
  have hrew : avgOver (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement .AA'
            ((lines.T .alice s.1.2.1 s.1.2.2).postprocess (fun fs =>
              (evalOpt s.1.2.1 (projX (directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                evalOpt s.1.2.2 (projZ (directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
            S.place .BA'' ((S.pointMeasExpOption .bob .X
              (projX (directPointToPauli P
                (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => xPointOverlap lines (sample.2, projX (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    rw [avgOver_prod]
    refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
    exact regroup_line_answer_sum lines sample.2.1 sample.2.2 _ _
      (fun o1 _ => (S.pointMeasExpOption .bob .X (projX (directPointToPauli P
        (sample.1.base + t • sample.1.direction)))).effect o1)
  refine (Real.sqrt_le_sqrt ?_).trans (sqrt_deficit_bound_le _ _ _ hm hδP hδQ)
  have hX := sublines.one_sub_avgOver_xPointOverlap_le lines
  rw [← hrew] at hX
  exact hX

/-- The remaining `Z`-point correlation is close to one with the fourth-root
error from the point and line constructions.  This is `lem:claim-17-3`, paper
lines 1204--1209.  The proof bounds the deficit of the correlation directly
from the consistency conclusion of `lem:qld-xz-lines` transported to the
sub-line law; the source's Cauchy--Schwarz step and its
`ε`-dependent self-consistency term are not needed, and the stated error
retains the source's `ε^{1/4}` term only for fidelity. -/
theorem subline_Z_term_near_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : AdmissibleParams) (ε δQ δP : ℝ)
        (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
        (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
              let u := directPointToPauli P
                (sample.1.base + t • sample.1.direction)
              let z := projZ u
              ∑ fX, ∑ fZ,
                (inner ℂ S.psiHat ((EuclideanSpace.equiv
                  (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
                    ((S.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                      S.place .BA''
                        (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                          S.psiHat))).re)) - 1| ≤
          C * Real.sqrt (P.m : ℝ) *
            (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ) +
              Real.rpow ε (1 / 4 : ℝ)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro P ε δQ δP S points lines sublines
  classical
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent .AA' .BA'' trivial)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S .AA' .BA'' trivial
        ((lines.T .alice s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q .bob s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent .AA' .BA'' trivial)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hLHS : avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        let u := directPointToPauli P
          (sample.1.base + t • sample.1.direction)
        let z := projZ u
        ∑ fX, ∑ fZ,
          (inner ℂ S.psiHat ((EuclideanSpace.equiv
            (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
              ((S.place .AA'
                  ((lines.T .alice sample.2.1 sample.2.2).effect (fX, fZ)) *
                S.place .BA''
                  (S.expPointEffectAtLineAnswer .bob .Z sample.2.2 z fZ)).mulVec
                    S.psiHat))).re)) =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
    simp only [zPointOverlap, ← ProjectiveSetting.pointMeasExpOption_effect_evalOpt]
    rfl
  rw [hLHS]
  set L := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
      (fun t => zPointOverlap lines (sample.2, projZ (directPointToPauli P
        (sample.1.base + t • sample.1.direction))))) with hL
  have hdef := sublines.one_sub_avgOver_zPointOverlap_le lines
  have hle := sublines.avgOver_zPointOverlap_le_one lines
  have hnonneg : 0 ≤ L :=
    avgOver_nonneg _ _ fun sample => avgOver_nonneg _ _ fun t =>
      zPointOverlap_nonneg lines _
  rw [← hL] at hdef hle
  have h0 : 0 ≤ 1 - L := by linarith
  have hsq : (1 - L) ^ 2 ≤ 1 - L := by nlinarith
  calc
    |L - 1| = 1 - L := by rw [abs_sub_comm, abs_of_nonneg h0]
    _ = Real.sqrt ((1 - L) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) +
          2 * Real.sqrt (4 * δQ)) := Real.sqrt_le_sqrt (hsq.trans hdef)
    _ ≤ 2 * Real.sqrt (P.m : ℝ) *
          (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) :=
      sqrt_deficit_bound_le _ _ _ hm hδP hδQ
    _ ≤ _ := by
      have hε := rpow_quarter_nonneg ε
      have hsm : 0 ≤ 2 * Real.sqrt (P.m : ℝ) :=
        mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
      nlinarith [mul_nonneg hsm hε]

end

end MIPStarRE.QPBT
