import MIPStarRE.QPBT.Combining.Claims
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Applying the classical low-degree test

This module states the two application obligations at the end of the Pauli-basis
combining argument.  Directly indexed combined-line measurements are recorded both
with the error form printed in the source and with the weaker estimate established by
its first proof route.  The final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials.  The existence assertions below
record the measurements and quantitative estimates required by the combining argument;
their derivations remain open.

## References

The combined-line declarations record directly indexed auxiliary forms of
`lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Chaining Claims 17-1, 17-2, and 17-3 bounds the joint overlap on the
actual subline law. This is the first route to `eq:qld-combined-lines-consistency`,
paper `14_analysis_of_the_pauli_basis_test.tex:1134-1241`, with the corrected
claim errors documented in `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.
It uses no assertion about the joint conditional law of the two projected points.
The passage from this overlap to an extended-line POVM remains separate. -/
theorem subline_joint_overlap_near_one :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : AdmissibleParams) (error pointError lineError : ℝ)
        (setting : ProjectiveSetting params error)
        (points : CombinedPointsWitness setting pointError)
        (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params),
        |avgOver sublines.D (fun sample =>
            avgOver (uniformDistribution (DirectScalarQ params.extendedDirectLd)) (fun parameter =>
              let point := directPointToPauli params
                (sample.1.base + parameter • sample.1.direction)
              ∑ polyX, ∑ polyZ,
                (inner ℂ setting.psiHat ((EuclideanSpace.equiv
                  (SixReg params setting.toStrategy.ιA setting.toStrategy.ιB) ℂ).symm
                    ((setting.place .AA'
                        ((lines.T .alice sample.2.1 sample.2.2).effect (polyX, polyZ)) *
                      setting.place .BA''
                        (((points.Q .bob (projX point) (projZ point)).postprocess
                          (fun pair => (some pair.1, some pair.2))).effect
                            (evalOpt sample.2.1 (projX point) polyX,
                              evalOpt sample.2.2 (projZ point) polyZ))).mulVec
                                setting.psiHat))).re)) - 1| ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := by
  obtain ⟨firstConstant, hfirstConstant, hfirst⟩ := subline_replace_by_ordered_product
  obtain ⟨secondConstant, hsecondConstant, hsecond⟩ := subline_remove_X_factor
  obtain ⟨thirdConstant, hthirdConstant, hthird⟩ := subline_Z_term_near_one
  refine ⟨firstConstant + secondConstant + thirdConstant, by linarith, ?_⟩
  intro params error pointError lineError setting points lines sublines
  have hchain := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add (hfirst params error pointError lineError setting points lines sublines)
      ((abs_sub_le _ _ (1 : ℝ)).trans
        (add_le_add (hsecond params error pointError lineError setting points lines sublines)
          (hthird params error pointError lineError setting points lines sublines))))
  have hpointHalf : 0 ≤ pointError ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hsum : 0 ≤ lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) :=
    add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have herrorQuarter := rpow_quarter_nonneg error
  simp only [Real.rpow_eq_pow] at herrorQuarter
  have hdimension := Real.sqrt_nonneg (params.m : ℝ)
  have hbound : firstConstant * pointError ^ (1 / 2 : ℝ) +
      secondConstant * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ)) +
      thirdConstant * Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ)) ≤
      (firstConstant + secondConstant + thirdConstant) *
        (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
          (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ))) := by
    nlinarith [mul_nonneg hsecondConstant.le hpointHalf,
      mul_nonneg hthirdConstant.le hpointHalf,
      mul_nonneg (mul_nonneg hfirstConstant.le hdimension) hsum,
      mul_nonneg (mul_nonneg hfirstConstant.le hdimension) herrorQuarter,
      mul_nonneg (mul_nonneg hsecondConstant.le hdimension) herrorQuarter]
  exact hchain.trans (by simpa only [Real.rpow_eq_pow, add_assoc] using hbound)

/-- Polynomial absorption for the first combining route, including large errors.
The independent unit bound on consistency accounts for the minimum. The factor
`dimension` is retained, as required by the correction to `lem:qld-4-13` in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, paper lines 1134--1246. -/
theorem exists_combining_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  obtain ⟨pointConstant, pointPower, hpointConstant, hpointPower, hpointBound⟩ := hpoint
  obtain ⟨lineConstant, errorPower, ratioPower, hlineConstant,
    herrorPower, hratioPower, hlineBound⟩ := hline
  let finalPower := min (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
  let coefficient := pointConstant ^ (1 / 2 : ℝ) + lineConstant ^ (1 / 4 : ℝ) +
    pointConstant ^ (1 / 4 : ℝ) + 1
  let finalConstant := 1 + constant * coefficient
  have hfinalPower : 0 < finalPower := by dsimp [finalPower]; positivity
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hfinalConstant : 1 ≤ finalConstant := by
    dsimp [finalConstant]
    linarith [mul_nonneg hconstant hcoefficient]
  refine ⟨fun error ratio => finalConstant *
    (error ^ finalPower + ratio ^ (ratioPower / 4)),
    ⟨finalConstant, finalPower, ratioPower / 4, hfinalConstant, hfinalPower,
      by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg herror _)
      (Real.rpow_nonneg hratio _)), le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdimensionNonneg : 0 ≤ dimension := by linarith
  have herrorTerm : 0 ≤ error ^ finalPower := Real.rpow_nonneg herror _
  have hratioTerm : 0 ≤ ratio ^ (ratioPower / 4) := Real.rpow_nonneg hratio _
  by_cases herrorOne : error ≤ 1
  · have hpointValue := hpointBound error herror
    have hlineValue := hlineBound error ratio herror hratio
    have hpointRoot (power : ℝ) (hpower : 0 ≤ power)
        (hsmall : finalPower ≤ pointPower * power) :
        (pointError error) ^ power ≤ pointConstant ^ power * error ^ finalPower := by
      calc
        _ ≤ (pointConstant * error ^ pointPower) ^ power :=
          Real.rpow_le_rpow hpointValue.1 hpointValue.2 hpower
        _ = pointConstant ^ power * error ^ (pointPower * power) := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg herror _),
            ← Real.rpow_mul herror]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le hsmall)
          (Real.rpow_nonneg (by linarith) _)
    have hpointQuarter := hpointRoot (1 / 4) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hpointHalf := hpointRoot (1 / 2) (by norm_num)
      (by
        have := min_le_left (pointPower / 4) (min (errorPower / 4) (1 / 4 : ℝ))
        dsimp [finalPower]
        linarith)
    have hlineQuarter : (lineError error ratio) ^ (1 / 4 : ℝ) ≤
        lineConstant ^ (1 / 4 : ℝ) * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      calc
        _ ≤ (lineConstant * (error ^ errorPower + ratio ^ ratioPower)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlineValue.1 hlineValue.2 (by norm_num)
        _ = lineConstant ^ (1 / 4 : ℝ) *
            (error ^ errorPower + ratio ^ ratioPower) ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by linarith) (by positivity)]
        _ ≤ lineConstant ^ (1 / 4 : ℝ) *
            ((error ^ errorPower) ^ (1 / 4 : ℝ) +
              (ratio ^ ratioPower) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror _)
              (Real.rpow_nonneg hratio _) (by norm_num) (by norm_num))
            (Real.rpow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← Real.rpow_mul herror, ← Real.rpow_mul hratio]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          apply add_le_add _ (by simp [div_eq_mul_inv])
          apply Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
          have hsmall : finalPower ≤ errorPower / 4 :=
            (min_le_right _ _).trans (min_le_left _ _)
          linarith
    have herrorQuarter : error ^ (1 / 4 : ℝ) ≤ error ^ finalPower :=
      Real.rpow_le_rpow_of_exponent_ge' herror herrorOne hfinalPower.le
        ((min_le_right _ _).trans (min_le_right _ _))
    have hsqrt : Real.sqrt dimension ≤ dimension := by
      nlinarith [Real.sq_sqrt hdimensionNonneg, Real.sqrt_nonneg dimension]
    have hsum : (pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
        ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ)) ≤
        dimension * (coefficient * (error ^ finalPower + ratio ^ (ratioPower / 4))) := by
      have hrootNonneg : 0 ≤ (lineError error ratio) ^ (1 / 4 : ℝ) +
          (pointError error) ^ (1 / 4 : ℝ) + error ^ (1 / 4 : ℝ) :=
        add_nonneg (add_nonneg (Real.rpow_nonneg hlineValue.1 _)
          (Real.rpow_nonneg hpointValue.1 _)) (Real.rpow_nonneg herror _)
      have hrootSum := add_le_add (add_le_add hlineQuarter hpointQuarter) herrorQuarter
      have hscaled := mul_le_mul hsqrt hrootSum hrootNonneg hdimensionNonneg
      have hpointScaled := mul_le_mul_of_nonneg_right hdimension
        (Real.rpow_nonneg hpointValue.1 (1 / 2 : ℝ))
      dsimp [coefficient]
      nlinarith [mul_nonneg hdimensionNonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 2 : ℝ))
          hratioTerm),
        mul_nonneg hdimensionNonneg
          (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ pointConstant) (1 / 4 : ℝ))
            hratioTerm),
        mul_le_mul_of_nonneg_left hpointHalf hdimensionNonneg,
        mul_nonneg hdimensionNonneg hratioTerm]
    refine (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hsum hconstant).trans ?_)
    dsimp [finalConstant]
    nlinarith [mul_nonneg hdimensionNonneg (add_nonneg herrorTerm hratioTerm)]
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge herrorOne) hfinalPower.le
    have hsumOne : 1 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ finalConstant - 1 by linarith)
        (add_nonneg herrorTerm hratioTerm)]
    nlinarith [mul_nonneg (show 0 ≤ dimension - 1 by linarith)
      (show 0 ≤ finalConstant * (error ^ finalPower + ratio ^ (ratioPower / 4)) by linarith)]

/-- Conditional directly indexed construction of the extended-line measurements with
the error expression `poly(m^2 * epsilon, md / q)` printed in `lem:qld-4-13`, paper
lines 1020--1034. This is an auxiliary obligation, not the source-facing statement.

The printed proof does not establish this error form: its first route gives
`m * poly(epsilon, md / q)`, while its second route gives a different bound and
uses a joint-law decomposition absent from the subline lemma.  The discrepancy is
documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`rem:qld-4-13-source-defects` in the blueprint. `ExtendedLinesWitness` uses the
directly indexed question carrier and line-point law documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, and the completed answer
alphabet documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Their conversion to the source's verifier game remains open. This declaration takes
an already constructed point witness; the companion obligation below supplies that
witness existentially. Its polynomial point-error function is fixed before the
output error is chosen, as in `exists_combinedLinesWitness_ofPointsWitness`.
This removes the unrestricted supplied-error omission tracked by issue #118;
it does not discharge the separate printed-error obligation.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_ofPointsWitness (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε)),
        Nonempty (ExtendedLinesWitness S points
          (deltaCombine ((P.m : ℝ) ^ 2 * ε)
            ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-! The following directly indexed obligation supplies the point witness from
`lem:qld-4-10` rather than taking it as an external hypothesis. -/

/-- Directly indexed extended-line obligation with the numerical error expression
printed in `lem:qld-4-13`, paper lines 1020--1034.

The `_ofPointsWitness` companion assumes a point witness, while this declaration
supplies one existentially. Both declarations use the directly indexed questions,
law, and completed answer alphabet, so neither is the source-facing paper statement.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(m^2 * epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
          ∃ points : CombinedPointsWitness S (deltaQ ε),
            Nonempty (ExtendedLinesWitness S points
              (deltaCombine ((P.m : ℝ) ^ 2 * ε)
                ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨deltaCombine, hdeltaCombine, hlines⟩ :=
    exists_extendedLinesWitness_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, deltaCombine, hdeltaCombine, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩

/-- Construction of the extended-line measurements with the estimate actually
delivered by the first proof route, `C * m * poly(epsilon, md / q)`.

This is an established auxiliary form of the argument, not the source-labelled
`lem:qld-4-13`; it must not be advertised as that theorem. The source discrepancy
is analyzed in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. As in the
companion directly indexed declaration, the extended questions use the directly
indexed line-space construction. This conditional declaration takes an already
constructed point witness with its polynomial error function fixed before the
line error is chosen; the obligation below supplies it existentially. The first
route's joint-overlap estimate is proved by `subline_joint_overlap_near_one`.
Conditional averaging into the extended-line POVM, axis-degree support, and the
completed-evaluation comparison remain to discharge this obligation. Relating
its game to the source's seed-bearing game requires the transport and soundness
obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense.
-/
theorem exists_extendedLinesWitness_established_ofPointsWitness (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
          (points : CombinedPointsWitness S (deltaQ ε)),
          Nonempty (ExtendedLinesWitness S points
            (C * (P.m : ℝ) *
              deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  sorry

/-- Directly indexed construction for the auxiliary estimate
`C * m * poly(epsilon, md / q)`. This has the same directly indexed estimate as
`exists_extendedLinesWitness_established_ofPointsWitness`, with the point witness
existentially supplied rather than assumed.

Its question carrier and line-point law are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; its `Option`-completed answer
alphabet is documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Transport to `lem:qld-4-13` must convert this completed comparison to the source's
sum over field answers, including degenerate zero-direction singleton lines.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue #196.
Here `poly(epsilon, md / q)` is read in that sense. -/
theorem exists_extendedLinesWitness_established :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
          ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
            ∃ points : CombinedPointsWitness S (deltaQ ε),
              Nonempty (ExtendedLinesWitness S points
                (C * (P.m : ℝ) *
                  deltaCombine ε ((P.m * P.d : ℕ) / (P.q : ℝ)))) := by
  obtain ⟨deltaQ, hdeltaQ, hpoints⟩ := exists_combinedPointsWitness
  obtain ⟨C, hC, deltaCombine, hdeltaCombine, hlines⟩ :=
    exists_extendedLinesWitness_established_ofPointsWitness deltaQ hdeltaQ
  refine ⟨deltaQ, hdeltaQ, C, hC, deltaCombine, hdeltaCombine,
    fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε S points⟩

/-- Construction of the projective global polynomial-pair measurements from
`lem:qld-4-7`, paper lines 1267--1274.  The statement has the source's universal
constants and contains no divisibility hypothesis or residual construction input.

The argument uses low-degree soundness at dimension `2 * m + 2`.  The current
direct carrier realizes the required dimension without assuming
`2 * m + 2 ∣ q`, but it does not itself prove the game-correspondence and
auxiliary-parameter estimates required by the soundness import; those obligations
are exposed by `exists_direct_ld_soundness` and documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.  Absorption of the established
combined-lines prefactor into the final universal constants is to use
`deltaQld_mono` on its stated source parameter domain.
-/
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 < ε →
        ∀ S : ProjectiveSetting P ε,
          Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  sorry

end

end MIPStarRE.QPBT
