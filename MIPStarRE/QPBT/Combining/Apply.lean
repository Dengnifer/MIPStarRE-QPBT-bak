import MIPStarRE.QPBT.Combining.Points
import MIPStarRE.QPBT.Test.SoundnessDefs

/-!
# Applying the classical low-degree test

This module proves the algebraic restriction and projective completion of a
measurement on extended polynomials to polynomial pairs, and states the remaining
application obligations at the end of the Pauli-basis combining argument.
Directly indexed combined-line measurements are recorded both
with the error form printed in the source and with the weaker estimate established by
its first proof route.  The final witness consists of a projective measurement of a
pair of global bounded individual-degree polynomials.  The existence assertions below
record the measurements and quantitative estimates required by the combining argument;
their quantitative derivations remain open.

## References

The combined-line declarations record directly indexed auxiliary forms of
`lem:qld-4-13` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`.
The global-pair declaration formalizes `lem:qld-4-7` in the same blueprint, with
paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1274`.
-/

namespace MIPStarRE.QPBT

open scoped BigOperators MatrixOrder

noncomputable section

/-- Recover the two polynomial components by setting the unused block to zero
and the scalar coordinates to `(1,0)` or `(0,1)`. This algebraic substitution
is the left inverse implicit in the restriction to combined outcomes in
`eq:qld-sgg-completeness`, paper lines 1375--1380. Unlike evaluation as a
polynomial function on a finite field, it does not require a degree bound. -/
noncomputable def recoverCombinedPair {K : Type*} [CommSemiring K] {m : ℕ}
    (polynomial : MvPolynomial (Fin (2 * m + 2)) K) :
    MvPolynomial (Fin m) K × MvPolynomial (Fin m) K :=
  (MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl coordinate) => MvPolynomial.X coordinate
    | .inl (.inr _) => 0
    | .inr scalar => if scalar = 0 then 1 else 0) polynomial,
   MvPolynomial.eval₂ MvPolynomial.C (fun index =>
    match finCombineEquiv m index with
    | .inl (.inl _) => 0
    | .inl (.inr coordinate) => MvPolynomial.X coordinate
    | .inr scalar => if scalar = 1 then 1 else 0) polynomial)

/-- Substitution recovers both components of a combined polynomial. This is
formalization support for the relabeling in `eq:qld-sgg-completeness`, paper
lines 1375--1380. -/
@[simp] theorem recoverCombinedPair_combinePoly {K : Type*} [CommSemiring K] {m : ℕ}
    (first second : MvPolynomial (Fin m) K) :
    recoverCombinedPair (combinePoly first second) = (first, second) := by
  simp [recoverCombinedPair, combinePoly, MvPolynomial.eval₂_rename,
    embX, embZ, alphaVar, betaVar, Function.comp_def, MvPolynomial.eval₂_eta]

/-- Distinct polynomial pairs label distinct combined outcomes. This justifies
restricting a measurement on extended polynomials to pairs without duplicating
an effect in `eq:qld-sgg-completeness`, paper lines 1375--1380. -/
theorem combinePoly_injective {K : Type*} [CommSemiring K] {m : ℕ} :
    Function.Injective (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) := by
  exact (show Function.LeftInverse recoverCombinedPair
    (fun pair : MvPolynomial (Fin m) K × MvPolynomial (Fin m) K =>
      combinePoly pair.1 pair.2) from fun pair =>
        recoverCombinedPair_combinePoly pair.1 pair.2).injective

/-- The bounded polynomial-pair embedding used to restrict the global
measurement in `eq:qld-sgg-completeness`, paper lines 1375--1380. The degree
bound is inherited from `def:combine-map`; the two scalar coordinates have
degree one, allowed by admissibility. -/
noncomputable def combinedPolyEmbedding (P : AdmissibleParams) :
    PolyPair P ↪ MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d where
  toFun pair := ⟨combinePoly pair.1.1 pair.2.1,
    combinePoly_mem_polyFunc P.hd pair.1.2 pair.2.2⟩
  inj' := by
    intro first second heq
    have hpoly : combinePoly first.1.1 first.2.1 = combinePoly second.1.1 second.2.1 :=
      congrArg Subtype.val heq
    have hpair : (first.1.1, first.2.1) = (second.1.1, second.2.1) :=
      combinePoly_injective hpoly
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))

/-- Restrict an extended-polynomial measurement to combined outcomes, as in
`eq:qld-sgg-completeness`, paper lines 1375--1380. Injectivity of the combining
map ensures that the retained effects sum to at most the identity. This
construction does not assert the source's quantitative completeness bound. -/
noncomputable def combinedPairSubmeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier) :
    Quantum.Submeasurement (PolyPair P) carrier where
  effect pair := measurement.effect (combinedPolyEmbedding P pair)
  pos pair := measurement.pos _
  sum_le_one := by
    classical
    rw [← Finset.sum_image (fun first _ second _ heq =>
      (combinedPolyEmbedding P).injective heq)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun outcome _ _ => measurement.pos outcome)).trans measurement.sum_le_one

/-- Restricting to combined outcomes preserves projectivity, as asserted
before `eq:qld-sgg-completeness`, paper lines 1375--1380. -/
theorem combinedPairSubmeasurement_projective (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (hprojective : Measurement.IsProjective measurement) :
    ∀ pair, Quantum.IsProj ((combinedPairSubmeasurement P measurement).effect pair) := by
  intro pair
  exact hprojective (combinedPolyEmbedding P pair)

/-- The missing operator of the polynomial-pair submeasurement is exactly the
sum of the effects outside the range of the combining map. This is the
operator identity underlying `eq:qld-sgg-completeness`, paper lines 1375--1380;
the bound on its state mass is a separate obligation. -/
theorem combinedPairSubmeasurement_missing (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier) :
    1 - (combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        measurement.effect polynomial := by
  classical
  have htotal : (combinedPairSubmeasurement P measurement).total =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P)),
        measurement.effect polynomial := by
    change (∑ pair, measurement.effect (combinedPolyEmbedding P pair)) = _
    rw [← Finset.sum_image (fun first _ second _ heq =>
      (combinedPolyEmbedding P).injective heq)]
    congr 1
    ext polynomial
    simp
  rw [htotal, ← measurement.sum_eq_one]
  apply sub_eq_iff_eq_add.mpr
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P))
    measurement.effect).symm.trans (add_comm _ _)

/-- Relabel a combined polynomial by its unique pair and send every other
polynomial to a specified pair. This implements the completion at an arbitrary
outcome in the last paragraph of `lem:qld-4-7`, paper lines 1402--1404. The
noncombined outcomes are retained at the completion outcome, not discarded. -/
noncomputable def completedPairLabel (P : AdmissibleParams) (completionPair : PolyPair P) :
    MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d → PolyPair P :=
  Function.extend (combinedPolyEmbedding P) id (fun _ => completionPair)

/-- Completion preserves every combined polynomial's pair label. -/
@[simp] theorem completedPairLabel_combinedPolyEmbedding (P : AdmissibleParams)
    (completionPair pair : PolyPair P) :
    completedPairLabel P completionPair (combinedPolyEmbedding P pair) = pair := by
  exact (combinedPolyEmbedding P).injective.extend_apply _ _ _

/-- All outcomes outside the combining map's range go to the completion pair. -/
theorem completedPairLabel_of_not_mem_range (P : AdmissibleParams)
    (completionPair : PolyPair P)
    (polynomial : MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d)
    (houtside : polynomial ∉ Set.range (combinedPolyEmbedding P)) :
    completedPairLabel P completionPair polynomial = completionPair := by
  exact Function.extend_apply' _ _ _ houtside

/-- The completed polynomial-pair measurement of the final paragraph of
`lem:qld-4-7`, paper lines 1402--1404, obtained by relabeling all extended
polynomial outcomes. No assertion about consistency is built into this
construction. -/
noncomputable def completedPairMeasurement (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair : PolyPair P) : Quantum.Measurement (PolyPair P) carrier :=
  measurement.postprocess (completedPairLabel P completionPair)

/-- Completing the pair measurement adds precisely its missing operator to
the specified outcome and leaves all other effects unchanged. This is the
completion formula of `lem:qld-4-7`, paper lines 1402--1404. -/
theorem completedPairMeasurement_effect (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (completionPair pair : PolyPair P) :
    (completedPairMeasurement P measurement completionPair).effect pair =
      (combinedPairSubmeasurement P measurement).effect pair +
        if pair = completionPair then 1 - (combinedPairSubmeasurement P measurement).total
        else 0 := by
  classical
  rw [completedPairMeasurement, Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P))]
  have hgood :
      Finset.univ.filter (fun polynomial => polynomial ∈ Set.range (combinedPolyEmbedding P)) =
        Finset.univ.image (combinedPolyEmbedding P) := by
    ext polynomial
    simp
  rw [hgood, Finset.sum_image (fun first _ second _ heq =>
    (combinedPolyEmbedding P).injective heq)]
  simp only [completedPairLabel_combinedPolyEmbedding]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ pair)]
  congr 1
  have hbad :
      (∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        if completedPairLabel P completionPair polynomial = pair then
          measurement.effect polynomial else 0) =
      ∑ polynomial ∈ Finset.univ.filter
        (fun polynomial => polynomial ∉ Set.range (combinedPolyEmbedding P)),
        if completionPair = pair then measurement.effect polynomial else 0 := by
    apply Finset.sum_congr rfl
    intro polynomial hpolynomial
    rw [completedPairLabel_of_not_mem_range P completionPair polynomial
      (Finset.mem_filter.mp hpolynomial).2]
  rw [hbad]
  by_cases heq : pair = completionPair
  · simp [heq, combinedPairSubmeasurement_missing]
  · simp [heq, Ne.symm heq]

/-- The completed polynomial-pair measurement is projective whenever the
extended-polynomial measurement is projective. This proves the qualitative
completion step in `lem:qld-4-7`, paper lines 1402--1404, without assuming its
unproved consistency conclusion. -/
theorem completedPairMeasurement_projective (P : AdmissibleParams)
    {carrier : Type*} [Fintype carrier] [DecidableEq carrier]
    (measurement : Quantum.Measurement
      (MIPStarRE.LDT.Preliminaries.polyFunc (2 * P.m + 2) (PauliScalar P) P.d) carrier)
    (hprojective : Measurement.IsProjective measurement) (completionPair : PolyPair P) :
    Measurement.IsProjective (completedPairMeasurement P measurement completionPair) := by
  exact SandwichProduct.postprocess_isProjective measurement hprojective _

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
witness existentially.
-/
theorem exists_extendedLinesWitness_ofPointsWitness :
    ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
      ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S δQ),
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

**Unfaithful:** The proof uses `exists_extendedLinesWitness_ofPointsWitness`, whose
construction and printed error estimate remain unproved. The discrepancy is recorded
in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. Discharge requires the
combined-line construction and the stated numerical estimate; this existential
assembly alone does not discharge either obligation. -/
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
    exists_extendedLinesWitness_ofPointsWitness
  refine ⟨deltaQ, hdeltaQ, deltaCombine, hdeltaCombine, fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε (deltaQ ε) S points⟩

/-- Construction of the extended-line measurements with the estimate actually
delivered by the first proof route, `C * m * poly(epsilon, md / q)`.

This is an established auxiliary form of the argument, not the source-labelled
`lem:qld-4-13`; it must not be advertised as that theorem. The source discrepancy
is analyzed in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. As in the
companion directly indexed declaration, the extended questions use the directly
indexed line-space construction. This conditional declaration takes an already
constructed point witness; the obligation below supplies it existentially. Relating
its game to the source's seed-bearing game requires the transport and soundness
obligations in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
theorem exists_extendedLinesWitness_established_ofPointsWitness :
    ∃ C : ℝ, 0 < C ∧
      ∃ deltaCombine : ℝ → ℝ → ℝ, IsPolyErr₂ deltaCombine ∧
        ∀ (P : AdmissibleParams) (ε δQ : ℝ) (S : ProjectiveSetting P ε)
          (points : CombinedPointsWitness S δQ),
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

**Unfaithful:** The proof uses
`exists_extendedLinesWitness_established_ofPointsWitness`, whose construction remains
open under issue #118 and `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
Discharge requires proving that construction from the displayed hypotheses. -/
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
    exists_extendedLinesWitness_established_ofPointsWitness
  refine ⟨deltaQ, hdeltaQ, C, hC, deltaCombine, hdeltaCombine,
    fun P ε S => ?_⟩
  obtain ⟨points⟩ := hpoints P ε S
  exact ⟨points, hlines P ε (deltaQ ε) S points⟩

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

**Unfaithful:** The extended-line strategy, the bound on noncombined polynomial
mass, and the transfer of consistency to the completed pair measurement remain
unproved in issue #119. The upstream transport obligations are documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; the line estimate is documented
in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. Discharge requires deriving
these estimates from the projective setting. `combinedPairSubmeasurement_missing`
and `completedPairMeasurement_effect` prove only the exact operator identities,
not their quantitative state-dependent bounds.
-/
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 < ε →
        ∀ S : ProjectiveSetting P ε,
          Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q)) := by
  sorry

end

end MIPStarRE.QPBT
