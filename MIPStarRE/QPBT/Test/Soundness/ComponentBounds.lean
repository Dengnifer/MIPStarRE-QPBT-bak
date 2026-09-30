import MIPStarRE.QPBT.Test.Soundness.RawOperatorTransfer

/-!
# Componentwise Pauli soundness bounds

The fixed-coefficient extraction estimates are retained separately through the
swap-isometry, Naimark, and raw-effect transfers. This module constructs one
soundness witness whose state and operator bounds use those stronger components
rather than the common extraction envelope.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and the extraction and final transfer argument in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

/-- A supplied global polynomial-pair witness determines one extraction
witness whose underlying auxiliary vector retains the stronger fixed-component
state and swapped-Pauli estimates. The extraction witness has common error
`18 * (x + sqrt x + r)`; the two displayed estimates retain the sharper
components for the same auxiliary vector.

**Unfaithful:** The global measurement is supplied as `GlobalPairWitness`,
rather than constructed from paper `lem:qld-4-7`. This is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #123. Elimination: compose
this theorem with the construction of the global witness from the test hypotheses. -/
theorem exists_extraction_witness_with_component_bounds
    (P : AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
    let x : ℝ := 2800 * (deltaG + Real.sqrt epsilon + r)
    ∃ v : ExtractionWitness S w (18 * (x + Real.sqrt x + r)),
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
          S.idealExpState v.aux‖ ^ 2 ≤ 16 * x ∧
      ∀ (side : PlayerSide) (W : PauliKind),
        opFamilyDistSq (uniformDistribution Unit)
          (fun (_ : Unit) (h : PauliRegister P) =>
            conjBy (S.placeSide side (swapUnitary w side))
              (S.placePlayer side ((S.pauliMeas side W).effect h)))
          (fun (_ : Unit) (h : PauliRegister P) =>
            S.placeExtractedRegister side (pauliProj W h))
          (S.idealExpState v.aux) ≤ 2 * x + 2 * r + 16 * Real.sqrt x := by
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
  let x : ℝ := 2800 * (deltaG + Real.sqrt epsilon + r)
  change ∃ v : ExtractionWitness S w (18 * (x + Real.sqrt x + r)),
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 ≤ 16 * x ∧
    ∀ (side : PlayerSide) (W : PauliKind),
      opFamilyDistSq (uniformDistribution Unit)
        (fun (_ : Unit) (h : PauliRegister P) =>
          conjBy (S.placeSide side (swapUnitary w side))
            (S.placePlayer side ((S.pauliMeas side W).effect h)))
        (fun (_ : Unit) (h : PauliRegister P) =>
          S.placeExtractedRegister side (pauliProj W h))
        (S.idealExpState v.aux) ≤ 2 * x + 2 * r + 16 * Real.sqrt x
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  obtain ⟨aux, haux, hstate⟩ :=
    exists_extraction_aux_of_global_pair_witness_explicit
      P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
  have hstate_x :
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ^ 2 ≤ 16 * x := by
    simpa only [x, r, deltaConstructPaulis, pauliBaselineExtractionConstant] using hstate
  have hstate_norm :
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ≤ 4 * Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, norm_nonneg
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux)]
  have hcoefficient : 2 + 4 * Real.sqrt 172 ≤ (2800 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (172 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 172)]
  have hbase : 0 ≤ deltaG + Real.sqrt epsilon + r := by positivity
  have hconstruct :
      deltaConstructPaulis (2 + 4 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q ≤ x := by
    dsimp only [deltaConstructPaulis, x, r, pauliBaselineExtractionConstant]
    exact mul_le_mul_of_nonneg_right hcoefficient hbase
  have hdefect (side : PlayerSide) (W : PauliKind) :
      S.evaluatedPauliDefect w side W ≤ x := by
    have hevaluated :=
      evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
        P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W
    cases side with
    | alice => exact hevaluated.1.trans hconstruct
    | bob => exact hevaluated.2.trans hconstruct
  have hswap (side : PlayerSide) (W : PauliKind) :
      opFamilyDistSq (uniformDistribution Unit)
        (fun (_ : Unit) (h : PauliRegister P) =>
          conjBy (S.placeSide side (swapUnitary w side))
            (S.placePlayer side ((S.pauliMeas side W).effect h)))
        (fun (_ : Unit) (h : PauliRegister P) =>
          S.placeExtractedRegister side (pauliProj W h))
        (S.idealExpState aux) ≤ 2 * x + 2 * r + 16 * Real.sqrt x := by
    calc
      _ ≤ 2 * S.evaluatedPauliDefect w side W + 2 * r +
          4 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
            S.idealExpState aux‖ := by
        simpa only [r, Nat.cast_mul] using S.extraction_pauli_dist_le w aux haux side W
      _ ≤ 2 * x + 2 * r + 16 * Real.sqrt x := by
        nlinarith [hdefect side W, hstate_norm]
  have hstate_scale :
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
          S.idealExpState aux‖ ^ 2 ≤ 18 * (x + Real.sqrt x + r) := by
    nlinarith [hstate_x, Real.sqrt_nonneg x]
  have hswap_scale (side : PlayerSide) (W : PauliKind) :
      opFamilyDistSq (uniformDistribution Unit)
        (fun (_ : Unit) (h : PauliRegister P) =>
          conjBy (S.placeSide side (swapUnitary w side))
            (S.placePlayer side ((S.pauliMeas side W).effect h)))
        (fun (_ : Unit) (h : PauliRegister P) =>
          S.placeExtractedRegister side (pauliProj W h))
        (S.idealExpState aux) ≤ 18 * (x + Real.sqrt x + r) := by
    nlinarith [hswap side W, Real.sqrt_nonneg x]
  let v : ExtractionWitness S w (18 * (x + Real.sqrt x + r)) := {
    swap_right_unitary := swapUnitary_mul_conjTranspose w
    swap_left_unitary := conjTranspose_mul_swapUnitary w
    aux := aux
    aux_norm := haux
    state_close := hstate_scale
    pauli_close := hswap_scale
  }
  refine ⟨v, ?_, ?_⟩
  · simpa only [v] using hstate_x
  · intro side W
    simpa only [v] using hswap side W

/-- Componentwise transfer from a supplied global polynomial-pair witness to
one witness for the original arbitrary strategy. For
`x = 2800 * (deltaG + sqrt epsilon + md/q)`, the same witness has squared state
error at most `16*x` and both raw Pauli-family distances at most
`472*x + 24*(md/q) + 192*sqrt x + 344*epsilon`.

The proof keeps the actual state error through `ExtractionWitness.state_error_eq`
and `pauli_naimark_witness_state_distance_eq`, and supplies that actual norm to
the raw-effect transfer theorem.

**Unfaithful:** The global measurement is supplied as `GlobalPairWitness`,
rather than constructed from paper `lem:qld-4-7`. This conditional theorem is
documented in `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue #123.
Elimination: construct the global witness from the test hypotheses before using
this result to prove paper `thm:pauli` from its stated assumptions. -/
theorem exists_pauli_soundness_witness_with_component_bounds
    (P : AdmissibleParams) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1)
    (R : Strategy (pauliBasisTest P)) (hwin : 1 - epsilon ≤ R.value)
    (deltaG : ℝ) (hdeltaG : 0 ≤ deltaG)
    (w : GlobalPairWitness (pauliNaimarkSetting P epsilon R hwin) deltaG) :
    let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
    let x : ℝ := 2800 * (deltaG + Real.sqrt epsilon + r)
    ∃ t : PauliSoundnessWitness P R,
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 16 * x ∧
      (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
        472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon) ∧
      ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
        472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon := by
  let r : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
  let x : ℝ := 2800 * (deltaG + Real.sqrt epsilon + r)
  change ∃ t : PauliSoundnessWitness P R,
    ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 16 * x ∧
    (∀ W : PauliKind, rawPauliOperatorDistanceA P R t W ≤
      472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon) ∧
    ∀ W : PauliKind, rawPauliOperatorDistanceB P R t W ≤
      472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon
  let S := pauliNaimarkSetting P epsilon R hwin
  obtain ⟨v, hstate_swap, hpauli_swap⟩ :=
    exists_extraction_witness_with_component_bounds
      P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
  let u := v.toPauliSoundnessWitness
  have hstate_u :
      ‖isometryTensor u.φA u.φB S.toStrategy.ψ -
          idealState P u.aux‖ ^ 2 ≤ 16 * x := by
    dsimp only [u]
    rw [v.state_error_eq]
    exact hstate_swap
  have hcompleted_a (W : PauliKind) :
      pauliOperatorDistanceA P S.toStrategy u W ≤
        36 * x + 4 * r + 32 * Real.sqrt x := by
    calc
      pauliOperatorDistanceA P S.toStrategy u W ≤
          2 * opFamilyDistSq (uniformDistribution Unit)
            (fun (_ : Unit) (h : PauliRegister P) =>
              conjBy (S.placeSide .alice (swapUnitary w .alice))
                (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)))
            (fun (_ : Unit) (h : PauliRegister P) =>
              S.placeExtractedRegister .alice (pauliProj W h))
            (S.idealExpState v.aux) +
          2 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
            S.idealExpState v.aux‖ ^ 2 := by
              simpa only [u] using v.pauli_distance_alice_le_components W
      _ ≤ 36 * x + 4 * r + 32 * Real.sqrt x := by
        nlinarith [hpauli_swap .alice W, hstate_swap]
  have hcompleted_b (W : PauliKind) :
      pauliOperatorDistanceB P S.toStrategy u W ≤
        36 * x + 4 * r + 32 * Real.sqrt x := by
    calc
      pauliOperatorDistanceB P S.toStrategy u W ≤
          2 * opFamilyDistSq (uniformDistribution Unit)
            (fun (_ : Unit) (h : PauliRegister P) =>
              conjBy (S.placeSide .bob (swapUnitary w .bob))
                (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)))
            (fun (_ : Unit) (h : PauliRegister P) =>
              S.placeExtractedRegister .bob (pauliProj W h))
            (S.idealExpState v.aux) +
          2 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
            S.idealExpState v.aux‖ ^ 2 := by
              simpa only [u] using v.pauli_distance_bob_le_components W
      _ ≤ 36 * x + 4 * r + 32 * Real.sqrt x := by
        nlinarith [hpauli_swap .bob W, hstate_swap]
  dsimp only [S, pauliNaimarkSetting] at u hstate_u hcompleted_a hcompleted_b
  let t := pauliNaimarkWitness P R u
  have hstate_t :
      ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 ≤ 16 * x := by
    dsimp only [t]
    rw [pauli_naimark_witness_state_distance_eq]
    exact hstate_u
  have hnaimark_a (W : PauliKind) :
      pauliOperatorDistanceA P R t W ≤
        204 * x + 12 * r + 96 * Real.sqrt x := by
    calc
      pauliOperatorDistanceA P R t W ≤
          3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P R) u W +
            6 * ‖isometryTensor u.φA u.φB (pauliNaimarkStrategy P R).ψ -
              idealState P u.aux‖ ^ 2 := by
                simpa only [t] using pauli_naimark_operator_distanceA_le P R u W
      _ ≤ 3 * (36 * x + 4 * r + 32 * Real.sqrt x) + 6 * (16 * x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hcompleted_a W) (by norm_num))
          (mul_le_mul_of_nonneg_left hstate_u (by norm_num))
      _ = 204 * x + 12 * r + 96 * Real.sqrt x := by ring
  have hnaimark_b (W : PauliKind) :
      pauliOperatorDistanceB P R t W ≤
        204 * x + 12 * r + 96 * Real.sqrt x := by
    calc
      pauliOperatorDistanceB P R t W ≤
          3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P R) u W +
            6 * ‖isometryTensor u.φA u.φB (pauliNaimarkStrategy P R).ψ -
              idealState P u.aux‖ ^ 2 := by
                simpa only [t] using pauli_naimark_operator_distanceB_le P R u W
      _ ≤ 3 * (36 * x + 4 * r + 32 * Real.sqrt x) + 6 * (16 * x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hcompleted_b W) (by norm_num))
          (mul_le_mul_of_nonneg_left hstate_u (by norm_num))
      _ = 204 * x + 12 * r + 96 * Real.sqrt x := by ring
  have hraw_a (W : PauliKind) :
      rawPauliOperatorDistanceA P R t W ≤
        472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon := by
    calc
      rawPauliOperatorDistanceA P R t W ≤
          2 * pauliOperatorDistanceA P R t W +
            4 * ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * epsilon :=
        raw_pauli_operator_distanceA_le_completed R hwin t (le_refl _) W
      _ ≤ 2 * (204 * x + 12 * r + 96 * Real.sqrt x) + 4 * (16 * x) +
          4 * (Fintype.card PauliEdge : ℝ) * epsilon := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (hnaimark_a W) (by norm_num))
            (mul_le_mul_of_nonneg_left hstate_t (by norm_num)))
          le_rfl
      _ = 472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon := by
        rw [pauli_edge_card]
        norm_num only [Nat.cast_ofNat]
        ring
  have hraw_b (W : PauliKind) :
      rawPauliOperatorDistanceB P R t W ≤
        472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon := by
    calc
      rawPauliOperatorDistanceB P R t W ≤
          2 * pauliOperatorDistanceB P R t W +
            4 * ‖isometryTensor t.φA t.φB R.ψ - idealState P t.aux‖ ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * epsilon :=
        raw_pauli_operator_distanceB_le_completed R hwin t (le_refl _) W
      _ ≤ 2 * (204 * x + 12 * r + 96 * Real.sqrt x) + 4 * (16 * x) +
          4 * (Fintype.card PauliEdge : ℝ) * epsilon := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (hnaimark_b W) (by norm_num))
            (mul_le_mul_of_nonneg_left hstate_t (by norm_num)))
          le_rfl
      _ = 472 * x + 24 * r + 192 * Real.sqrt x + 344 * epsilon := by
        rw [pauli_edge_card]
        norm_num only [Nat.cast_ofNat]
        ring
  exact ⟨t, hstate_t, hraw_a, hraw_b⟩

end

end MIPStarRE.QPBT
