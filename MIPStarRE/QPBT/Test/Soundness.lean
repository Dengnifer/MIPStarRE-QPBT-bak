import MIPStarRE.QPBT.Test.SoundnessDefs
import MIPStarRE.QPBT.Test.Soundness.RangeProjection
import MIPStarRE.QPBT.Test.Soundness.Ancilla
import MIPStarRE.QPBT.Test.Soundness.OperatorTransfer
import MIPStarRE.QPBT.Test.Soundness.ProjectiveSetting
import MIPStarRE.QPBT.Test.Soundness.NaimarkReduction
import MIPStarRE.QPBT.Test.Soundness.NaimarkOperatorTransfer

/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem and provides auxiliary
range-projection estimates, ancilla isometries, and the transfer of supplied
extraction data to the three soundness estimates.
The final composition uses the projective-setting producer and the Naimark
reduction/transfer lemmas in the imported support modules.  The scalar
square-root error bound remains in `MIPStarRE.QPBT.Combining.RootErrorBounds`.

## References

The main declaration is blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum

noncomputable section

/-- **Local proof obligation:** on the unit error interval, squaring a
`deltaQld` term is absorbed by increasing the prefactor and replacing `b` by
`b / 4`.  This scalar estimate is used only to compose the projective
support theorem with the Naimark operator-transfer bounds; it is not an
additional hypothesis of `thm:pauli`. -/
private theorem deltaQld_sq_le {P : AdmissibleParams} {a b ε : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (deltaQld a b ε P.m P.d P.q) ^ 2 ≤
      deltaQld (3 * a ^ 2 + 2 * a) (b / 4) ε P.m P.d P.q := by
  let degree : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let rate : ℝ := ε ^ b + (P.q : ℝ) ^ (-b) + 2 ^ (-(b * degree))
  let rate' : ℝ := ε ^ (b / 4) + (P.q : ℝ) ^ (-(b / 4)) +
    2 ^ (-((b / 4) * degree))
  let a' : ℝ := 3 * a ^ 2 + 2 * a
  have hdegree1 : 1 ≤ degree := by
    dsimp [degree]
    exact Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hdegree0 : 0 ≤ degree := by linarith
  have hq1 : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq
    rw [hk]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hrate'0 : 0 ≤ rate' := by
    dsimp [rate']
    positivity
  have hrate_sq : rate ^ 2 ≤ 3 * rate' := by
    have hsum :
        (ε ^ b + (P.q : ℝ) ^ (-b) + 2 ^ (-(b * degree))) ^ 2 ≤
          3 * ((ε ^ b) ^ 2 + ((P.q : ℝ) ^ (-b)) ^ 2 +
            (2 ^ (-(b * degree))) ^ 2) := by
      nlinarith [sq_nonneg (ε ^ b - (P.q : ℝ) ^ (-b)),
        sq_nonneg (ε ^ b - 2 ^ (-(b * degree))),
        sq_nonneg ((P.q : ℝ) ^ (-b) - 2 ^ (-(b * degree)))]
    have hεb_sq : (ε ^ b) ^ 2 ≤ ε ^ (b / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε0]
      exact Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 (by positivity) (by linarith)
    have hqb_sq : ((P.q : ℝ) ^ (-b)) ^ 2 ≤ (P.q : ℝ) ^ (-(b / 4)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P.q)]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have h2b_sq : ((2 : ℝ) ^ (-(b * degree))) ^ 2 ≤
        (2 : ℝ) ^ (-((b / 4) * degree)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg hb.le hdegree0]
    dsimp [rate, rate'] at hsum ⊢
    exact hsum.trans <| mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hεb_sq hqb_sq) h2b_sq) (by norm_num)
  have h2a : 2 * a ≤ a' := by
    dsimp [a']
    nlinarith [sq_nonneg a]
  have h3a2 : 3 * a ^ 2 ≤ a' := by
    dsimp [a']
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg a)]
  have hdegree_pow : degree ^ (2 * a) ≤ degree ^ a' := by
    exact Real.rpow_le_rpow_of_exponent_le hdegree1 h2a
  have hdelta_eq : deltaQld a b ε P.m P.d P.q = a * degree ^ a * rate := by
    simp [deltaQld, degree, rate]
  have hdelta'_eq :
      deltaQld a' (b / 4) ε P.m P.d P.q = a' * degree ^ a' * rate' := by
    simp [deltaQld, a', degree, rate']
  rw [hdelta_eq, hdelta'_eq]
  have hdegree_pow_sq : (degree ^ a) ^ 2 = degree ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdegree0]
    ring_nf
  calc
    (a * degree ^ a * rate) ^ 2 =
        (a ^ 2 * degree ^ (2 * a)) * rate ^ 2 := by
          calc
            (a * degree ^ a * rate) ^ 2 =
                (a ^ 2 * (degree ^ a) ^ 2) * rate ^ 2 := by ring
            _ = (a ^ 2 * degree ^ (2 * a)) * rate ^ 2 := by
              rw [hdegree_pow_sq]
    _ ≤ (a ^ 2 * degree ^ a') * (3 * rate') := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hdegree_pow (sq_nonneg a)) hrate_sq
      · positivity
      · positivity
    _ = (3 * a ^ 2) * degree ^ a' * rate' := by ring
    _ ≤ a' * degree ^ a' * rate' := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right h3a2 (by positivity)
      · exact hrate'0

/-- **Local proof obligation:** after reducing a large error to the endpoint
`ε = 1`, the endpoint `deltaQld` bound is monotone in `ε`.  This discharges
the large-error branch of the source-shaped theorem without adding an error
cap to its statement. -/
private theorem deltaQld_mono_epsilon_ge_one {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hε : 1 ≤ ε) :
    deltaQld a b 1 P.m P.d P.q ≤ deltaQld a b ε P.m P.d P.q := by
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by positivity
  have hεb : (1 : ℝ) ^ b ≤ ε ^ b := by
    exact Real.rpow_le_rpow (by norm_num) hε hb
  have hsum : (1 : ℝ) ^ b + (P.q : ℝ) ^ (-b) +
      2 ^ (-b * ((P.m * P.d : ℕ) : ℝ)) ≤
      ε ^ b + (P.q : ℝ) ^ (-b) +
        2 ^ (-b * ((P.m * P.d : ℕ) : ℝ)) := by
    linarith
  have hsum' : Real.rpow (1 : ℝ) b + (P.q : ℝ) ^ (-b) +
      2 ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤
      ε ^ b + (P.q : ℝ) ^ (-b) +
        2 ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) := by
    simpa [Real.one_rpow, neg_mul] using hsum
  unfold deltaQld
  exact mul_le_mul_of_nonneg_left hsum'
    (mul_nonneg (by linarith) (Real.rpow_nonneg hdegree0 a))

/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`thm:pauli`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
blueprint `def:povm-distance`.
-/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hb₀1, hprojective⟩ :=
    exists_projective_setting_isometry_bounds
  let a₁ : ℝ := 3 * a₀ ^ 2 + 2 * a₀
  let b₁ : ℝ := b₀ / 4
  let aFinal : ℝ := 9 * a₁
  have ha₁ : 1 ≤ a₁ := by
    dsimp [a₁]
    nlinarith [sq_nonneg a₀]
  have ha₀₁ : a₀ ≤ a₁ := by
    dsimp [a₁]
    nlinarith [sq_nonneg a₀]
  have hb₁ : 0 < b₁ := by
    dsimp [b₁]
    linarith
  have hb₁₀ : b₁ < 1 := by
    dsimp [b₁]
    nlinarith
  have haFinal : 1 ≤ aFinal := by
    dsimp [aFinal]
    nlinarith [ha₁]
  have hscale_at {P : AdmissibleParams} {e : ℝ}
      (he : 0 ≤ e) :
      9 * deltaQld a₁ b₁ e P.m P.d P.q ≤
        deltaQld aFinal b₁ e P.m P.d P.q := by
    simpa [aFinal] using
      (scale_deltaQld_le (P := P) (a := a₁) (b := b₁) (epsilon := e)
        ha₁ he (by norm_num : (1 : ℝ) ≤ 9))
  have hcompose :
      ∀ (P : AdmissibleParams) (e : ℝ) (T : Strategy (pauliBasisTest P)),
        0 ≤ e → e ≤ 1 → 1 - e ≤ T.value →
          ∃ w : PauliSoundnessWitness P T,
            ‖isometryTensor w.φA w.φB T.ψ - idealState P w.aux‖ ≤
                deltaQld aFinal b₁ e P.m P.d P.q ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceA P T w W ≤ deltaQld aFinal b₁ e P.m P.d P.q) ∧
            (∀ W : PauliKind,
              pauliOperatorDistanceB P T w W ≤ deltaQld aFinal b₁ e P.m P.d P.q) := by
    intro P e T he0 he1 hT
    let setting : ProjectiveSetting P e := pauliNaimarkSetting P e T hT
    obtain ⟨t, htState, htA, htB⟩ := hprojective P e he0 he1 setting
    dsimp only [setting, pauliNaimarkSetting] at htState htA htB
    let d₀ : ℝ := deltaQld a₀ b₀ e P.m P.d P.q
    let d₁ : ℝ := deltaQld a₁ b₁ e P.m P.d P.q
    let dFinal : ℝ := deltaQld aFinal b₁ e P.m P.d P.q
    have delta_nonneg (c r : ℝ) (hc : 0 ≤ c) :
        0 ≤ deltaQld c r e P.m P.d P.q := by
      have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.zero_le (P.m * P.d))
      have hq0 : (0 : ℝ) ≤ (P.q : ℝ) := Nat.cast_nonneg _
      have hsum : 0 ≤ Real.rpow e r + Real.rpow (P.q : ℝ) (-r) +
          Real.rpow 2 (-((r : ℝ) * ((P.m * P.d : ℕ) : ℝ))) := by
        exact add_nonneg
          (add_nonneg (Real.rpow_nonneg he0 r) (Real.rpow_nonneg hq0 (-r)))
          (Real.rpow_nonneg (by norm_num) _)
      unfold deltaQld
      exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hdegree0 c)) hsum
    have hd₀ : 0 ≤ d₀ := by
      exact delta_nonneg a₀ b₀ (by linarith)
    have hd₁ : 0 ≤ d₁ := by
      exact delta_nonneg a₁ b₁ (by linarith)
    have hd₀₁ : d₀ ≤ d₁ := by
      dsimp [d₀, d₁]
      exact deltaQld_mono ha₀ ha₀₁ (by dsimp [b₁]; linarith) hb₁ he0 he1
    have hd₀_sq : d₀ ^ 2 ≤ d₁ := by
      simpa [d₀, d₁, a₁, b₁] using deltaQld_sq_le ha₀ hb₀ he0 he1
    have hscale : 9 * d₁ ≤ dFinal := by
      simpa [d₁, dFinal] using hscale_at he0
    have htransfer : 3 * d₀ + 6 * d₀ ^ 2 ≤ dFinal := by
      have hquad : 3 * d₀ + 6 * d₀ ^ 2 ≤ 9 * d₁ := by
        nlinarith [hd₀₁, hd₀_sq]
      exact hquad.trans hscale
    have hstate₀ :
        ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
          idealState P t.aux‖ ≤ d₀ := by
      change ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
          idealState P t.aux‖ ≤ d₀ at htState
      exact htState
    have hstate_final :
        ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
          idealState P t.aux‖ ≤ dFinal := by
      have h₀₁ : d₀ ≤ dFinal := by
        calc
          d₀ ≤ d₁ := hd₀₁
          _ ≤ 9 * d₁ := by nlinarith
          _ ≤ dFinal := hscale
      exact hstate₀.trans h₀₁
    refine ⟨pauliNaimarkWitness P T t, ?_, ?_, ?_⟩
    · rw [pauli_naimark_witness_state_distance_eq]
      exact hstate_final
    · intro W
      have hstate_sq :
          ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
            idealState P t.aux‖ ^ 2 ≤ d₀ ^ 2 := by
        have hnorm : 0 ≤
            ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
              idealState P t.aux‖ := norm_nonneg _
        have hprod := mul_nonneg
          (sub_nonneg.mpr hstate₀)
          (add_nonneg hd₀ hnorm)
        nlinarith [hprod]
      calc
        pauliOperatorDistanceA P T (pauliNaimarkWitness P T t) W ≤
            3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P T) t W +
              6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
                idealState P t.aux‖ ^ 2 :=
          pauli_naimark_operator_distanceA_le P T t W
        _ ≤ 3 * d₀ + 6 * d₀ ^ 2 := by
          nlinarith [htA W, hstate_sq]
        _ ≤ dFinal := htransfer
    · intro W
      have hstate_sq :
          ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
            idealState P t.aux‖ ^ 2 ≤ d₀ ^ 2 := by
        have hnorm : 0 ≤
            ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
              idealState P t.aux‖ := norm_nonneg _
        have hprod := mul_nonneg
          (sub_nonneg.mpr hstate₀)
          (add_nonneg hd₀ hnorm)
        nlinarith [hprod]
      calc
        pauliOperatorDistanceB P T (pauliNaimarkWitness P T t) W ≤
            3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P T) t W +
              6 * ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P T).ψ -
                idealState P t.aux‖ ^ 2 :=
          pauli_naimark_operator_distanceB_le P T t W
        _ ≤ 3 * d₀ + 6 * d₀ ^ 2 := by
          nlinarith [htB W, hstate_sq]
        _ ≤ dFinal := htransfer
  refine ⟨aFinal, b₁, haFinal, hb₁, hb₁₀, ?_⟩
  intro P ε he0 S hS
  by_cases he1 : ε ≤ 1
  · exact hcompose P ε S he0 he1 hS
  · have hege : 1 ≤ ε := le_of_not_ge he1
    have hS1 : 1 - (1 : ℝ) ≤ S.value := by
      linarith [Strategy.value_nonneg S]
    obtain ⟨w, hwState, hwA, hwB⟩ :=
      hcompose P 1 S (by norm_num) (by norm_num) hS1
    let dFinal : ℝ := deltaQld aFinal b₁ 1 P.m P.d P.q
    have hmon : dFinal ≤ deltaQld aFinal b₁ ε P.m P.d P.q := by
      dsimp [dFinal]
      exact deltaQld_mono_epsilon_ge_one haFinal (by linarith) hege
    refine ⟨w, ?_, ?_, ?_⟩
    · have hwState' :
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ dFinal := by
        change ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
          deltaQld aFinal b₁ 1 P.m P.d P.q
        exact hwState
      exact hwState'.trans hmon
    · intro W
      have hwA' : pauliOperatorDistanceA P S w W ≤ dFinal := by
        change pauliOperatorDistanceA P S w W ≤ deltaQld aFinal b₁ 1 P.m P.d P.q
        exact hwA W
      exact hwA'.trans hmon
    · intro W
      have hwB' : pauliOperatorDistanceB P S w W ≤ dFinal := by
        change pauliOperatorDistanceB P S w W ≤ deltaQld aFinal b₁ 1 P.m P.d P.q
        exact hwB W
      exact hwB'.trans hmon

end

end MIPStarRE.QPBT
