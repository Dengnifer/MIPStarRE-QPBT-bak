import MIPStarRE.QPBT.Games.Consistency
import MIPStarRE.QPBT.Games.StrategyClasses

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results are `fact:agreement` through
`lem:close-strategies-have-close-values` in
`blueprint/src/chapter/ch12_qpbt_games.tex:227-438`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-423` and
`:531-540`.
-/

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-- Consistency bounds state-dependent distance, with the explicit factor
hidden in `fact:agreement`; blueprint `ch12_qpbt_games.tex:227-238`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem opFamilyDistSq_le_two_mul_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      2 * consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
  sorry

/-- For projective POVMs, state-dependent distance bounds consistency. This is
the second item of `fact:agreement`, blueprint `ch12_qpbt_games.tex:227-238`,
paper `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_opFamilyDistSq_of_projective {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (hB : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      opFamilyDistSq μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  sorry

/-- Projectivity on one side gives the square-root consistency estimate in the
third item of `fact:agreement`; blueprint `ch12_qpbt_games.tex:227-238`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`. -/
theorem consistencyDefect_le_sqrt_of_projective_left {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x)) :
    consistencyDefect μ (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ ≤
      Real.sqrt (2 * opFamilyDistSq μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ) := by
  sorry

/-- Left multiplication by a square-summable operator family does not increase
state-dependent distance. This is `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:240-252`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:313-344`. -/
theorem opFamilyDistSq_mul_left_le {X Y α β γ ι : Type*}
    [DecidableEq X] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution (X × Y)) (A B : X → (α × β) → Op ι)
    (C : Y → α → γ → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ y a, (1 - ∑ c : γ, (C y a c)ᴴ * C y a c).PosSemidef)
    (h : opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) :
    opFamilyDistSq μ
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ ≤ δ := by
  sorry

/-- Function-indexed left multiplication preserves a state-dependent bound.
This is `fact:add-a-proj2`, blueprint `ch12_qpbt_games.tex:254-268`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:347-361`. -/
theorem opFamilyDistSq_mul_funIndexed_le {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (S : X → (X → α) → Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hS : ∀ x, (1 - ∑ g : X → α, (S x g)ᴴ * S x g).PosSemidef)
    (h : opFamilyDistSq μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ) :
    opFamilyDistSq μ (fun x g => S x g * (A x).effect (g x))
      (fun x g => S x g * (B x).effect (g x)) ψ ≤ δ := by
  sorry

/-- A projective sub-sum absorbs an approximating operator family. This is
`lem:cool-closeness-fact`, blueprint `ch12_qpbt_games.tex:270-288`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:364-380`. -/
theorem opDistSq_sum_sub_mul_le_of_projective {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A : X → Measurement α ι) (B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hA : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (A x))
    (h : opFamilyDistSq μ (fun x a => (A x).effect a) B ψ ≤ δ)
    (s : Finset α) :
    opDistSq μ (fun x => ∑ a ∈ s, (A x).effect a)
      (fun x => ∑ a ∈ s, (A x).effect a * B x a) ψ ≤ δ := by
  sorry

/-- Explicit squared-distance triangle inequality. This is `fact:triangle`,
blueprint `ch12_qpbt_games.tex:290-297`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:383-387`. -/
theorem opFamilyDistSq_le_of_le_of_le {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (δ ε : ℝ)
    (hAB : opFamilyDistSq μ A B ψ ≤ δ)
    (hBC : opFamilyDistSq μ B C ψ ≤ ε) :
    opFamilyDistSq μ A C ψ ≤ 2 * δ + 2 * ε := by
  sorry

/-- Triangle inequality for consistency, with the square-root loss of
`fact:triangle-for-simeq`; blueprint `ch12_qpbt_games.tex:299-309`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-395`. -/
theorem consistencyDefect_trans_le {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B C D : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (ε δ γ : ℝ)
    (hAB : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (B x).effect a) ψ ≤ ε)
    (hCB : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (B x).effect a) ψ ≤ δ)
    (hCD : consistencyDefect μ (fun x a => (C x).effect a)
      (fun x a => (D x).effect a) ψ ≤ γ) :
    consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (D x).effect a) ψ ≤ ε + 2 * Real.sqrt (δ + γ) := by
  sorry

/-- Coarse-graining cannot increase inconsistency. This is
`fact:data-processing`, blueprint `ch12_qpbt_games.tex:311-320`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-401`. -/
theorem consistencyDefect_postprocess_le {X α β ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (f : α → β) :
    consistencyDefect μ (fun x b => ((A x).postprocess f).effect b)
      (fun x b => ((B x).postprocess f).effect b) ψ ≤
      consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ := by
  sorry

/-- Joint closeness to a projective refinement implies approximate
commutation. The universal constant is quantified before the operator data, as
required by `lem:commutation-analysis`; blueprint
`ch12_qpbt_games.tex:324-355`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:410-461`. -/
theorem opDistSq_commutator_le {X α β γ ιA ιB : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (μ : Distribution X)
      (A : X → Measurement (α × β) ιA)
      (B : X → Measurement ((α × β) × γ) ιB)
      (D : X → Measurement (α × γ) ιA)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) (δ : ℝ),
      (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (B x)) →
      opFamilyDistSq μ
        (fun x ab => heteroKron ((A x).effect ab) 1)
        (fun x ab => heteroKron 1 (((B x).postprocess
          (fun abc => abc.1)).effect ab)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x ac => heteroKron ((D x).effect ac) 1)
        (fun x ac => heteroKron 1 (((B x).postprocess
          (fun abc => (abc.1.1, abc.2))).effect ac)) ψ ≤ δ →
      opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => heteroKron
          (((A x).effect (abc.1.1, abc.1.2)) * ((D x).effect (abc.1.1, abc.2)) -
            ((D x).effect (abc.1.1, abc.2)) * ((A x).effect (abc.1.1, abc.1.2))) 1)
        (fun _ _ => 0) ψ ≤ C₀ * δ := by
  sorry

/-- Strategies on identified local spaces and the same transported state have
close values. The asymptotic constant is universal for the game. This is
`lem:close-strategies-have-close-values`, blueprint
`ch12_qpbt_games.tex:430-438`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:531-540`. -/
theorem abs_value_sub_le_of_areClose :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Game) (S S' : Strategy G) (δ : ℝ)
      (_hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1) (hclose : AreCloseStrategies G S S' δ),
      reindexState (Equiv.prodCongr (Equiv.cast hclose.hA).symm
        (Equiv.cast hclose.hB).symm) S'.ψ = S.ψ →
      (S.IsProjective ∨ S'.IsProjective) →
      |S.value - S'.value| ≤ C₀ * Real.rpow δ (1 / 2 : ℝ) := by
  sorry

/-- Averaging contractions preserves state-dependent operator closeness.
This is `lem:avg-closeness`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:299-319`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:100-113`.
The probability hypothesis is explicit because the proof uses Jensen's
inequality for the average. -/
theorem avg_closeness {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability) (A B : X → Op ι)
    (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState
        (averageOperatorOverDistribution μ fun x =>
          α x • (A x - B x)) ψ‖ ^ 2 ≤
      opDistSq μ A B ψ := by
  sorry

/-- Passing from answer-indexed effects to unit-modulus weighted observables
costs at most the answer-alphabet cardinality. This is `lem:povm-to-obs`,
blueprint `blueprint/src/chapter/ch14_qpbt_observables.tex:321-354`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129`. -/
theorem povm_to_obs {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B : X → α → Op ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ (fun x => ∑ a, c a • A x a) (fun x => ∑ a, c a • B x a) ψ ≤
      Fintype.card α * opFamilyDistSq μ A B ψ := by
  sorry

/-- Orthonormalization of a consistent pair of POVMs. The resulting
Alice-side measurement is projective and remains close to the original one on
the bipartite state. This imported result is `lem:ortho`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:356-383`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`;
the source cites KV11 and the self-contained proof [ML20]. -/
theorem exists_projective_close_of_consistent :
    ∃ η : ℝ → ℝ,
      (∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
        η δ ≤ C * Real.rpow δ (1 / 4 : ℝ)) ∧
      ∀ (ιA ιB α : Type) [Fintype ιA] [DecidableEq ιA]
        [Fintype ιB] [DecidableEq ιB] [Fintype α] [DecidableEq α]
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (Q : Measurement α ιA)
        (R : Measurement α ιB) (δ : ℝ),
        0 ≤ δ ∧ δ ≤ 1 →
        consistencyDefect (uniformDistribution Unit)
          (fun _ a => heteroKron (Q.effect a) 1)
          (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ →
        ∃ Pm : Measurement α ιA,
          MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
          opFamilyDistSq (uniformDistribution Unit)
            (fun _ a => heteroKron (Pm.effect a) 1)
            (fun _ a => heteroKron (Q.effect a) 1) ψ ≤ η δ := by
  sorry

end MIPStarRE.QPBT
