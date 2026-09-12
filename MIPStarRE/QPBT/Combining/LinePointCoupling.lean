import MIPStarRE.QPBT.Games.DistanceTheorems.TensorSupport

/-!
# Line-point coupling with an explicit point error

A line outcome and the opposite point outcome have a joint probability law.
Replacing the point outcome by a deterministic reference changes disagreement
by at most the actual point error. The coefficient is one, and no independence
of the two outcomes is assumed. The estimate holds separately on each line and
survives averaging over any finite line-point law.

## References

These are formalization-only auxiliaries for `lem:qld-4-13` and `claim:17-1`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034,1140-1173`.
They retain the point error missing from the universal interface in issue #509;
see `docs/paper-gaps/qpbt_combined-lines-error-term.tex`. They do not assert
existence of extended-line measurements or a polynomial bound for that error.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

/-- For a nonnegative joint law, replacing the point answer by `c` changes
disagreement by at most its own disagreement with `c`. The law need not be
normalized. Here `e` evaluates the line outcome at the sampled point. -/
theorem line_point_coupling_disagreement_le {F A : Type*}
    [Fintype F] [Fintype A] [DecidableEq A]
    (w : F → A → ℝ) (hw : ∀ f a, 0 ≤ w f a) (e : F → A) (c : A) :
    |(∑ f, ∑ a, if e f = a then 0 else w f a) -
        (∑ f, ∑ a, if e f = c then 0 else w f a)| ≤
      ∑ f, ∑ a, if a = c then 0 else w f a := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  by_cases hac : a = c
  · subst a
    simp
  · by_cases hea : e f = a <;> by_cases hec : e f = c <;>
      simp [hac, Ne.symm hac, hea, hec, abs_of_nonneg (hw f a), hw f a]

/-- The explicit quantum coupling on one line, at one sampled point. The
POVMs act on separate local spaces. The right side is the actual error of the
point measurement relative to `c`, without any strategy-error substitution. -/
theorem line_point_povm_coupling_le {F A ιA ιB : Type*}
    [Fintype F] [Fintype A] [DecidableEq A]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (T : Measurement F ιA) (Q : Measurement A ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (e : F → A) (c : A) :
    |(∑ f, ∑ a, if e f = a then 0 else
          stateQForm ψ (heteroKron (T.effect f) (Q.effect a))) -
        (∑ f, if e f = c then 0 else
          stateQForm ψ (heteroKron (T.effect f) 1))| ≤
      ∑ a, if a = c then 0 else stateQForm ψ (heteroKron 1 (Q.effect a)) := by
  have hrow (f : F) :
      (∑ a, stateQForm ψ (heteroKron (T.effect f) (Q.effect a))) =
        stateQForm ψ (heteroKron (T.effect f) 1) := by
    rw [← stateQForm_finset_sum]
    congr 1
    ext i j
    have hQ := congrFun (congrFun Q.sum_eq_one i.2) j.2
    simpa [heteroKron, Matrix.kronecker_apply, Matrix.sum_apply, ← Finset.mul_sum]
      using congrArg (fun z => (T.effect f) i.1 j.1 * z) hQ
  have hcol (a : A) :
      (∑ f, stateQForm ψ (heteroKron (T.effect f) (Q.effect a))) =
        stateQForm ψ (heteroKron 1 (Q.effect a)) := by
    rw [← stateQForm_finset_sum]
    congr 1
    ext i j
    have hT := congrFun (congrFun T.sum_eq_one i.1) j.1
    simpa [heteroKron, Matrix.kronecker_apply, Matrix.sum_apply, ← Finset.sum_mul]
      using congrArg (fun z => z * (Q.effect a) i.2 j.2) hT
  have h := line_point_coupling_disagreement_le
    (fun f a => stateQForm ψ (heteroKron (T.effect f) (Q.effect a)))
    (fun f a => stateQForm_nonneg ψ (kronecker_nonneg (T.pos f) (Q.pos a))) e c
  have hr : (∑ f, ∑ a, if e f = c then 0 else
        stateQForm ψ (heteroKron (T.effect f) (Q.effect a))) =
      ∑ f, if e f = c then 0 else stateQForm ψ (heteroKron (T.effect f) 1) := by
    apply Finset.sum_congr rfl
    intro f _
    by_cases hfc : e f = c <;> simp [hfc, hrow]
  have hc : (∑ f, ∑ a, if a = c then 0 else
        stateQForm ψ (heteroKron (T.effect f) (Q.effect a))) =
      ∑ a, if a = c then 0 else stateQForm ψ (heteroKron 1 (Q.effect a)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hac : a = c <;> simp [hac, hcol]
  rwa [hr, hc] at h

/-- Averaging the per-line coupling retains the actual point error with
coefficient one. `T x` is the evaluated line POVM at sample `x`; it may depend
on the line and point arbitrarily. The middle term is disagreement with a
deterministic reference, so both upper and lower bounds follow from this
absolute-value estimate. No normalization assumptions are required. -/
theorem consistencyDefect_line_point_coupling_le {X A ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (T : X → Measurement A ιA) (Q : X → Measurement A ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (c : X → A) :
    |consistencyDefect μ (fun x a => heteroKron ((T x).effect a) 1)
          (fun x a => heteroKron 1 ((Q x).effect a)) ψ -
        avgOver μ (fun x => ∑ a, if a = c x then 0 else
          stateQForm ψ (heteroKron ((T x).effect a) 1))| ≤
      avgOver μ (fun x => ∑ a, if a = c x then 0 else
        stateQForm ψ (heteroKron 1 ((Q x).effect a))) := by
  have h x := abs_le.mp (line_point_povm_coupling_le (T x) (Q x) ψ id (c x))
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
  rw [← avgOver_sub]
  apply abs_le.mpr
  constructor
  · calc
      -avgOver μ _ = avgOver μ (fun x =>
          -(∑ a, if a = c x then 0 else
            stateQForm ψ (heteroKron 1 ((Q x).effect a)))) := by
        simp only [avgOver, mul_neg, Finset.sum_neg_distrib]
      _ ≤ _ := avgOver_mono μ _ _ (fun x => (h x).1)
  · exact avgOver_mono μ _ _ (fun x => (h x).2)

end MIPStarRE.QPBT
