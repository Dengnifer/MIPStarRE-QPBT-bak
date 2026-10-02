module

public import MIPStarRE.QPBT.Palomar.LowDegreeConsistency
public import MIPStarRE.QPBT.Palomar.LowDegreeGameStrategyBridge
public import MIPStarRE.QPBT.Test.LowDegreeGameTheorems

/-!
# Exact bridges for compact low-degree consistency

This module identifies the compact effect sums and three low-degree defects
with the corresponding library measurements and consistency defects.  It also
gives the inverse numerical-record conversion needed to apply the registered
soundness theorem to compact parameters.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248` and
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:394-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- A compact parameter record carries the registered admissible-size predicate. -/
theorem LowDegreeParams.is_admissible_size (P : LowDegreeParams) :
    MIPStarRE.QPBT.IsAdmissibleSize P.q :=
  P.hq

/-- Copy compact numerical parameters into the registered low-degree domain. -/
def LowDegreeParams.toLdParams (P : LowDegreeParams) : MIPStarRE.QPBT.LdParams where
  q := P.q
  m := P.m
  d := P.d
  k := P.k
  hm := P.hm
  hd := P.hd
  hk := P.hk
  hq := P.is_admissible_size
  hdvd := P.hdvd

/-- Compact parameters are recovered exactly after conversion to the library record. -/
@[simp] theorem LowDegreeParams.ofLdParams_toLdParams (P : LowDegreeParams) :
    LowDegreeParams.ofLdParams P.toLdParams = P := by
  cases P
  rfl

/-- Library parameters are recovered exactly after conversion to the compact record. -/
@[simp] theorem LowDegreeParams.toLdParams_ofLdParams (P : MIPStarRE.QPBT.LdParams) :
    (LowDegreeParams.ofLdParams P).toLdParams = P := by
  cases P
  rfl

/-- Compact postprocessing of a converted library measurement has the original effect. -/
@[simp] theorem postprocessEffect_ofMeasurement {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (M : MIPStarRE.Quantum.Measurement A I)
    (f : A → B) (b : B) :
    postprocessEffect (POVM.ofMeasurement M) f b = (M.postprocess f).effect b :=
  rfl

/-- Relabeling before effect-level postprocessing only transports the relabeling map. -/
theorem postprocessEffect_relabel {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq C]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : POVM A I)
    (f : B → C) (c : C) :
    postprocessEffect (POVM.relabel e M) f c =
      postprocessEffect M (fun a => f (e a)) c := by
  simp only [postprocessEffect, POVM.relabel_effect, Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm
    (fun a => if f (e a) = c then M.effect a else 0)]
  simp

/-- The library postprocessing of a relabeled compact POVM is the compact effect sum. -/
theorem toMeasurement_relabel_postprocess_effect {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
    (e : A ≃ B) (M : POVM A I) (f : B → C) (c : C) :
    (((POVM.relabel e M).toMeasurement).postprocess f).effect c =
      postprocessEffect M (fun a => f (e a)) c := by
  rw [← postprocessEffect_ofMeasurement]
  exact postprocessEffect_relabel e M f c

/-- Compact and library point questions agree under the question equivalence. -/
@[simp] theorem lowDegreeQuestionEquiv_symm_point (L : MIPStarRE.QPBT.LdParams)
    (u : Fin L.m → MIPStarRE.QPBT.ScalarQ L) :
    (lowDegreeQuestionEquiv L).symm (MIPStarRE.QPBT.ldPointQuestionOf L u) =
      lowDegreePointQuestion (LowDegreeParams.ofLdParams L) u := by
  rfl

/-- The wrong-form-to-zero point map is unchanged by answer relabeling. -/
@[simp] theorem ldPointValuesOrZero_answerEquiv (L : MIPStarRE.QPBT.LdParams)
    (a : LowDegreeAnswer (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L)) :
    MIPStarRE.QPBT.ldPointValuesOrZero L (lowDegreeAnswerEquiv L a) =
      lowDegreePointValuesOrZero a := by
  rcases a with a | (a | a) <;> rfl

/-- Compact and library polynomial-tuple evaluation are definitionally identical. -/
@[simp] theorem evalLowDegreePolynomialTuple_eq (L : MIPStarRE.QPBT.LdParams)
    (u : Fin L.m → MIPStarRE.QPBT.ScalarQ L)
    (g : LowDegreePolynomialTuple (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L)) :
    evalLowDegreePolynomialTuple u g = MIPStarRE.QPBT.evalPolyTupleAt u g :=
  rfl

/-- Alice's point-answer effect is unchanged by strategy and answer transport. -/
theorem lowDegreeStrategyToLibrary_alice_point_effect
    (L : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L))
    (u : Fin L.m → MIPStarRE.QPBT.ScalarQ L) (a : Fin L.k → MIPStarRE.QPBT.ScalarQ L) :
    ((((lowDegreeStrategyToLibrary L S).A (MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
      (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) =
        postprocessEffect (S.alice (lowDegreePointQuestion
          (LowDegreeParams.ofLdParams L) u)) lowDegreePointValuesOrZero a := by
  change ((((POVM.relabel (lowDegreeAnswerEquiv L)
    (S.alice ((lowDegreeQuestionEquiv L).symm
      (MIPStarRE.QPBT.ldPointQuestionOf L u)))).toMeasurement).postprocess
      (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) = _
  rw [toMeasurement_relabel_postprocess_effect]
  simp

/-- Bob's point-answer effect is unchanged by strategy and answer transport. -/
theorem lowDegreeStrategyToLibrary_bob_point_effect
    (L : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L))
    (u : Fin L.m → MIPStarRE.QPBT.ScalarQ L) (a : Fin L.k → MIPStarRE.QPBT.ScalarQ L) :
    ((((lowDegreeStrategyToLibrary L S).B (MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
      (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) =
        postprocessEffect (S.bob (lowDegreePointQuestion
          (LowDegreeParams.ofLdParams L) u)) lowDegreePointValuesOrZero a := by
  change ((((POVM.relabel (lowDegreeAnswerEquiv L)
    (S.bob ((lowDegreeQuestionEquiv L).symm
      (MIPStarRE.QPBT.ldPointQuestionOf L u)))).toMeasurement).postprocess
      (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) = _
  rw [toMeasurement_relabel_postprocess_effect]
  simp

/-- The compact PMF defect is exactly the library defect for the same distribution. -/
theorem consistencyDefect_toPMF {X O I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → O → Matrix I I ℂ) (B : X → O → Matrix J J ℂ)
    (ψ : EuclideanSpace ℂ (I × J)) :
    Palomar.consistencyDefect (μ.toPMF hμ) A B ψ =
      MIPStarRE.QPBT.consistencyDefect μ
        (fun x a => MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => MIPStarRE.QPBT.heteroKron 1 (B x a)) ψ := by
  unfold Palomar.consistencyDefect MIPStarRE.QPBT.consistencyDefect
  rw [MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum μ hμ]
  simp only [PMF.realWeightedSum, smul_eq_mul, MIPStarRE.QPBT.heteroKron]

/-- The compact point--polynomial defect is exactly the registered first defect. -/
theorem ldPointPolynomialDefect_ofMeasurement_eq
    (L : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L))
    (GB : MIPStarRE.QPBT.PolyMeasTuple L S.ιB) :
    ldPointPolynomialDefect (LowDegreeParams.ofLdParams L) S
        (POVM.ofMeasurement GB) =
      MIPStarRE.QPBT.consistencyDefect
        (uniformDistribution (Fin L.m → MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome => MIPStarRE.QPBT.heteroKron
          ((((lowDegreeStrategyToLibrary L S).A
            (MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
              (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => MIPStarRE.QPBT.heteroKron 1
          ((GB.postprocess (MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome))
        (lowDegreeStrategyToLibrary L S).ψ := by
  unfold ldPointPolynomialDefect
  rw [← MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [consistencyDefect_toPMF]
  apply MIPStarRE.QPBT.consistencyDefect_congr
  · intro u outcome
    rw [lowDegreeStrategyToLibrary_alice_point_effect]
    rfl
  · intro u outcome
    simp only [postprocessEffect_ofMeasurement]
    rfl

/-- The compact polynomial--point defect is exactly the registered second defect. -/
theorem ldPolynomialPointDefect_ofMeasurement_eq
    (L : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L))
    (GA : MIPStarRE.QPBT.PolyMeasTuple L S.ιA) :
    ldPolynomialPointDefect (LowDegreeParams.ofLdParams L) S
        (POVM.ofMeasurement GA) =
      MIPStarRE.QPBT.consistencyDefect
        (uniformDistribution (Fin L.m → MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome => MIPStarRE.QPBT.heteroKron
          ((GA.postprocess (MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome) 1)
        (fun u outcome => MIPStarRE.QPBT.heteroKron 1
          ((((lowDegreeStrategyToLibrary L S).B
            (MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
              (MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome))
        (lowDegreeStrategyToLibrary L S).ψ := by
  unfold ldPolynomialPointDefect
  rw [← MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [consistencyDefect_toPMF]
  apply MIPStarRE.QPBT.consistencyDefect_congr
  · intro u outcome
    simp only [postprocessEffect_ofMeasurement]
    rfl
  · intro u outcome
    rw [lowDegreeStrategyToLibrary_bob_point_effect]
    rfl

/-- The compact polynomial--polynomial defect is exactly the registered third defect. -/
theorem ldPolynomialPolynomialDefect_ofMeasurement_eq
    (L : MIPStarRE.QPBT.LdParams)
    (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L))
    (GA : MIPStarRE.QPBT.PolyMeasTuple L S.ιA)
    (GB : MIPStarRE.QPBT.PolyMeasTuple L S.ιB) :
    ldPolynomialPolynomialDefect (LowDegreeParams.ofLdParams L) S
        (POVM.ofMeasurement GA) (POVM.ofMeasurement GB) =
      MIPStarRE.QPBT.consistencyDefect (uniformDistribution Unit)
        (fun _ g => MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
        (fun _ g => MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
        (lowDegreeStrategyToLibrary L S).ψ := by
  unfold ldPolynomialPolynomialDefect
  rw [← MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [consistencyDefect_toPMF]
  rfl

/-- The compact error function is definitionally the registered `deltaLd`. -/
@[simp] theorem deltaLd_eq_library (a b ε : ℝ) (q m d k : ℕ) :
    Palomar.deltaLd a b ε q m d k = MIPStarRE.QPBT.deltaLd a b ε q m d k :=
  rfl

end


end MIPStarRE.QPBT.Palomar
