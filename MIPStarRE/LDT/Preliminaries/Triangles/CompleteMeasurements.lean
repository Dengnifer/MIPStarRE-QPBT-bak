module

public import MIPStarRE.LDT.Preliminaries.DistanceBounds
public import MIPStarRE.LDT.Preliminaries.Triangles.Core

/-!
# Linear consistency triangles for complete measurements

This module proves a linear-error three-link triangle inequality for complete
measurements.  The proof combines the exact decomposition of consistency into
squared distance and projectivity defects with the existing three-step
state-dependent-distance triangle.

The completeness hypotheses are essential: the corresponding statement is
false for arbitrary submeasurements.

## References

* `references/ldt-paper/preliminaries.tex`,
  `prop:simeq-triangle-inequality` at lines 649-684.
* `references/ldt-paper/inductive_step.tex`, lines 111-185.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- The failure of a complete measurement to be projective, evaluated on a
state.  Every summand is nonnegative because each measurement effect lies in
the operator interval `[0, 1]`. -/
noncomputable def measurementProjectivityDefect
    {Outcome ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) : Error :=
  ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)

/-- The projectivity defect of a complete measurement is nonnegative. -/
theorem measurementProjectivityDefect_nonneg
    {Outcome ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) :
    0 ≤ measurementProjectivityDefect ψ A := by
  unfold measurementProjectivityDefect
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ <| sub_nonneg.mpr <|
      MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (Measurement.outcome_le_one A a)

/-- For complete measurements, twice the consistency defect is the squared
distance plus the two nonnegative projectivity defects. -/
theorem two_mul_qConsDefect_eq_qSDD_add_projectivity_defects
    {Outcome ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) :
    2 * qConsDefect ψ A.toSubMeas B.toSubMeas =
      qSDD ψ A.toSubMeas B.toSubMeas +
        measurementProjectivityDefect ψ A + measurementProjectivityDefect ψ B := by
  let diagA : Error := ∑ a, ev ψ (A.outcome a * A.outcome a)
  let diagB : Error := ∑ a, ev ψ (B.outcome a * B.outcome a)
  have hsumA : ∑ a, ev ψ (A.outcome a) = ev ψ 1 := by
    rw [← ev_sum ψ A.outcome, A.sum_eq]
  have hsumB : ∑ a, ev ψ (B.outcome a) = ev ψ 1 := by
    rw [← ev_sum ψ B.outcome, B.sum_eq]
  have hdiagA_le : diagA ≤ ev ψ 1 := by
    calc
      diagA ≤ ∑ a, ev ψ (A.outcome a) := by
        exact Finset.sum_le_sum fun a _ =>
          ev_mono ψ _ _ <|
            MIPStarRE.Quantum.sq_le_self
              (A.outcome_pos a) (Measurement.outcome_le_one A a)
      _ = ev ψ 1 := hsumA
  have hdiagB_le : diagB ≤ ev ψ 1 := by
    calc
      diagB ≤ ∑ a, ev ψ (B.outcome a) := by
        exact Finset.sum_le_sum fun a _ =>
          ev_mono ψ _ _ <|
            MIPStarRE.Quantum.sq_le_self
              (B.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ 1 := hsumB
  have hqSDD :
      qSDD ψ A.toSubMeas B.toSubMeas =
        diagA + diagB - 2 * qMatchMass ψ A.toSubMeas B.toSubMeas := by
    have hexpand (a : Outcome) :
        ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
          ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a) := by
      have hcomm :
          ev ψ (B.outcome a * A.outcome a) =
            ev ψ (A.outcome a * B.outcome a) :=
        ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
      calc
        ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
            ev ψ ((A.outcome a * A.outcome a - A.outcome a * B.outcome a) -
              (B.outcome a * A.outcome a - B.outcome a * B.outcome a)) := by
                congr 1
                simp [sub_mul, mul_sub, Measurement.outcome_hermitian]
                abel
        _ = ev ψ (A.outcome a * A.outcome a) -
              ev ψ (A.outcome a * B.outcome a) -
              (ev ψ (B.outcome a * A.outcome a) -
                ev ψ (B.outcome a * B.outcome a)) := by
                  rw [ev_sub, ev_sub, ev_sub]
        _ = ev ψ (A.outcome a * A.outcome a) +
              ev ψ (B.outcome a * B.outcome a) -
              2 * ev ψ (A.outcome a * B.outcome a) := by
                rw [hcomm]
                ring
    unfold qSDD qSDDCore qMatchMass
    calc
      ∑ a, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
          ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a)) := by
              exact Finset.sum_congr rfl fun a _ => hexpand a
      _ = diagA + diagB - 2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
            simp only [diagA, diagB, Finset.sum_sub_distrib,
              Finset.sum_add_distrib, Finset.mul_sum]
  have hinner_nonneg :
      0 ≤ ev ψ 1 - qMatchMass ψ A.toSubMeas B.toSubMeas := by
    have hqSDD_nonneg := qSDD_nonneg ψ A.toSubMeas B.toSubMeas
    rw [hqSDD] at hqSDD_nonneg
    linarith
  have hdefectA :
      measurementProjectivityDefect ψ A = ev ψ 1 - diagA := by
    unfold measurementProjectivityDefect
    calc
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) =
          ∑ a, (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
            exact Finset.sum_congr rfl fun a _ => ev_sub ψ _ _
      _ = (∑ a, ev ψ (A.outcome a)) - diagA := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ 1 - diagA := by rw [hsumA]
  have hdefectB :
      measurementProjectivityDefect ψ B = ev ψ 1 - diagB := by
    unfold measurementProjectivityDefect
    calc
      ∑ a, ev ψ (B.outcome a - B.outcome a * B.outcome a) =
          ∑ a, (ev ψ (B.outcome a) - ev ψ (B.outcome a * B.outcome a)) := by
            exact Finset.sum_congr rfl fun a _ => ev_sub ψ _ _
      _ = (∑ a, ev ψ (B.outcome a)) - diagB := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ 1 - diagB := by rw [hsumB]
  unfold qConsDefect
  rw [A.total_eq_one, B.total_eq_one, one_mul, max_eq_right hinner_nonneg]
  rw [hqSDD, hdefectA, hdefectB]
  ring

/-- A pointwise three-link consistency triangle for complete measurements on a
common Hilbert space. -/
theorem qConsDefect_triangle_three_of_measurements
    {Outcome ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B C D : Measurement Outcome ι) :
    qConsDefect ψ A.toSubMeas D.toSubMeas ≤
      3 * (qConsDefect ψ A.toSubMeas B.toSubMeas +
        qConsDefect ψ C.toSubMeas B.toSubMeas +
        qConsDefect ψ C.toSubMeas D.toSubMeas) := by
  have htri := questionSDD_triangle_three ψ A.toSubMeas B.toSubMeas
    C.toSubMeas D.toSubMeas
  have hBCsym := qSDD_symm ψ B.toSubMeas C.toSubMeas
  rw [hBCsym] at htri
  have hAB := two_mul_qConsDefect_eq_qSDD_add_projectivity_defects ψ A B
  have hCB := two_mul_qConsDefect_eq_qSDD_add_projectivity_defects ψ C B
  have hCD := two_mul_qConsDefect_eq_qSDD_add_projectivity_defects ψ C D
  have hAD := two_mul_qConsDefect_eq_qSDD_add_projectivity_defects ψ A D
  have hA0 := measurementProjectivityDefect_nonneg ψ A
  have hB0 := measurementProjectivityDefect_nonneg ψ B
  have hC0 := measurementProjectivityDefect_nonneg ψ C
  have hD0 := measurementProjectivityDefect_nonneg ψ D
  linarith

/-- A pointwise three-link consistency triangle for complete measurements on
the two tensor factors of a heterogeneous bipartite state. -/
theorem qBipartiteConsDefect_triangle_three_of_measurements
    {Outcome ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A C : Measurement Outcome ιA) (B D : Measurement Outcome ιB) :
    qBipartiteConsDefect ψ A.toSubMeas D.toSubMeas ≤
      3 * (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas +
        qBipartiteConsDefect ψ C.toSubMeas B.toSubMeas +
        qBipartiteConsDefect ψ C.toSubMeas D.toSubMeas) := by
  let AL := leftLiftedMeasurement (ιB := ιB) A
  let BL := rightLiftedMeasurement (ιA := ιA) B
  let CL := leftLiftedMeasurement (ιB := ιB) C
  let DL := rightLiftedMeasurement (ιA := ιA) D
  simpa [AL, BL, CL, DL, qBipartiteConsDefect_eq_qConsDefect_placed,
    leftLiftedMeasurement, rightLiftedMeasurement] using
      qConsDefect_triangle_three_of_measurements ψ AL BL CL DL

/-- Linear-error heterogeneous triangle for complete measurements.

If `A` is consistent with `B`, `C` is consistent with `B`, and `C` is
consistent with `D`, then `A` is consistent with `D` at three times the sum of
the input errors.  This alternative linear bound also requires completeness of
all four families. -/
theorem consistency_triangle_three_heterogeneous
    {Question Outcome ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A C : IdxMeas Question Outcome ιA) (B D : IdxMeas Question Outcome ιB)
    (ε δ γ : Error)
    (hAB : ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) ε)
    (hCB : ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas C) (IdxMeas.toIdxSubMeas B) δ)
    (hCD : ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas C) (IdxMeas.toIdxSubMeas D) γ) :
    ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas D)
      (3 * (ε + δ + γ)) := by
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q).toSubMeas (D q).toSubMeas) ≤
        avgOver 𝒟 (fun q => 3 *
          (qBipartiteConsDefect ψ (A q).toSubMeas (B q).toSubMeas +
            qBipartiteConsDefect ψ (C q).toSubMeas (B q).toSubMeas +
            qBipartiteConsDefect ψ (C q).toSubMeas (D q).toSubMeas)) := by
              apply avgOver_mono
              intro q
              exact qBipartiteConsDefect_triangle_three_of_measurements
                ψ (A q) (C q) (B q) (D q)
    _ = 3 *
        (avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q).toSubMeas (B q).toSubMeas) +
          avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (C q).toSubMeas (B q).toSubMeas) +
          avgOver 𝒟 (fun q =>
            qBipartiteConsDefect ψ (C q).toSubMeas (D q).toSubMeas)) := by
              simp [avgOver_const_mul, avgOver_add, add_assoc]
    _ ≤ 3 * (ε + δ + γ) := by
          have hAB' := hAB.offDiagonalBound
          have hCB' := hCB.offDiagonalBound
          have hCD' := hCD.offDiagonalBound
          unfold bipartiteConsError at hAB' hCB' hCD'
          change avgOver 𝒟 (fun q =>
            qBipartiteConsDefect ψ (A q).toSubMeas (B q).toSubMeas) ≤ ε at hAB'
          change avgOver 𝒟 (fun q =>
            qBipartiteConsDefect ψ (C q).toSubMeas (B q).toSubMeas) ≤ δ at hCB'
          change avgOver 𝒟 (fun q =>
            qBipartiteConsDefect ψ (C q).toSubMeas (D q).toSubMeas) ≤ γ at hCD'
          linarith

end MIPStarRE.LDT.Preliminaries
