module

public import MIPStarRE.QPBT.Observables.WinImplications.FactorTransport
public import MIPStarRE.QPBT.Observables.WinImplications.TwistedCommutation

/-!
# The factor-interchanged phase-signed commutation relation

Interchanging the tensor factors places Bob's point observables on the left.
The reversed consistency estimates of `lem:qld-win-implications` and Alice's
Magic Square anticommutation give the bound, which is then transported to the
original state. This proves the factor-interchanged relation in
`lem:qld-win-implications-obs`.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

local instance pauliEdgeNonemptyInterchanged : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## The interchanged consistency inputs on the interchanged state -/

/-- Commuting point/Pair-W consistency with Bob on the left factor. This is the
factor-interchanged form of item 5 of `lem:qld-win-implications`, transported
to the interchanged state; paper
`14_analysis_of_the_pauli_basis_test.tex:227,232-239`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem win_comm_cons_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_comm_cons_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-- The fixed coefficient in `win_comm_cons_swapped_proof`. -/
theorem win_comm_cons_swapped_explicit {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (hε : 0 ≤ ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_)
    (win_comm_cons_interchanged_explicit P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-- Pair-W self-consistency with Bob on the left factor, transported to the
interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pairW_self_consistency_comm_swapped {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (pairW_self_consistency_comm_le S W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ

/-- The commuting Pair check with Bob on the left factor, transported to the
interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem win_comm_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_comm_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairComponentMeas .alice W ω).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ

/-- The fixed coefficient in `win_comm_swapped_proof`. -/
theorem win_comm_swapped_explicit {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (hε : 0 ≤ ε) (W : PauliKind) :
    consistencyDefect (commTupleDist P)
        (fun ω a => heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => heteroKron 1 ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ 2 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (win_comm_interchanged_explicit P ε S hε W)
  exact consistencyDefect_swappedState (commTupleDist P)
    (fun ω a => (S.pairComponentMeas .alice W ω).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ

/-- Magic Square variable consistency with Bob on the left factor, transported
to the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem win_ms_cons_swapped_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect a))
        S.swappedState ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := win_ms_cons_interchanged_proof
  refine ⟨C, hC, ?_⟩
  intro P ε S hε W
  refine le_trans (le_of_eq ?_) (h P ε S hε W)
  exact consistencyDefect_swappedState (anticommTupleDist P)
    (fun ω a => (S.msVarBitMeas .alice (selectedMsVar W) ω).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-- The fixed coefficient in `win_ms_cons_swapped_proof`. -/
theorem win_ms_cons_swapped_explicit {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (hε : 0 ≤ ε) (W : PauliKind) :
    consistencyDefect (anticommTupleDist P)
        (fun ω a => heteroKron
          ((S.pointTraceMeas .bob W (selectedTuplePoint W ω)
            (selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => heteroKron 1
          ((S.msVarBitMeas .alice (selectedMsVar W) ω).effect a))
        S.swappedState ≤ 16 * (Fintype.card PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (win_ms_cons_interchanged_explicit P ε S hε W)
  exact consistencyDefect_swappedState (anticommTupleDist P)
    (fun ω a => (S.msVarBitMeas .alice (selectedMsVar W) ω).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
      (selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-! ## The two halves on Bob's factor -/

/-- The point observables of Bob approximately commute on commuting tuples,
read on the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_commutator_comm_le_bob_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) -
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤
        (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
          1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) *
            (ε + Real.sqrt ε) := by
  classical
  have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
  set K : ℝ := 4 * (Fintype.card PauliEdge : ℝ) with hKdef
  have hK : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  intro P ε S hε
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hmain := point_obs_commutator_comm_le_explicit
    (ιL := S.toStrategy.ιB) (ιR := S.toStrategy.ιA)
    (fun ω => S.pointTraceMeas .bob .X ω.1 ω.2.2.1)
    (fun ω => S.pointTraceMeas .bob .Z ω.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairMeas .alice ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (norm_swappedState S) (by positivity)
    (fun ω => SandwichProduct.postprocess_isProjective _ (S.isProjective.1 _) _)
    (fun ω => pointObs_eq_one_sub_two_smul S .bob .X ω.2.2.1 ω.1)
    (fun ω => pointObs_eq_one_sub_two_smul S .bob .Z ω.2.2.2 ω.2.1)
    (win_comm_cons_swapped_explicit S hε .X)
    (win_comm_cons_swapped_explicit S hε .Z)
    (pairW_self_consistency_comm_swapped S .X)
    (pairW_self_consistency_comm_swapped S .Z)
    (win_comm_swapped_explicit S hε .X) (win_comm_swapped_explicit S hε .Z)
  refine le_trans hmain ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card PauliEdge : ℝ) * ε +
      2 * (Fintype.card PauliEdge : ℝ) * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card PauliEdge : ℝ) * ε +
        2 * (Fintype.card PauliEdge : ℝ) * ε = K * ε by
      rw [hKdef]; ring]
    exact Real.sqrt_mul hK ε
  rw [hKsplit]
  nlinarith [Real.sqrt_nonneg K, hε, hsq]

/-- A universal coefficient bounds Bob's average squared point-observable
commutator norm in the interchanged state by a multiple of `ε + sqrt ε`. -/
theorem exists_pointObs_commutator_comm_le_bob :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (commTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) -
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤ C * (ε + Real.sqrt ε) := by
  let C : ℝ := 1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
    1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    nlinarith [Real.sqrt_nonneg (4 * (Fintype.card PauliEdge : ℝ))]
  · simpa only [C] using point_obs_commutator_comm_le_bob_explicit

/-- Alice's Magic Square variable anticommutator read on the interchanged
state.  Paper `14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObsA_anticommutator_swapped_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
          (obsOf (S.msVarBitMeas .alice 0 ω) *
              obsOf (S.msVarBitMeas .alice 4 ω) +
            obsOf (S.msVarBitMeas .alice 4 ω) *
              obsOf (S.msVarBitMeas .alice 0 ω)))
        S.swappedState‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  have htrans := norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
      (obsOf (S.msVarBitMeas .alice 0 ω) *
          obsOf (S.msVarBitMeas .alice 4 ω) +
        obsOf (S.msVarBitMeas .alice 4 ω) *
          obsOf (S.msVarBitMeas .alice 0 ω)))
    S.toStrategy.ψ
  have hswap : reindexOp (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
      (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
        (obsOf (S.msVarBitMeas .alice 0 ω) * obsOf (S.msVarBitMeas .alice 4 ω) +
          obsOf (S.msVarBitMeas .alice 4 ω) * obsOf (S.msVarBitMeas .alice 0 ω))) =
    heteroKron
      (obsOf (S.msVarBitMeas .alice 0 ω) * obsOf (S.msVarBitMeas .alice 4 ω) +
        obsOf (S.msVarBitMeas .alice 4 ω) * obsOf (S.msVarBitMeas .alice 0 ω))
      (1 : Op S.toStrategy.ιB) := by
    exact reindexOp_prodComm_heteroKron _ _
  rw [hswap] at htrans
  exact le_of_eq_of_le (congrArg (fun t : ℝ => t ^ 2) htrans)
    (msVarBitObsA_anticommutator_le S ω)

/-- The point observables of Bob approximately anticommute on anticommuting
tuples, read on the interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_anticommutator_anticomm_le_bob_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) +
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤
        (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
          3551040 * (16 * (Fintype.card PauliEdge : ℝ))) * ε := by
  classical
  intro P ε S hε
  simp only [pointObs_eq_obsOf]
  have hdist : ∀ W : PauliKind,
      avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA)
            (obsOf (S.pointTraceMeas .bob W (selectedTuplePoint W ω)
              (selectedTupleScalar W ω))) 1 -
          heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
            (obsOf (S.msVarBitMeas .alice (selectedMsVar W) ω)))
        S.swappedState‖ ^ 2) ≤
          4 * ((16 * (Fintype.card PauliEdge : ℝ)) * ε) := by
    intro W
    have h := obsDist_le_of_consistencyDefect
      (ιL := S.toStrategy.ιB) (ιR := S.toStrategy.ιA) (anticommTupleDist P)
      (fun ω => S.pointTraceMeas .bob W (selectedTuplePoint W ω)
        (selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .alice (selectedMsVar W) ω) S.swappedState
      (win_ms_cons_swapped_explicit S hε W)
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdefect : avgOver (anticommTupleDist P)
      (fun ω => 1 - S.msValueAt ω) ≤
        (16 * (Fintype.card PauliEdge : ℝ)) * ε := by
    have hprob := anticommTupleDist_isProbability P
    have hsplit : avgOver (anticommTupleDist P)
        (fun ω => 1 - S.msValueAt ω) =
        1 - avgOver (anticommTupleDist P) S.msValueAt := by
      rw [avgOver_sub, avgOver_const_of_isProbability _ hprob]
    rw [hsplit]
    exact le_of_abs_le (win_magic_square_explicit P ε S hε)
  have hmsavg : avgOver (anticommTupleDist P) (fun ω =>
      ‖applyOperatorToState
        (heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
          (obsOf (S.msVarBitMeas .alice 0 ω) *
              obsOf (S.msVarBitMeas .alice 4 ω) +
            obsOf (S.msVarBitMeas .alice 4 ω) *
              obsOf (S.msVarBitMeas .alice 0 ω)))
        S.swappedState‖ ^ 2) ≤
          1183680 * ((16 * (Fintype.card PauliEdge : ℝ)) * ε) := by
    calc
      _ ≤ avgOver (anticommTupleDist P)
          (fun ω => 1183680 * (1 - S.msValueAt ω)) :=
        avgOver_mono _ _ _
          (fun ω => msVarBitObsA_anticommutator_swapped_le S ω)
      _ = 1183680 * avgOver (anticommTupleDist P)
          (fun ω => 1 - S.msValueAt ω) := avgOver_const_mul _ _ _
      _ ≤ 1183680 * ((16 * (Fintype.card PauliEdge : ℝ)) * ε) :=
        mul_le_mul_of_nonneg_left hdefect (by norm_num)
  have hmain := obs_anticommutator_avg_le (ιL := S.toStrategy.ιB)
    (ιR := S.toStrategy.ιA)
    (fun ω => obsOf (S.pointTraceMeas .bob .X ω.1 ω.2.2.1))
    (fun ω => obsOf (S.pointTraceMeas .bob .Z ω.2.1 ω.2.2.2))
    (fun ω => obsOf (S.msVarBitMeas .alice 0 ω))
    (fun ω => obsOf (S.msVarBitMeas .alice 4 ω)) S.swappedState
    (fun ω => pointTraceObs_conjTranspose_mul_self S .bob .X ω.1 ω.2.2.1)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .bob .Z ω.2.1 ω.2.2.2)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .alice 0 ω)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .alice 4 ω)
    (hdist .X) (hdist .Z) hmsavg
  exact le_trans hmain (le_of_eq (by ring))

/-- A universal coefficient bounds Bob's average squared point-observable
anticommutator norm in the interchanged state by a multiple of `ε`. -/
theorem exists_pointObs_anticommutator_anticomm_le_bob :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιA) +
            heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤ C * ε := by
  let C : ℝ := 96 * (16 * (Fintype.card PauliEdge : ℝ)) +
    3551040 * (16 * (Fintype.card PauliEdge : ℝ))
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    nlinarith
  · simpa only [C] using point_obs_anticommutator_anticomm_le_bob_explicit

/-! ## The interchanged twisted commutation relation -/

/-- The factor-interchanged phase-signed commutation relation on Bob's factor.
This is the trailing clause of `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_twisted_commutation_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  classical
  intro P ε S hε
  have hswapped := twisted_commutation_of_halves
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (norm_swappedState S)
    (fun ω => pointObs_conjTranspose_mul_self S .bob .X ω.2.2.1 ω.1)
    (fun ω => pointObs_conjTranspose_mul_self S .bob .Z ω.2.2.2 ω.2.1)
    hε (by positivity) (by positivity)
    (point_obs_commutator_comm_le_bob_explicit P ε S hε)
    (point_obs_anticommutator_anticomm_le_bob_explicit P ε S hε)
  have htransport := opDistSq_smul_swappedState
    (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB)
    (uniformDistribution (PauliTuple P))
    (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2))
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1 *
      S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
      S.pointObs .bob .X ω.2.2.1 ω.1) S.toStrategy.ψ
  exact le_of_eq_of_le htransport.symm hswapped

/-- A universal coefficient bounds Bob's phase-signed point-observable
commutation distance by a multiple of `sqrt ε`. -/
theorem pointObs_twisted_commutation_interchanged_proof :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤ C * Real.sqrt ε := by
  let C : ℝ := 2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
      1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
    (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
      3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    have hcard : (1 : ℝ) ≤ (Fintype.card PauliEdge : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card PauliEdge)
    nlinarith [Real.sqrt_nonneg (4 * (Fintype.card PauliEdge : ℝ))]
  · simpa only [C] using point_obs_twisted_commutation_interchanged_explicit

end WinImplications

end

end MIPStarRE.QPBT
