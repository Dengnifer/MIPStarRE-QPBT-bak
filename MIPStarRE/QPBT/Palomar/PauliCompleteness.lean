module

public import MIPStarRE.QPBT.Palomar.PauliExtractionBridge

/-!
# Compact Pauli basis test completeness

This module transports the registered value-one SPCC strategy to the compact
Palomar game.  Its public statement uses the concrete Pauli SPCC predicate and
the once-and-for-all field model, while symmetric-game and relabeling objects
occur only in the proof.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`,
paper `lem:pauli-completeness`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- `lem:pauli-completeness`: every compact Pauli basis game has a symmetric
projective, consistent, support-wise commuting strategy of value exactly one. -/
theorem exists_spcc_value_one (P : PauliParams) :
    ∃ S : SymmetricPauliStrategy P
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
      S.IsPauliSPCC P
          (MIPStarRE.QPBT.binaryRepresentation
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) ∧
      S.toStrategy.value
          (pauliGame P
            (MIPStarRE.QPBT.binaryRepresentation
              (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
            (MIPStarRE.QPBT.fixedBinTrace
              (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) = 1 := by
  classical
  let Q := P.toAdmissibleParams
  obtain ⟨T, hspcc, hvalue⟩ := MIPStarRE.QPBT.exists_spcc_value_one Q
  let T' := SymmetricStrategy.ofSymmetricStrategy T
  let S := SymmetricStrategy.relabel T'
    (pauliQuestionEquiv Q).symm (pauliAnswerEquivCompact Q).symm
  have hspcc' : T'.IsSPCC
      (SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm Q)) :=
    (SymmetricStrategy.isSPCC_ofSymmetricStrategy_iff T).2 hspcc
  have hspccS : S.IsSPCC (pauliSymmetricGame Q) := by
    apply (SymmetricStrategy.relabel_isSPCC_iff
      (SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm Q))
      (pauliSymmetricGame Q) T'
      (pauliQuestionEquiv Q).symm (pauliAnswerEquivCompact Q).symm rfl).2
    exact hspcc'
  have hvalueS : S.toStrategy.value (pauliSymmetricGame Q).toGame = 1 := by
    calc
      S.toStrategy.value (pauliSymmetricGame Q).toGame =
          T'.toStrategy.value
            (SymmetricGame.ofSymmetricGame
              (MIPStarRE.QPBT.pauliBasisTestSymm Q)).toGame := by
        exact Strategy.value_relabel
          (SymmetricGame.ofSymmetricGame
            (MIPStarRE.QPBT.pauliBasisTestSymm Q)).toGame
          T'.toStrategy (pauliQuestionEquiv Q).symm
          (pauliQuestionEquiv Q).symm (pauliAnswerEquivCompact Q).symm
          (pauliAnswerEquivCompact Q).symm
      _ = T.toStrategy.value := SymmetricStrategy.value_ofSymmetricStrategy T
      _ = 1 := hvalue
  have hP : PauliParams.ofAdmissibleParams Q = P := by
    simp [Q]
  let statement : PauliParams → Prop := fun R =>
    ∃ U : SymmetricPauliStrategy R
        (MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size).K,
      U.IsPauliSPCC R
          (MIPStarRE.QPBT.binaryRepresentation
            (MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size)) ∧
        U.toStrategy.value
          (pauliGame R
            (MIPStarRE.QPBT.binaryRepresentation
              (MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size))
            (MIPStarRE.QPBT.fixedBinTrace
              (MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size))) = 1
  have hstatement : statement (PauliParams.ofAdmissibleParams Q) := by
    let R := PauliParams.ofAdmissibleParams Q
    let fieldStatement : MIPStarRE.QPBT.FixedFieldModel Q.q → Prop := fun F =>
      ∃ U : SymmetricPauliStrategy R F.K,
        U.IsPauliSPCC R (MIPStarRE.QPBT.binaryRepresentation F) ∧
          U.toStrategy.value
            (pauliGame R (MIPStarRE.QPBT.binaryRepresentation F)
              (MIPStarRE.QPBT.fixedBinTrace F)) = 1
    have hfield : fieldStatement Q.model := by
      refine ⟨S, ?_, ?_⟩
      · exact (isPauliSPCC_iff_isSPCC Q S).2 hspccS
      · rw [← pauliSymmetricGame_toGame Q]
        exact hvalueS
    have hmodel : Q.model =
        MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size := by
      rfl
    have htransported := Eq.mp (congrArg fieldStatement hmodel) hfield
    exact htransported
  exact Eq.mp (congrArg statement hP) hstatement

end

end MIPStarRE.QPBT.Palomar
