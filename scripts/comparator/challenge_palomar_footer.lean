
namespace MIPStarRE.QPBT.Palomar

-- source: MIPStarRE/QPBT/Palomar/PauliCompleteness.lean:21-34
/-- Compact form of paper `lem:pauli-completeness`. -/
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
  sorry

-- source: MIPStarRE/QPBT/Palomar/LowDegreeSoundness.lean:20-44
/-- Compact form of paper `lem:ld-soundness`. -/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : LowDegreeParams) (ε : ℝ), 0 < ε →
        ∀ S : LowDegreeStrategy P (MIPStarRE.QPBT.fixedFieldModel P.q
            P.is_admissible_size).K,
          S.IsProjective →
          1 - ε ≤ S.value (lowDegreeGame P
            (MIPStarRE.QPBT.binaryRepresentation
              (MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size))) →
          ∃ GA : LowDegreePolynomialPOVM P
              (MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size).K S.ιA,
            ∃ GB : LowDegreePolynomialPOVM P
                (MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).K S.ιB,
              ldPointPolynomialDefect P S GB ≤
                  deltaLd a b ε P.q P.m P.d P.k ∧
                ldPolynomialPointDefect P S GA ≤
                  deltaLd a b ε P.q P.m P.d P.k ∧
                ldPolynomialPolynomialDefect P S GA GB ≤
                  deltaLd a b ε P.q P.m P.d P.k := by
  sorry

-- source: MIPStarRE/QPBT/Palomar/PauliSoundness.lean:22-48
/-- Compact form of paper `thm:pauli`. -/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (MIPStarRE.QPBT.binaryRepresentation
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
              (MIPStarRE.QPBT.fixedBinTrace
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := PauliRegister P
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliAliceError P S w
                  (MIPStarRE.QPBT.fixedBinTrace
                    (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawPauliBobError P S w
                  (MIPStarRE.QPBT.fixedBinTrace
                    (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q := by
  sorry

-- source: MIPStarRE/QPBT/Palomar/PauliSoundness.lean:68-95
/-- Compact form of paper `cor:pauli-binary`. -/
theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (MIPStarRE.QPBT.binaryRepresentation
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
              (MIPStarRE.QPBT.fixedBinTrace
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := QubitRegister P
                (MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).basisDim) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawQubitAliceError P S w
                  (MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawQubitBobError P S w
                  (MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q := by
  sorry

end MIPStarRE.QPBT.Palomar

end
