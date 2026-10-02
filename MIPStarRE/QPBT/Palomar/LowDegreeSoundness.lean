module

public import MIPStarRE.QPBT.Palomar.LowDegreeConsistencyBridge

/-!
# Compact low-degree soundness

This module transports the registered low-degree soundness theorem to the
compact Palomar game surface, preserving its constants, parameter domain,
quantifier order, and three separate consistency conclusions.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-440`,
paper `lem:ld-soundness`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- Quantum soundness of the simultaneous classical low-degree test, in the
compact Palomar presentation (paper `lem:ld-soundness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-440`). -/
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
  classical
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := MIPStarRE.QPBT.exists_ld_soundness
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  rintro ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩ ε hε S hprojective hvalue
  let L : MIPStarRE.QPBT.LdParams :=
    ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩
  have hprojective' : (lowDegreeStrategyToLibrary L S).IsProjective :=
    (lowDegreeStrategyToLibrary_isProjective_iff L S).2 hprojective
  have hvalue' : 1 - ε ≤ (lowDegreeStrategyToLibrary L S).value := by
    rw [lowDegreeStrategyToLibrary_value]
    exact hvalue
  obtain ⟨GA, GB, hpointPolynomial, hpolynomialPoint, hpolynomialPolynomial⟩ :=
    hsound L ε hε (lowDegreeStrategyToLibrary L S) hprojective' hvalue'
  refine ⟨POVM.ofMeasurement GA, POVM.ofMeasurement GB, ?_, ?_, ?_⟩
  · exact (ldPointPolynomialDefect_ofMeasurement_eq L S GB).trans_le
      hpointPolynomial
  · exact (ldPolynomialPointDefect_ofMeasurement_eq L S GA).trans_le
      hpolynomialPoint
  · exact (ldPolynomialPolynomialDefect_ofMeasurement_eq L S GA GB).trans_le
      hpolynomialPolynomial

end

end MIPStarRE.QPBT.Palomar
