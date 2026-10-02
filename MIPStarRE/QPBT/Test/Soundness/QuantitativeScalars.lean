module

public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.Bounds
public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.NativeSeparated
public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.Fractional
public import MIPStarRE.QPBT.Test.Soundness.QuantitativeScalars.Comparisons

/-!
# Final quantitative scalar bounds for Pauli soundness

This module converts the quantitative global-pair error into the common state
and raw-operator error used by the final Pauli soundness theorem. It also
compares the resulting degree-four bound with the fixed explicit baseline and
with the canonical `deltaQld` form.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1491`
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`
-/
