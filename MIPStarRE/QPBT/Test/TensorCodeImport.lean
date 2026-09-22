import MIPStarRE.QPBT.Test.TensorCodeImport.PairGeometry
import MIPStarRE.QPBT.Test.TensorCodeImport.PairRegister
import MIPStarRE.QPBT.Test.TensorCodeImport.PairMeasurement
import MIPStarRE.QPBT.Test.TensorCodeImport.PairState
import MIPStarRE.QPBT.Test.TensorCodeImport.Parameters
import MIPStarRE.QPBT.Test.TensorCodeImport.Weights
import MIPStarRE.QPBT.Test.TensorCodeImport.Comparison

/-!
# The source-to-tensor-code strategy reduction

The modules collected here prove the hidden-subcube pair sampling identities,
construct a finite shared register and all six projective measurement families,
and bound the actual tensor-test rejection by `3/2` times source rejection.
The stronger endpoint bound in Definition 4.6 is also proved. Scalar bounds
verify an auxiliary sampling parameter. The cited tensor-code soundness theorem
and transport of its global measurements remain open. The independent direct
low-degree proof does not use these constructions.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-458`
- Ji et al., arXiv:2111.08131v3, Figures 1 and 2 and Theorem 4.7.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/
