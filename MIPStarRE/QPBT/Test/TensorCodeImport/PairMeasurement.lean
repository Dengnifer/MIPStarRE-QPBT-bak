import MIPStarRE.QPBT.Test.TensorCodeImport.PairRegister
import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiber
import MIPStarRE.QPBT.Games.Sandwich.Support

/-!
# Projective measurements for visible pairs

The shared finite register selects a compatible source diagonal question
for each visible pair. In each block the source measurement is performed
once and its polynomial is evaluated at both endpoints. Thus the pair
measurement depends only on the pair and the local shared register, and it
is projective whenever the source measurements are projective.

This constructs the pair family needed by the tensor-code reduction. The
joint Born-weight comparison and the complete game-value estimate remain
separate obligations; projectivity alone does not prove them.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-272,443-458`
- Ji et al., arXiv:2111.08131v3, Figures 1 and 2 and Definition 4.5.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- Evaluate a source diagonal answer at the parameters `t` and `t+1`
for the sampled endpoints. Wrong-type answers are completed to `(0,0)`;
the source rejects them, so a value comparison must account for their mass.
For a zero direction, the source's universal evaluation predicate still
checks both of these parameters. -/
def pairReadout (D : DirectLdParams) (r : Fin D.k) (sample : DirectLdSpace D) :
    DirectLdAnswer D → DirectScalarQ D × DirectScalarQ D
  | .dlinePolys f =>
      let t := directLineRepParameter
        (directPrefixProjection sample.index sample.direction) sample.point
      (evalCoefficient (f r) t, evalCoefficient (f r) (t + 1))
  | _ => (0, 0)

/-- The pair measurement in a common finite register. It is indexed only by
the visible pair; the hidden subcube is selected internally by the register.
For the source import one uses the unique coordinate when `D.k = 1`. -/
def pairMeasurement (D : DirectLdParams) (r : Fin D.k)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
    (pair : PairQuestion D) :
    MIPStarRE.Quantum.Measurement (DirectScalarQ D × DirectScalarQ D)
      (ι × PairRegister D) :=
  blockDiagonalMeasurement fun register =>
    let sample := (register pair).val
    (M (.dline, directLdMap D .dline sample)).postprocess (pairReadout D r sample)

/-- Projectivity of the constructed pair measurement follows from
postprocessing within each register block. No averaging of projections on
the original Hilbert space is used. -/
theorem pairMeasurement_isProjective (D : DirectLdParams) (r : Fin D.k)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : DirectLdQuestion D → MIPStarRE.Quantum.Measurement (DirectLdAnswer D) ι)
    (hM : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (M q))
    (pair : PairQuestion D) :
    MIPStarRE.QPBT.Measurement.IsProjective (pairMeasurement D r M pair) := by
  apply blockDiagonalMeasurement_isProjective
  intro register
  exact SandwichProduct.postprocess_isProjective _ (hM _) _

end

end MIPStarRE.QPBT.TensorCodeImport
