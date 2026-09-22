import MIPStarRE.QPBT.Test.TensorCodeImport.Rejection

/-!
# Rejection probabilities of the tensor-code test

These definitions evaluate the actual measurement families against the
predicates of Figures 1--2. The referee's endpoint bit is retained in the
rejection calculation, not revealed as part of a pair question. Thus even
a repeated pair has the two ordered answer positions required by the test.

## References

- Ji et al., arXiv:2111.08131v3, Figures 1--2 and Definition 4.6.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:443-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, import obligations (#704).
-/

namespace MIPStarRE.QPBT.TensorCodeImport

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Select an ordered endpoint or its answer position. -/
def endpoint {α : Type*} (second : Bool) (pair : α × α) : α :=
  if second then pair.2 else pair.1

/-- Axis-line versus point rejection, averaged over the two player roles.
The unused direction in the uniform sample has no effect on either question. -/
def TensorCodeStrategy.axisRejection {D : DirectLdParams} (T : TensorCodeStrategy D) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
    let line := axisQuestion D sample
    let u := fun j => sample.point j.rev
    let t := sample.point sample.index
    (measurementRejection T.ψ (T.axisA line) (T.pointB u)
        (fun word a => decide (word.val t = a)) +
      measurementRejection T.ψ (T.pointA u) (T.axisB line)
        (fun a word => decide (word.val t = a))) / 2

/-- One endpoint's pair-versus-point rejection, with uniform player roles.
Neither the hidden subcube nor its dimension occurs in a measurement index. -/
def TensorCodeStrategy.endpointRejection {D : DirectLdParams}
    (T : TensorCodeStrategy D) (second : Bool) : ℝ :=
  avgOver (tensorPairDistribution D) fun pair =>
    (measurementRejection T.ψ (T.pairA pair) (T.pointB (endpoint second pair))
        (fun ab a => decide (endpoint second ab = a)) +
      measurementRejection T.ψ (T.pointA (endpoint second pair)) (T.pairB pair)
        (fun a ab => decide (endpoint second ab = a))) / 2

/-- Point synchronicity rejection. The redundant independent source index
and direction are forgotten, leaving a uniform geometric point. -/
def TensorCodeStrategy.pointSyncRejection {D : DirectLdParams}
    (T : TensorCodeStrategy D) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
    let u := fun j => sample.point j.rev
    measurementRejection T.ψ (T.pointA u) (T.pointB u) (fun a b => decide (a = b))

/-- Axis-line synchronicity rejection, with the axis test's line marginal. -/
def TensorCodeStrategy.axisSyncRejection {D : DirectLdParams}
    (T : TensorCodeStrategy D) : ℝ :=
  avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
    let line := axisQuestion D sample
    measurementRejection T.ψ (T.axisA line) (T.axisB line) (fun a b => decide (a = b))

/-- Ordered-pair synchronicity rejection, with the hidden-subcube pair law. -/
def TensorCodeStrategy.pairSyncRejection {D : DirectLdParams}
    (T : TensorCodeStrategy D) : ℝ :=
  avgOver (tensorPairDistribution D) fun pair =>
    measurementRejection T.ψ (T.pairA pair) (T.pairB pair) (fun a b => decide (a = b))

/-- The weighted rejection probability: three equally weighted subtests,
uniform roles and endpoint bit, and three equally weighted synchronous types.
Exchangeability of the pair law identifies the endpoint average with the
order-bit experiment in Figure 1. -/
def TensorCodeStrategy.rejection {D : DirectLdParams} (T : TensorCodeStrategy D) : ℝ :=
  T.axisRejection / 3 + (T.endpointRejection false + T.endpointRejection true) / 6 +
    (T.pointSyncRejection + T.axisSyncRejection + T.pairSyncRejection) / 9

/-- The error used by Definition 4.6, which bounds each endpoint separately.
It also bounds the referee's mean endpoint rejection. -/
def TensorCodeStrategy.goodnessError {D : DirectLdParams} (T : TensorCodeStrategy D) : ℝ :=
  T.axisRejection / 3 + max (T.endpointRejection false) (T.endpointRejection true) / 3 +
    (T.pointSyncRejection + T.axisSyncRejection + T.pairSyncRejection) / 9

end

end MIPStarRE.QPBT.TensorCodeImport
