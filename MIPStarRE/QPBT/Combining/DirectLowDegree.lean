module

public import MIPStarRE.QPBT.Combining.DirectLowDegree.Soundness
public import MIPStarRE.QPBT.Combining.DirectLowDegree.AnyStrategySoundness
public import MIPStarRE.QPBT.Combining.DirectLowDegree.CoefficientCollision
public import MIPStarRE.QPBT.Combining.DirectLowDegree.CoefficientConsistency
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Consistency
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.LineResampling
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Strategy
public import MIPStarRE.QPBT.Combining.DirectLowDegree.GameValue
public import MIPStarRE.QPBT.Combining.DirectLowDegree.RejectionBounds
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PassConversion
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Error
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Simultaneous
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Strategy
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.GameValue
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.WinPredicate
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Value
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Restriction
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.ExactLinearity
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Recovery
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryDefect
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryTransport
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.SimultaneousGeneral
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.Combining.Error
public import MIPStarRE.QPBT.Combining.DirectLowDegree.Transport.PointAgreement
public import MIPStarRE.QPBT.Combining.DirectLowDegree.SeedIndexedSoundness
public import MIPStarRE.QPBT.Combining.DirectLowDegree.ResampledCoefficientConsistency
public import MIPStarRE.QPBT.Combining.DirectLowDegree.ExtendedCoefficientLoss

/-!
# The directly indexed low-degree game

The low-degree game used by the Pauli-basis combining argument is needed in
dimension `2 * m + 2`.  The existing conditionally linear game represents a
coordinate index by an equally sized fiber in the scalar field and therefore
requires the dimension to divide the field size.  This file gives the separate
directly indexed variant which samples that index directly.

The geometric line carrier records the sampled coordinate, and line evaluation
uses an `Option` outcome rather than assigning a value when a point does not
determine one.  The game retains the point, axis-line, and diagonal-line answer
formats and the nine ordered type branches of the original low-degree game.

The `Transport` modules relate the direct game to the seed-indexed game and to
the low individual degree test: `Transport.Correspondence`
identifies coordinates, answers, and the question law of the two QPBT
presentations; `Transport.SeedFiber` dilates a seed-indexed strategy to a
direct strategy by a correlated residue register, and `Transport.SeedFiberValue`
shows that the dilation preserves the value exactly; `Transport.Questions`
reads LDT lines as canonical direct questions and rebases direct answers;
`Transport.Strategy` reads one coordinate of a projective direct strategy as
an LDT projective strategy, with exact Born-weight formulas for both
constructions; `Transport.Consistency` reexpresses the three
single-polynomial LDT consistency relations in direct coordinates, the first
two at a fixed tuple coordinate; and
`Transport.BranchComparison`, `Transport.DiagonalRecursion`, and
`Transport.PassConversion` convert a value bound of the direct game into the
pass hypothesis of the low individual degree theorem for every
coordinate strategy.  `GameValue` supplies the rejection calculus relating the
direct value to the LDT branch weights.  `Transport.Error` carries the
scalar half of the transport: the auxiliary sampling parameter with which
the low individual degree theorem is applied, bounds on the three terms of its
error function, and the absorption of the resulting simultaneous-measurement
estimate into the error function of `lem:ld-soundness`; and
`Transport.Simultaneous` applies that theorem to every coordinate, carries
the Schwartz--Zippel collision estimate to the direct polynomial
representatives, and proves the polynomial-tuple conclusion of
`lem:ld-soundness` for simultaneity parameter `1`.  It also records why the
coordinate conclusions do not determine simultaneous measurements for larger
parameters.  `Transport.PointAgreement` reads the point-agreement branch of
either game as a consistency estimate, and `SeedIndexedSoundness` transports
the polynomial-tuple conclusions back to the seed-indexed game `ldGame` by
compressing the correlated residue register, recovering the global polynomial
relation from the two point relations and the point-agreement branch.

For a general simultaneity parameter, the reduction introduces the combined
parameters `DirectLdParams.combined`, of dimension `m + k` and simultaneity
parameter `1`; the combining map on polynomial tuples and its individual-degree
bound; the substitution recovering the components of a combined polynomial,
which exhibits the combining map as injective; and the Schwartz--Zippel
collision estimate for two linear forms in the combining variables; and the
combined strategy itself, which answers every question of the combined game by
measuring one question of the original strategy and relabelling its outcome,
together with its projectivity, the identification of the measured questions on
each sample of the combined game, and the transport of its value.  The recovery
of the components of a combined outcome costs `(m + k) d / q` in the two point
relations.  The general-simultaneity theorem combines these constructions, and
the scalar estimate absorbs the resulting error into the error function of
`lem:ld-soundness`; see
`blueprint/src/chapter/ch13_qpbt_test.tex`, the subsection on the combining
reduction.

## References

The underlying game is blueprint
`def:ld-game`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The need for the directly indexed repair in Chapter 15 is explained around
blueprint
`rem:qld-4-7-divisibility` and in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/
