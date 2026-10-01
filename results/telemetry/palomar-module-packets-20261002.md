# Palomar module-conversion ownership inventory

Source snapshot: `97dc6e049b0ce966be18bf8801e14b30c0081919`. The source import graph and file ownership
below are immutable planning inputs, not a lifecycle registry. GitHub #743 and
its child issues hold dependencies and status. Every path is assigned once.

The pilot P0 is issue #744. Subsequent packets use its validated, documented
module/visibility pattern and preserve theorem statements and Lean/Mathlib v4.32.0.
The current owner section 9 permits MAIN to reconsider an in-project route with
a recorded reason and cost. Normal CI and independent review always apply.

A parser-aware scan found 742 files, 1942 imports and 1849 local import edges;
all file SCCs are singletons. The rank is zero for a file with no local dependency
and one plus the greatest dependency rank otherwise. No forward packet edge exists.
P3 and P4 can run independently after P2: P4 does not depend on P3.

## P0: Pilot

Files: 7. Direct packet prerequisites: none.

```text
rank	path
0	MIPStarRE/Quantum/FiniteMatrix/Basic.lean
0	scripts/Checkdecls.lean
1	MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean
1	MIPStarRE/Quantum/FiniteMatrix/Order.lean
2	MIPStarRE/Quantum/FiniteMatrix/BlockDiagonal.lean
2	MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean
3	MIPStarRE/Quantum/FiniteMatrix.lean
```

## P1: Foundation and LDT 1

Files: 142. Direct packet prerequisites: P0.

```text
rank	path
0	MIPStarRE/LDT/Basic/ParametersBase.lean
0	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
0	MIPStarRE/LDT/Preliminaries/Polynomials.lean
0	MIPStarRE/LDT/Tactic/LdtSimpAttr.lean
0	MIPStarRE/Quantum/FiniteConicDuality.lean
0	MIPStarRE/Quantum/FiniteHilbert.lean
1	MIPStarRE/LDT/Basic/AxisParallelLine.lean
1	MIPStarRE/LDT/Basic/RpowBounds.lean
1	MIPStarRE/LDT/Basic/SqrtBounds.lean
1	MIPStarRE/LDT/Preliminaries/FiniteFields.lean
2	MIPStarRE/LDT/Basic/DiagonalLine.lean
2	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean
2	MIPStarRE/Quantum/Measurement.lean
2	MIPStarRE/Quantum/ProjectorONB.lean
3	MIPStarRE/LDT/Basic/LinePolynomials.lean
3	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean
3	MIPStarRE/Quantum.lean
4	MIPStarRE/LDT/Basic/Distribution.lean
4	MIPStarRE/LDT/Basic/LowDegreePolynomial.lean
4	MIPStarRE/LDT/Basic/QuantumState.lean
4	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean
5	MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean
5	MIPStarRE/LDT/Basic/OperatorExpectations.lean
5	MIPStarRE/LDT/Basic/PMFAverages.lean
5	MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean
5	MIPStarRE/LDT/Basic/SubMeasurementCore.lean
5	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta2Zeta3.lean
6	MIPStarRE/LDT/Basic/PMFUniformAverages.lean
6	MIPStarRE/LDT/Basic/TensorPlacement.lean
6	MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean
6	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Zeta4.lean
7	MIPStarRE/LDT/Basic/DistributionUniformSums.lean
7	MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean
7	MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/ErrorBounds.lean
7	MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/Final.lean
8	MIPStarRE/LDT/Basic/DistributionAvg.lean
8	MIPStarRE/LDT/Basic/DistributionPMF.lean
8	MIPStarRE/LDT/Basic/MeasurementLift.lean
8	MIPStarRE/LDT/Basic/OpFamily.lean
8	MIPStarRE/LDT/Tactic/QuantumNonneg.lean
9	MIPStarRE/LDT/Basic/DistributionMapAverages.lean
9	MIPStarRE/LDT/Basic/DistributionProduct.lean
9	MIPStarRE/LDT/Basic/DistributionUniform.lean
9	MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean
9	MIPStarRE/LDT/Pasting/Defs/Tuples.lean
9	MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean
9	MIPStarRE/LDT/Tactic/AvgCongr.lean
9	MIPStarRE/LDT/Test/Defs.lean
10	MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean
10	MIPStarRE/LDT/GlobalVariance/Defs/Core.lean
10	MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean
10	MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean
10	MIPStarRE/LDT/Pasting/Defs/Interpolation.lean
10	MIPStarRE/LDT/Preliminaries/Defs.lean
10	MIPStarRE/LDT/Tactic/LdtSimp.lean
10	MIPStarRE/LDT/Test/SchwartzZippelStep.lean
10	MIPStarRE/LDT/Test/StrategyCore.lean
11	MIPStarRE/LDT/CommutativityPoints/Defs.lean
11	MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean
11	MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean
11	MIPStarRE/LDT/MainInductionStep/Defs.lean
11	MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean
11	MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean
11	MIPStarRE/LDT/Preliminaries/ComparisonCore.lean
11	MIPStarRE/LDT/Test/Classical.lean
11	MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean
11	MIPStarRE/LDT/Test/StrategyRole/Core.lean
12	MIPStarRE/LDT/Commutativity/Defs/Core.lean
12	MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/TraceForms.lean
12	MIPStarRE/LDT/GlobalVariance/Defs/Families.lean
12	MIPStarRE/LDT/MainInductionStep/Statements.lean
12	MIPStarRE/LDT/Pasting/Defs/Families.lean
12	MIPStarRE/LDT/Preliminaries/DistanceBounds.lean
12	MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean
12	MIPStarRE/LDT/Test/StrategyRole/Algebra.lean
12	MIPStarRE/LDT/Test/SurfaceVsPoint.lean
13	MIPStarRE/LDT/Commutativity/Defs/Stability.lean
13	MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean
13	MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean
13	MIPStarRE/LDT/GlobalVariance/Theorems/Statements.lean
13	MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean
13	MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean
13	MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean
13	MIPStarRE/LDT/Test/StrategyFailures.lean
14	MIPStarRE/LDT/Commutativity/Defs/Normalization.lean
14	MIPStarRE/LDT/CommutativityPoints/Approximation.lean
14	MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Matrix.lean
14	MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean
14	MIPStarRE/LDT/Pasting/Defs/Context.lean
14	MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean
14	MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean
14	MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean
15	MIPStarRE/LDT/Commutativity/Scaffold/Core.lean
15	MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean
15	MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean
15	MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean
15	MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/MainError.lean
15	MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean
15	MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Base.lean
15	MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean
15	MIPStarRE/LDT/Preliminaries/ComparisonProjective.lean
15	MIPStarRE/LDT/Preliminaries/Completion.lean
15	MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Core.lean
15	MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/InnerProduct.lean
15	MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Final.lean
16	MIPStarRE/LDT/Commutativity/Scaffold/Symmetry.lean
16	MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean
16	MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Axis.lean
16	MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Diagonal.lean
16	MIPStarRE/LDT/Pasting/Statements.lean
16	MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean
16	MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Left.lean
16	MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Middle.lean
16	MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean
16	MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/ApproxDelta.lean
16	MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/Evaluation.lean
16	MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean
17	MIPStarRE/LDT/Commutativity/Scaffold/Products.lean
17	MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean
17	MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean
17	MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Core.lean
17	MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/Completion.lean
17	MIPStarRE/LDT/Pasting/Bernoulli/MatrixChernoff.lean
17	MIPStarRE/LDT/Pasting/Bernoulli/Weights.lean
17	MIPStarRE/LDT/Pasting/Core/DDistinct.lean
17	MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/LeftTransfer.lean
17	MIPStarRE/LDT/Preliminaries/Triangles/Core.lean
18	MIPStarRE/LDT/Commutativity/EvaluatedSliceBounds/PhaseOneThree.lean
18	MIPStarRE/LDT/Commutativity/ScalarApproximation/Core.lean
18	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean
18	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean
18	MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean
18	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean
18	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean
18	MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean
18	MIPStarRE/LDT/Preliminaries/Triangles/CompleteMeasurements.lean
18	MIPStarRE/LDT/Preliminaries/Triangles/SimEq.lean
19	MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Averages.lean
19	MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean
20	MIPStarRE/LDT/Commutativity/EvaluatedSliceCommutation/Consequences.lean
20	MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean
20	MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean
```

## P2: LDT 2

Files: 109. Direct packet prerequisites: P0, P1.

```text
rank	path
21	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic/PointSwap.lean
21	MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean
21	MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean
21	MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean
22	MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkCore.lean
22	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean
22	MIPStarRE/LDT/Preliminaries/SelfConsistency/Extensions.lean
23	MIPStarRE/LDT/Commutativity/ScalarApproximation/Pointwise.lean
23	MIPStarRE/LDT/GlobalVariance/Theorems/AlgebraicIdentity.lean
23	MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean
23	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean
23	MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean
23	MIPStarRE/LDT/Pasting/Core/CompletePart.lean
23	MIPStarRE/LDT/Pasting/Core/LdGbcon.lean
23	MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean
23	MIPStarRE/LDT/SelfImprovement/Defs.lean
24	MIPStarRE/LDT/Commutativity/GCommStability/OverlapOne.lean
24	MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean
24	MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkFull.lean
24	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean
24	MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean
24	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Base.lean
24	MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean
24	MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Helper.lean
25	MIPStarRE/LDT/Commutativity/GCommStability/OverlapTwo.lean
25	MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Common.lean
25	MIPStarRE/LDT/GlobalVariance/Theorems/PolynomialSumBounds.lean
25	MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean
25	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean
25	MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/Conversion.lean
25	MIPStarRE/LDT/Pasting/SwitcherooSetup/Centers.lean
25	MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean
25	MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean
26	MIPStarRE/LDT/Commutativity/GCommStability/Scalar/First.lean
26	MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean
26	MIPStarRE/LDT/Commutativity/GCommStability/Scalar/Second.lean
26	MIPStarRE/LDT/Commutativity/Transport/EvaluationSpecialization.lean
26	MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean
26	MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean
26	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/AlmostProjective.lean
26	MIPStarRE/LDT/Pasting/SwitcherooSetup/Terms.lean
26	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical.lean
26	MIPStarRE/LDT/SelfImprovement/Theorems/Results/CommonHelpers.lean
26	MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Completeness.lean
27	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean
27	MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean
27	MIPStarRE/LDT/Commutativity/Transport/Pullback.lean
27	MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransportSum.lean
27	MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean
27	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Rows.lean
27	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/RectangularSvd.lean
27	MIPStarRE/LDT/Pasting/SwitcherooContraction/Split.lean
27	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Basic.lean
27	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Witness.lean
27	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean
27	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean
27	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean
28	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseSeven.lean
28	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseSix.lean
28	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainTail.lean
28	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Averages.lean
28	MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/SumForm.lean
28	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean
28	MIPStarRE/LDT/Pasting/SwitcherooContraction/Commuted.lean
28	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Saturated.lean
28	MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean
28	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean
28	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean
28	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean
29	MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainReverse.lean
29	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/QSDD.lean
29	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean
29	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Normalization.lean
29	MIPStarRE/LDT/Commutativity/Transport/FullSlice/ZeroBounds.lean
29	MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean
29	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Sigma.lean
29	MIPStarRE/LDT/Pasting/SwitcherooContraction/ScalarTerms.lean
29	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean
29	MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean
30	MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean
30	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Y.lean
30	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean
30	MIPStarRE/LDT/Pasting/SwitcherooCompletion/Expansion.lean
30	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean
30	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean
30	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean
31	MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean
31	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/ClosenessCore.lean
31	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/ClosenessXEval.lean
31	MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean
31	MIPStarRE/LDT/Pasting/SwitcherooCompletion/FourthTermChain.lean
31	MIPStarRE/LDT/Pasting/SwitcherooCompletion/SecondTerm.lean
31	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Factored.lean
32	MIPStarRE/LDT/Commutativity/Transport/FullSlice/Bridges/Closeness.lean
32	MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean
32	MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean
32	MIPStarRE/LDT/Pasting/SwitcherooCompletion/CompletePart.lean
32	MIPStarRE/LDT/Pasting/SwitcherooCompletion/Utilities.lean
32	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean
32	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean
33	MIPStarRE/LDT/Commutativity/Main/Auxiliary/HEvalTransport.lean
33	MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean
33	MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean
33	MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Handoff.lean
33	MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/MatchMass.lean
33	MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean
33	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean
33	MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean
33	MIPStarRE/LDT/Test/MainTheorem/SourceScalars.lean
```

## P3: LDT 3

Files: 85. Direct packet prerequisites: P1, P2.

```text
rank	path
34	MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean
34	MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Line169Repair.lean
34	MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/Output.lean
34	MIPStarRE/LDT/SelfImprovement/Theorems/AddInUFullStatement.lean
34	MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUPointConsistency.lean
34	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Core.lean
34	MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/Scalars.lean
35	MIPStarRE/LDT/Commutativity/Main/Results.lean
35	MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean
35	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean
36	MIPStarRE/LDT/Pasting/CommutingWithG/Complete.lean
36	MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean
37	MIPStarRE/LDT/Pasting/CommutingWithG/Incomplete.lean
37	MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistencyLiteral.lean
38	MIPStarRE/LDT/Pasting/GHatFacts.lean
38	MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean
39	MIPStarRE/LDT/Pasting/ComparisonLemmas/Common.lean
39	MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean
39	MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean
40	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/Definitions.lean
40	MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Averaging.lean
40	MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Core.lean
40	MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean
41	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/SumBounds.lean
41	MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadLine.lean
42	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Move.lean
42	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Split.lean
42	MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadMass.lean
43	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/StageMass.lean
43	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Base.lean
44	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/FactBundles.lean
44	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean
45	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean
45	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Chain.lean
46	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean
46	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/BackChain.lean
46	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean
47	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/StageA0M1.lean
47	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChainStep.lean
48	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/HalfSandwich.lean
48	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Core.lean
49	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/FinalMove.lean
49	MIPStarRE/LDT/Pasting/ComparisonLemmas/CommuteGHalfSandwich.lean
50	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean
50	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/EndpointEquivs.lean
51	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds.lean
51	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean
52	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Moves.lean
52	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/PrefixMoved.lean
53	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Telescope.lean
53	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean
54	MIPStarRE/LDT/Pasting/Bernoulli/FromHToG.lean
54	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean
55	MIPStarRE/LDT/Pasting/Bernoulli/ScalarBounds.lean
55	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean
56	MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Core.lean
57	MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/HBError.lean
58	MIPStarRE/LDT/Pasting/ComparisonLemmas/HBConsistency.lean
59	MIPStarRE/LDT/Pasting/ComparisonLemmas/HAConsistency.lean
60	MIPStarRE/LDT/Pasting/Bernoulli/DegreeZero.lean
60	MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean
60	MIPStarRE/LDT/Pasting/ContextWrappers.lean
61	MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean
62	MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean
63	MIPStarRE/LDT/Pasting/Bernoulli/Final.lean
64	MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean
65	MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean
66	MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/AnswerValued.lean
67	MIPStarRE/LDT/MainInductionStep/Theorems/StageDataConstructors.lean
68	MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Core.lean
69	MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Successor.lean
70	MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean
71	MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/AnswerFields.lean
72	MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean
73	MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly/Successor.lean
74	MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Base.lean
75	MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems/Successor.lean
76	MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Core.lean
77	MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean
78	MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Final.lean
79	MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean
79	MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/LinearTriangle.lean
80	MIPStarRE/LDT/Test/MainTheorem/LinearTriangle/MainFormal.lean
81	MIPStarRE/LDT.lean
81	MIPStarRE/LDT/Test/AxiomAudit.lean
```

## P4: QPBT 1

Files: 110. Direct packet prerequisites: P0, P1, P2.

```text
rank	path
0	MIPStarRE/QPBT/Algebra/Coefficients.lean
0	MIPStarRE/QPBT/Algebra/Subspaces.lean
1	MIPStarRE/QPBT/Algebra/FieldBasis.lean
1	MIPStarRE/QPBT/Algebra/Lines.lean
1	MIPStarRE/QPBT/Algebra/LowDegreeCode.lean
1	MIPStarRE/QPBT/Algebra/RowEchelon.lean
1	MIPStarRE/QPBT/Algebra/SubspacesTheorems.lean
1	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Polynomial.lean
1	MIPStarRE/QPBT/Games/ErrorFunctions.lean
1	MIPStarRE/QPBT/State.lean
2	MIPStarRE/QPBT/Algebra/LowDegreeCodeTheorems.lean
2	MIPStarRE/QPBT/Algebra/Pauli.lean
2	MIPStarRE/QPBT/Algebra/RowEchelonAlgorithm.lean
2	MIPStarRE/QPBT/Algebra/SelfDualBasis.lean
2	MIPStarRE/QPBT/Combining/PassingError.lean
3	MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean
4	MIPStarRE/QPBT/Algebra/PauliTheorems.lean
5	MIPStarRE/QPBT/Algebra/PrimePauliBasis.lean
9	MIPStarRE/QPBT/Games/Defs.lean
9	MIPStarRE/QPBT/Games/DistributionAux.lean
10	MIPStarRE/QPBT/Combining/Linearity/Defs.lean
10	MIPStarRE/QPBT/Games/CondLinear.lean
10	MIPStarRE/QPBT/Games/Distance.lean
10	MIPStarRE/QPBT/Games/DistributionMarginals.lean
10	MIPStarRE/QPBT/Games/RestrictedAverage.lean
11	MIPStarRE/QPBT/Combining/Linearity/BooleanFourier.lean
11	MIPStarRE/QPBT/Games/CondLinearTheorems/DirectSumSupport.lean
11	MIPStarRE/QPBT/Games/CondLinearTheorems/Reindex.lean
11	MIPStarRE/QPBT/Games/Consistency.lean
11	MIPStarRE/QPBT/Test/LowDegreeGame.lean
11	MIPStarRE/QPBT/Test/MagicSquare.lean
12	MIPStarRE/QPBT/Combining/Linearity/BLR.lean
12	MIPStarRE/QPBT/Games/CondLinearTheorems.lean
12	MIPStarRE/QPBT/Observables/LineDefs.lean
13	MIPStarRE/QPBT/Combining/Lines/ZeroDirectionMass.lean
13	MIPStarRE/QPBT/Games/TypedCondLinear.lean
14	MIPStarRE/QPBT/Test/PauliBasisTest.lean
15	MIPStarRE/QPBT/Combining/DirectLowDegree/Geometry.lean
15	MIPStarRE/QPBT/Combining/ErrorObstruction.lean
15	MIPStarRE/QPBT/ExplicitConstants.lean
15	MIPStarRE/QPBT/Observables/Anticommuting.lean
15	MIPStarRE/QPBT/Test/SoundnessDefs.lean
16	MIPStarRE/QPBT/Combining/RootErrorBounds.lean
16	MIPStarRE/QPBT/Test/CanonicalParams.lean
16	MIPStarRE/QPBT/Test/Soundness/ScalarAbsorption.lean
17	MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean
18	MIPStarRE/QPBT/Combining/OverlapGap.lean
18	MIPStarRE/QPBT/Games/DistanceTheorems/TensorSupport.lean
18	MIPStarRE/Quantum/ControlledUnitary.lean
19	MIPStarRE/QPBT/Combining/ComplexOverlapGap.lean
19	MIPStarRE/QPBT/Games/DistanceTheorems/TensorConsistency.lean
24	MIPStarRE/QPBT/Combining/Linearity/NaimarkRounding.lean
25	MIPStarRE/QPBT/Combining/Linearity/Stability.lean
25	MIPStarRE/QPBT/Games/StrategyClasses.lean
26	MIPStarRE/QPBT/Combining/Linearity.lean
26	MIPStarRE/QPBT/Combining/Linearity/PrintedClaims.lean
26	MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean
26	MIPStarRE/QPBT/Games/GroundCompression.lean
26	MIPStarRE/QPBT/Games/MeasurementCompression.lean
26	MIPStarRE/QPBT/Games/Symmetrization.lean
26	MIPStarRE/QPBT/Observables/Setup.lean
26	MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean
26	MIPStarRE/QPBT/Test/MagicSquareTheorems/Basic.lean
27	MIPStarRE/QPBT/Combining/Defs.lean
27	MIPStarRE/QPBT/Combining/DirectLowDegree/Game.lean
27	MIPStarRE/QPBT/Combining/ErrorBounds.lean
27	MIPStarRE/QPBT/Test/MagicSquareTheorems/PerfectStrategy/Observables.lean
27	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean
28	MIPStarRE/QPBT/Algebra/Decoding.lean
28	MIPStarRE/QPBT/Combining/DirectLowDegree/GameValue.lean
28	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Parameters.lean
28	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Correspondence.lean
28	MIPStarRE/QPBT/Combining/Lines/RestrictedMixture.lean
28	MIPStarRE/QPBT/Combining/Lines/SubLineSupport.lean
28	MIPStarRE/QPBT/Test/MagicSquareTheorems/PerfectStrategy/Measurements.lean
28	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/RejectionBounds.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Answers.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Linearity.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Error.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Questions.lean
29	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedFiber.lean
29	MIPStarRE/QPBT/Combining/Lines/SubLineBlocks.lean
29	MIPStarRE/QPBT/Extraction/PolynomialCollision.lean
29	MIPStarRE/QPBT/Test/MagicSquareTheorems/PerfectStrategy.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/CoefficientCollision.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Error.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Restriction.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/LineResampling.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedError.lean
30	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Strategy.lean
30	MIPStarRE/QPBT/Combining/DirectPassingErrorBounds.lean
30	MIPStarRE/QPBT/Test/Soundness/EpsReduction.lean
31	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/BranchComparison.lean
31	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Coefficients.lean
31	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Consistency/Measurements.lean
31	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedFiberValue.lean
32	MIPStarRE/QPBT/Combining/CombinedPolynomialImage.lean
32	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/ExactLinearity.lean
32	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Consistency/State.lean
32	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/DiagonalRecursion.lean
33	MIPStarRE/QPBT/Combining/BlockSpecialization.lean
33	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Recovery.lean
33	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Consistency/Defect.lean
33	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/PassConversion.lean
34	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Consistency/Compression.lean
34	MIPStarRE/QPBT/Games/DistanceTheorems/ProjectiveRounding.lean
35	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Consistency.lean
35	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/PointAgreement.lean
35	MIPStarRE/QPBT/Games/DistanceTheorems/RoundingTransport.lean
```

## P5: QPBT 2

Files: 110. Direct packet prerequisites: P1, P2, P3, P4.

```text
rank	path
36	MIPStarRE/QPBT/Games/DistanceTheorems.lean
37	MIPStarRE/QPBT/Games/Sandwich/Defs.lean
37	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean
38	MIPStarRE/QPBT/Combining/Lines/FiberCollision.lean
38	MIPStarRE/QPBT/Games/Sandwich/Support.lean
38	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/IdealTarget.lean
38	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Reflections.lean
38	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Transfer.lean
38	MIPStarRE/QPBT/Test/Soundness/RangeProjection.lean
39	MIPStarRE/QPBT/Combining/DirectLowDegree/CoefficientConsistency.lean
39	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Strategy.lean
39	MIPStarRE/QPBT/Combining/PairCompletion.lean
39	MIPStarRE/QPBT/Extraction/OverlapTransfer.lean
39	MIPStarRE/QPBT/Games/Sandwich/Quantitative.lean
39	MIPStarRE/QPBT/Games/SupportMass.lean
39	MIPStarRE/QPBT/Games/SupportedCompletion.lean
39	MIPStarRE/QPBT/Observables/Defs.lean
39	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/AnticommutatorB.lean
39	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/CellRelations.lean
39	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Constants.lean
39	MIPStarRE/QPBT/Test/Soundness/Ancilla.lean
40	MIPStarRE/QPBT/Combining/DirectLowDegree/ResampledCoefficientConsistency.lean
40	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/QuestionLaw.lean
40	MIPStarRE/QPBT/Games/Sandwich/Pasting/SchmidtMirror.lean
40	MIPStarRE/QPBT/Observables/ExpandedDefs.lean
40	MIPStarRE/QPBT/Observables/WinImplications/Setup.lean
40	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Anticommutation.lean
40	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Consistency.lean
40	MIPStarRE/QPBT/Test/Soundness/NaimarkReduction.lean
41	MIPStarRE/QPBT/Combining/DirectLowDegree/ExtendedCoefficientLoss.lean
41	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/GameValue.lean
41	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/WinPredicate.lean
41	MIPStarRE/QPBT/Extraction/Defs.lean
41	MIPStarRE/QPBT/Extraction/EncodingSupport.lean
41	MIPStarRE/QPBT/Games/Sandwich/Pasting/CodewordConsistency.lean
41	MIPStarRE/QPBT/Observables/IdealPointConsistency.lean
41	MIPStarRE/QPBT/Observables/WinImplications/Averages.lean
41	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/SecondPair.lean
41	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Swap.lean
41	MIPStarRE/QPBT/Test/Soundness/NaimarkOperatorTransfer.lean
42	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/Value.lean
42	MIPStarRE/QPBT/Extraction/PauliComparison.lean
42	MIPStarRE/QPBT/Games/Sandwich/Pasting/PinchedReduction.lean
42	MIPStarRE/QPBT/Observables/WinImplications/LowDegree.lean
42	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/TwoQubitSwap.lean
43	MIPStarRE/QPBT/Combining/Lines/AffineEvaluation.lean
43	MIPStarRE/QPBT/Games/Sandwich/Pasting/CrossMove.lean
43	MIPStarRE/QPBT/Observables/LineMeasurement/Evaluation.lean
43	MIPStarRE/QPBT/Observables/LineMeasurement/Restriction.lean
43	MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean
43	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/SwapPair.lean
44	MIPStarRE/QPBT/Combining/Lines/UniformAffineCollision.lean
44	MIPStarRE/QPBT/Games/Sandwich/Pasting/Assembly.lean
44	MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean
44	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/SwapTransport.lean
45	MIPStarRE/QPBT/Games/Sandwich/Pasting/Heterogeneous.lean
45	MIPStarRE/QPBT/Observables/WinImplications/Consistency.lean
45	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/JointState.lean
46	MIPStarRE/QPBT/Combining/ExplicitScalarBounds.lean
46	MIPStarRE/QPBT/Games/Sandwich.lean
46	MIPStarRE/QPBT/Observables/WinImplications/Interchange.lean
46	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/TwoQubitIntertwine.lean
47	MIPStarRE/QPBT/Combining/ActualErrorBounds.lean
47	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/RecoveryDefect.lean
47	MIPStarRE/QPBT/Combining/PolynomialImageBounds.lean
47	MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean
47	MIPStarRE/QPBT/Observables/WinImplications/FactorTransport.lean
47	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Assembly.lean
48	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/RecoveryTransport.lean
48	MIPStarRE/QPBT/Observables/WinImplications/Approx.lean
48	MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Marginals.lean
49	MIPStarRE/QPBT/Observables/WinImplications/PointObs.lean
49	MIPStarRE/QPBT/Test/MagicSquareTheorems.lean
50	MIPStarRE/QPBT/Observables/WinImplications/CommutingObs.lean
50	MIPStarRE/QPBT/Test/MagicSquareTheorems/PrintedClaim.lean
51	MIPStarRE/QPBT/Observables/WinImplications/AnticommutingObs.lean
52	MIPStarRE/QPBT/Observables/WinImplications/TwistedCommutation.lean
53	MIPStarRE/QPBT/Observables/WinImplications/InterchangedCommutation.lean
54	MIPStarRE/QPBT/Observables/WinImplications.lean
55	MIPStarRE/QPBT/Observables/ExpandedPlacement.lean
56	MIPStarRE/QPBT/Observables/ExpandedCommutation.lean
56	MIPStarRE/QPBT/Observables/LineMeasurement/Projector.lean
56	MIPStarRE/QPBT/Observables/LineMeasurement/SquareRootError.lean
57	MIPStarRE/QPBT/Extraction/EPRProjection.lean
57	MIPStarRE/QPBT/Observables/LineMeasurement/Expanded.lean
57	MIPStarRE/QPBT/Observables/PointConsistency.lean
57	MIPStarRE/QPBT/Test/Completeness/HonestStrategy.lean
58	MIPStarRE/QPBT/Extraction/EPRState.lean
58	MIPStarRE/QPBT/Observables/LineMeasurement/SelfConsistency.lean
58	MIPStarRE/QPBT/Test/Completeness/HonestStrategy/MeasurementFamily.lean
59	MIPStarRE/QPBT/Extraction/RegisterTransport.lean
59	MIPStarRE/QPBT/Observables/LineMeasurement/LinePointOverlap.lean
59	MIPStarRE/QPBT/Test/Completeness/Commutation.lean
60	MIPStarRE/QPBT/Observables/LineMeasurement/BipartiteTransport.lean
60	MIPStarRE/QPBT/Test/Completeness/Rejection.lean
61	MIPStarRE/QPBT/Observables/LineMeasurement/EvalClassConsistency.lean
61	MIPStarRE/QPBT/Test/Completeness.lean
62	MIPStarRE/QPBT/Observables/LineMeasurement/LinePointConsistency.lean
63	MIPStarRE/QPBT/Observables/LineMeasurement.lean
64	MIPStarRE/QPBT/Combining/Points/PlacementSupport.lean
65	MIPStarRE/QPBT/Combining/Points/Placement.lean
66	MIPStarRE/QPBT/Combining/Lines/PointwiseDefect.lean
66	MIPStarRE/QPBT/Combining/Points/Commutation.lean
67	MIPStarRE/QPBT/Combining/Lines/RestrictedConsistency.lean
67	MIPStarRE/QPBT/Combining/Points/Sandwich.lean
68	MIPStarRE/QPBT/Combining/Points/Consistency.lean
69	MIPStarRE/QPBT/Combining/Points/Orthonormalization.lean
70	MIPStarRE/QPBT/Combining/Points/Closeness.lean
81	MIPStarRE/QPBT/Combining/QuantitativeDirectScalars.lean
82	MIPStarRE/QPBT/Combining/QuantitativeScalarBase.lean
```

## P6: QPBT 3

Files: 104. Direct packet prerequisites: P1, P3, P4, P5.

```text
rank	path
83	MIPStarRE/QPBT/Combining/QuantitativeNativeScalars/Core.lean
84	MIPStarRE/QPBT/Combining/QuantitativeNativeFractionalScalars.lean
85	MIPStarRE/QPBT/Combining/QuantitativeScalars.lean
86	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Simultaneous.lean
86	MIPStarRE/QPBT/Combining/QuantitativeNativeScalars.lean
86	MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Bounds.lean
87	MIPStarRE/QPBT/Combining/DirectLowDegree/PolynomialConsistency.lean
87	MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean
87	MIPStarRE/QPBT/Combining/QuantitativeNativeGlobalPairScalars.lean
88	MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean
88	MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/NativeSeparated.lean
89	MIPStarRE/QPBT/Combining/DirectLowDegree/AnyStrategySoundness.lean
89	MIPStarRE/QPBT/Combining/DirectLowDegree/SeedIndexedSoundness.lean
89	MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean
89	MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Fractional.lean
90	MIPStarRE/QPBT/Combining/DirectLowDegree.lean
90	MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars/Comparisons.lean
91	MIPStarRE/QPBT/Combining/Witnesses.lean
91	MIPStarRE/QPBT/Test/Soundness/QuantitativeScalars.lean
92	MIPStarRE/QPBT/Combining/Lines/CombinedMeasurement.lean
92	MIPStarRE/QPBT/Combining/Lines/ConsistencyPositivity.lean
92	MIPStarRE/QPBT/Combining/Lines/RestrictedAverage.lean
92	MIPStarRE/QPBT/Combining/Lines/SubLineExtended.lean
92	MIPStarRE/QPBT/Combining/OrderedPoints.lean
92	MIPStarRE/QPBT/Combining/PointErrorObstruction.lean
92	MIPStarRE/QPBT/Combining/Points/Absorption.lean
92	MIPStarRE/QPBT/Combining/PointsDataProcessing.lean
92	MIPStarRE/QPBT/Extraction/Observables.lean
93	MIPStarRE/QPBT/Combining/LinePolynomial.lean
93	MIPStarRE/QPBT/Combining/Lines/ConditionalConsistency.lean
93	MIPStarRE/QPBT/Combining/Lines/Marginal.lean
93	MIPStarRE/QPBT/Combining/Lines/NondegeneratePastingMass.lean
93	MIPStarRE/QPBT/Combining/Lines/SubLineUniform.lean
93	MIPStarRE/QPBT/Combining/Points/MarginalContraction.lean
93	MIPStarRE/QPBT/Combining/PolynomialFiberBounds.lean
93	MIPStarRE/QPBT/Combining/QuadraticPointObstruction.lean
93	MIPStarRE/QPBT/Extraction/Bounds.lean
93	MIPStarRE/QPBT/Extraction/CharacterConsistency.lean
93	MIPStarRE/QPBT/Extraction/PointConsistency.lean
93	MIPStarRE/QPBT/Extraction/PrintedClaims.lean
94	MIPStarRE/QPBT/Combining/Lines/AxisLineResampling.lean
94	MIPStarRE/QPBT/Combining/Lines/DiagonalResampling.lean
94	MIPStarRE/QPBT/Combining/Lines/NondegeneratePastingDistribution.lean
94	MIPStarRE/QPBT/Combining/Lines/SubLinePrefix.lean
94	MIPStarRE/QPBT/Combining/Points/WitnessMarginals.lean
94	MIPStarRE/QPBT/Combining/RetainedPointBounds.lean
94	MIPStarRE/QPBT/Extraction/PointConsistencyPrime.lean
94	MIPStarRE/QPBT/Extraction/PullingMeasurement.lean
95	MIPStarRE/QPBT/Combining/Lines/DiscardedMass.lean
95	MIPStarRE/QPBT/Combining/Lines/MixedResampling.lean
95	MIPStarRE/QPBT/Combining/Lines/PastingRestoration.lean
95	MIPStarRE/QPBT/Combining/Lines/SubLineSeed.lean
95	MIPStarRE/QPBT/Combining/Lines/SubLineTransport.lean
95	MIPStarRE/QPBT/Combining/Points.lean
95	MIPStarRE/QPBT/Extraction/PullingPointConsistency.lean
96	MIPStarRE/QPBT/Combining/ExtendedLineGame.lean
96	MIPStarRE/QPBT/Combining/Lines/NondegeneratePastingResampling.lean
96	MIPStarRE/QPBT/Combining/Lines/SubLineBranch.lean
96	MIPStarRE/QPBT/Combining/Lines/WeightedCollision.lean
96	MIPStarRE/QPBT/Combining/OrderedPolynomialEstimates.lean
96	MIPStarRE/QPBT/Combining/UniformLinePoint.lean
97	MIPStarRE/QPBT/Combining/ExtendedLineGame/NativePointConsistency.lean
97	MIPStarRE/QPBT/Combining/ExtendedLineGame/ParameterCompletion.lean
97	MIPStarRE/QPBT/Combining/ExtendedLineGame/StateTransport.lean
97	MIPStarRE/QPBT/Combining/Lines/NondegenerateFiberCollision.lean
97	MIPStarRE/QPBT/Combining/Lines/ProductWeightedCollision.lean
97	MIPStarRE/QPBT/Combining/Lines/SubLineConstruct.lean
98	MIPStarRE/QPBT/Combining/ExtendedLineGame/LinePointRejection.lean
98	MIPStarRE/QPBT/Combining/ExtendedLineGame/SpectatorExpectation.lean
98	MIPStarRE/QPBT/Combining/Lines/ConditionalCollision.lean
98	MIPStarRE/QPBT/Combining/Lines/PairStateConsistencyTransport.lean
98	MIPStarRE/QPBT/Combining/Lines/SubLineSource.lean
98	MIPStarRE/QPBT/Combining/WitnessErrorNonneg.lean
99	MIPStarRE/QPBT/Combining/ExtendedLineGame/MixedLinePointRejection.lean
99	MIPStarRE/QPBT/Combining/ExtendedLineGame/SameLineRejection.lean
99	MIPStarRE/QPBT/Combining/Lines/SubLineMixture.lean
99	MIPStarRE/QPBT/Extraction/NonencodingSupport.lean
100	MIPStarRE/QPBT/Combining/ExtendedLineGame/PointPointRejection.lean
100	MIPStarRE/QPBT/Combining/ExtendedLineGame/SameLineCoefficientBound.lean
100	MIPStarRE/QPBT/Combining/Lines/PointComparison.lean
100	MIPStarRE/QPBT/Combining/Lines/SubLineJoint.lean
100	MIPStarRE/QPBT/Extraction/Consistency.lean
101	MIPStarRE/QPBT/Combining/ExtendedLineGame/EvaluatedLineComparison.lean
101	MIPStarRE/QPBT/Combining/Lines/Conditioning.lean
101	MIPStarRE/QPBT/Extraction/BlockMeasurement.lean
101	MIPStarRE/QPBT/Extraction/SuppliedPointConsistency.lean
102	MIPStarRE/QPBT/Combining/ExtendedLineGame/LineNoneMass.lean
102	MIPStarRE/QPBT/Combining/Lines/Construction.lean
102	MIPStarRE/QPBT/Combining/Lines/PointSelfConsistencyCompleted.lean
102	MIPStarRE/QPBT/Extraction/PullingDefect.lean
103	MIPStarRE/QPBT/Combining/ExtendedLineGame/ParameterEvaluatedLineBound.lean
103	MIPStarRE/QPBT/Combining/Lines.lean
103	MIPStarRE/QPBT/Extraction/EvaluatedPauliConsistency.lean
103	MIPStarRE/QPBT/Extraction/ObservableConsistency.lean
104	MIPStarRE/QPBT/Combining/ExtendedLineGame/AxisParameterDefectTransport.lean
104	MIPStarRE/QPBT/Combining/ExtendedLineGame/DiagonalParameterDefectTransport.lean
104	MIPStarRE/QPBT/Combining/ExtendedLines/Measurement.lean
104	MIPStarRE/QPBT/Combining/ZEvalDeficit.lean
104	MIPStarRE/QPBT/Extraction/SwappedConsistency.lean
105	MIPStarRE/QPBT/Combining/ExtendedLineGame/PassingValue.lean
105	MIPStarRE/QPBT/Combining/SubLineComplex.lean
105	MIPStarRE/QPBT/Combining/SubLineZDeficit.lean
105	MIPStarRE/QPBT/Extraction/PauliTransport.lean
105	MIPStarRE/QPBT/Extraction/ProjectionFromDistance.lean
```

## P7: QPBT 4

Files: 38. Direct packet prerequisites: P1, P3, P4, P5, P6.

```text
rank	path
106	MIPStarRE/QPBT/Combining/ExtendedLineGame/PolynomialConsistency.lean
106	MIPStarRE/QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean
106	MIPStarRE/QPBT/Combining/ExtendedLineGame/SuppliedDirectSoundness.lean
106	MIPStarRE/QPBT/Combining/Lines/ConcreteXDeficit.lean
106	MIPStarRE/QPBT/Combining/XEvalDeficit.lean
106	MIPStarRE/QPBT/Extraction/ConcretePauliComparison.lean
106	MIPStarRE/QPBT/Extraction/StateExtraction.lean
107	MIPStarRE/QPBT/Combining/Claims.lean
107	MIPStarRE/QPBT/Combining/ExtendedLineGame/ScalarPolynomial.lean
107	MIPStarRE/QPBT/Combining/ExtendedLineGame/SuppliedScalarPolynomialConsistency.lean
107	MIPStarRE/QPBT/Combining/SubLineXDeficit.lean
107	MIPStarRE/QPBT/Extraction/Unitary.lean
108	MIPStarRE/QPBT/Combining/ExtendedLineGame/ScalarNonlinearMass.lean
108	MIPStarRE/QPBT/Combining/ExtendedLines/Overlap.lean
108	MIPStarRE/QPBT/Test/Soundness/StateTransfer.lean
109	MIPStarRE/QPBT/Combining/ExtendedLineGame/WrongVariableMass.lean
109	MIPStarRE/QPBT/Combining/ExtendedLines/Estimates.lean
109	MIPStarRE/QPBT/Test/Soundness/OperatorTransfer.lean
110	MIPStarRE/QPBT/Combining/ExtendedLineGame/PairMeasurement.lean
111	MIPStarRE/QPBT/Combining/ExtendedLineGame/RetainedPointMass.lean
112	MIPStarRE/QPBT/Combining/ExtendedLineGame/PairPointConsistency.lean
113	MIPStarRE/QPBT/Combining/Apply.lean
114	MIPStarRE/QPBT/Combining/Quantitative.lean
114	MIPStarRE/QPBT/Extraction/Construction.lean
114	MIPStarRE/QPBT/Extraction/SourceUnitary.lean
115	MIPStarRE/QPBT/Test/Soundness/ProjectiveSetting.lean
116	MIPStarRE/QPBT/Test/Soundness/NaimarkAssembly.lean
117	MIPStarRE/QPBT/Test/Soundness/RawOperatorTransferCore.lean
118	MIPStarRE/QPBT/Test/Soundness/RawOperatorTransfer.lean
119	MIPStarRE/QPBT/Test/Soundness.lean
119	MIPStarRE/QPBT/Test/Soundness/ComponentBounds.lean
120	MIPStarRE/QPBT/Test/NonVacuity.lean
120	MIPStarRE/QPBT/Test/QuantitativeSoundness.lean
120	MIPStarRE/QPBT/Test/QubitForm.lean
121	MIPStarRE/QPBT/Test/QuantitativeQubitForm.lean
122	MIPStarRE/QPBT.lean
122	MIPStarRE/QPBT/Test/AxiomAudit.lean
123	MIPStarRE.lean
```

## P8: Generated sources and tools

Files: 37. Direct packet prerequisites: P3, P6, P7.

```text
rank	path
0	scripts/comparator/challenge_footer.lean
0	scripts/comparator/challenge_header.lean
0	scripts/comparator/challenge_qpbt_footer.lean
0	scripts/comparator/challenge_qpbt_header.lean
0	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/LDT/Basic/ParametersBase.lean
0	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/LDT/Preliminaries/Polynomials.lean
0	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/Coefficients.lean
0	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/Subspaces.lean
0	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/Quantum/FiniteMatrix/Basic.lean
1	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/FieldBasis.lean
1	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/Lines.lean
1	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/LowDegreeCode.lean
1	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/State.lean
1	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean
2	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/LDT/Basic/Distribution.lean
2	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/Pauli.lean
2	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/SelfDualBasis.lean
2	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/Quantum/Measurement.lean
3	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean
3	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/CondLinear.lean
3	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/Defs.lean
3	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/DistributionAux.lean
4	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Algebra/PauliTheorems.lean
4	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/Consistency.lean
4	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/TypedCondLinear.lean
4	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/LowDegreeGame.lean
4	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/MagicSquare.lean
5	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Games/StrategyClasses.lean
5	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/PauliBasisTest.lean
6	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Observables/WinImplications/Setup.lean
6	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean
6	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/SoundnessDefs.lean
7	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/Completeness.lean
7	scripts/comparator/expected/qpbt/Challenge/MIPStarRE/QPBT/Test/QubitForm.lean
8	scripts/comparator/expected/qpbt/Challenge.lean
80	scripts/comparator/extract_closure.lean
114	results/telemetry/native-audits/pr549-01a0a525/PR549NativeChecks.lean
```

## Special handling

P8 preserves the original bytes of the historical telemetry harness as archival
text; any extension change must be accompanied by a relocation note and hash.
Comparator header/footer inputs are templates, not standalone modules. Rename
their non-source inputs consistently with generator/config references, and
regenerate actual Lean outputs with exactly one module header. All retained
regular Lean files must satisfy Palomar; no proof or source is hidden to evade
a source-size restriction. All files are already within its 10000-line limit.

The four LDT tactic files, both theorem axiom audits, Checkdecls, the closure
extractor and the historical command elaborator need deliberate meta handling.
The aggregate public import surfaces and exposed definition bodies must remain
available to existing consumers. The committed library and expected statement
declarations preserve their mathematical meaning.
