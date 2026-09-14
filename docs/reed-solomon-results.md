# Quantitative Reed–Solomon bounds: reader's guide

This branch accompanies the paper's mathematical list-decoding and mutual correlated
agreement (MCA) results and its ProveKit, ZisK, and LambdaVM parameter certificates.
Start with the [mathematical guide](../ArkLib/Data/CodingTheory/ReedSolomon/PaperGuide.lean)
and the [application guide](../ArkLibExamples/ReedSolomon/PaperGuide.lean).

The branch is `quang/reed-solomon-quantitative-bounds`. Its starting validated revision is
`ffab000e71c5b19e8a19bebadcc0050eac1366e3`; subsequent edits need their own validation.
The [completion handoff](design/reed-solomon-release-handoff.md) records that work.

## Scope

The paper retains bounded-input list recovery, but this development does not formalize it.
The paper no longer states the separate exact-on-the-first-order-curve endpoint corollary.
Its headline first-order theorem continues to require a positive agreement gap.

The mathematical guide does not import the executable decoder guide. Decoder source is
preserved, and the generated `ArkLib` umbrella still imports it; this is an entrypoint
separation, not a physically pruned repository. Running-time analysis and verification of
complete deployed proof systems are outside scope. Decoder development continues separately.

## Headline results to read and review

These stable IDs are the author's watchlist. A result counts as readable only after both its
docstring and its statement annotations have been checked against the standard below.
Existing prose should be retained when it already meets that standard. Every row below has now
completed that review.

All declaration names below are relative to `ReedSolomon` unless another namespace is given.

| ID | Result and paper role | Exact source and declarations | Readability status |
|---|---|---|---|
| R1 | Complete Johnson list bound, every characteristic | [Johnson/WeightedCertificate](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean): `closePolynomialSet_finite_and_ncard_le_johnsonPairwise` | Source-reviewed, annotated, and compiled |
| R2 | Johnson MCA, including the sharper weighted certificate | [Johnson/Agreement](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean): `exists_exceptional_johnson_lineMCA_allChar`; [WeightedCertificate](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean): `exists_exceptional_weightedJohnsonMCA_fullAgreement` | Source-reviewed, annotated, and compiled |
| R3 | Headline first-order list and MCA bounds, both rate branches | [FirstOrder/Branchwise](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Branchwise.lean): `FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds`, `FirstOrder.firstOrderBranch_finiteLength_rate_bounds`, `FirstOrder.firstOrderBranch_finiteLength_mcaError_le` | Source-reviewed, annotated, and compiled |
| R4 | Finite first-order curve certificate used by the applications | [FirstOrder/HybridCurveProfile](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/HybridCurveProfile.lean): compatibility `CurveCertificate.exists_exceptional_exact_powerAgreement_best` and paper-exact `CurveCertificate.exists_exceptional_exact_powerAgreement_best_optimized`; [Squarefree/Sharp](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean): `FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp_at`, `FirstOrder.Squarefree.exists_exceptional_retainedSquarefreeCurveMCA_sharp_optimized`, `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized` | Source-reviewed, annotated, and compiled |
| R5 | Fixed-order lists from the rate-dependent gate | [ListDecodability/Capacity/RatePartition](../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/RatePartition.lean): `exists_ratePartition_list_bound` | Source-reviewed, annotated, and compiled |
| R6 | Fixed-order line MCA from the same gate | [MCA/Capacity/RatePartition](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/RatePartition.lean): `exists_ratePartition_lineMCA_parameters` | Source-reviewed, annotated, and compiled |
| R7 | Explicit derivative order at a fixed rate and gap: lists | [ListDecodability/Capacity/FixedRateExplicitGate](../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity/FixedRateExplicitGate.lean): `fixedRatePartitionOrder_list_bound_selected`, `fixedRatePartitionOrder_list_bound` | Source-reviewed, annotated, and compiled |
| R8 | The same explicit fixed-rate order: line MCA | [MCA/Capacity/FixedRateExplicitGate](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/FixedRateExplicitGate.lean): `fixedRatePartitionOrder_lineMCA` | Source-reviewed, annotated, and compiled |
| R9 | List decoding up to capacity, uniformly over all rates | [ListDecodability/Capacity](../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean): `exists_rateCapacity_list` and the property `HasCapacityLists` | Source-reviewed, annotated, and compiled |
| R10 | MCA up to capacity, uniformly over all rates | [MCA/Capacity](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean): `sharpCapacity_lineAgreement`, `exists_sharpCapacity_lineAgreement`, and `HasSharpCapacityLineAgreement` | Source-reviewed, annotated, and compiled |
| R11 | Affine families and powers batching | [MCA/Capacity](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean): `sharpCapacity_affineAgreement_and_mcaError`, `sharpCapacity_powerBatchingAgreement`; R4 supplies the finite first-order powers bound | Source-reviewed, annotated, and compiled |
| R12 | Interleaving and shared-level multilinear folds | [Interleaved/PowerAgreementArbitrary](../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/PowerAgreementArbitrary.lean): `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary`; [BinaryTensorFoldAgreement](../ArkLib/Data/CodingTheory/ProximityGenerator/BinaryTensorFoldAgreement.lean): `TensorMCA.tensorFoldBad_card_le`; [RS specialization](../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean): `fullSetLevelWitness_interleaved_of_exactAgreement`, `interleavedRS_tensorFoldBad_card_le_heightThree` | Source-reviewed, annotated, and compiled |

The statement-reading pass must also cover the definitions that make these conclusions
meaningful: `closePolynomialSet` in [AgreementList](../ArkLib/Data/CodingTheory/ReedSolomon/AgreementList.lean),
`HasExactCorrelatedPair` in [Symbolic/RegularEquation](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Symbolic/RegularEquation.lean),
and `HasExactPowerAgreement` in [PolynomialCurve/FullAgreement](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PolynomialCurve/FullAgreement.lean).
Also explain `firstOrderBranchThreshold`, `finiteLengthSlack`, `ratePartitionGamma`,
`fixedRatePartitionOrder`, and the piecewise capacity parameter functions at their owner modules.
Do not make readers expand several definitions merely to discover the theorem's guarantee.

Two application-facing connections are part of the same watchlist, not optional follow-ups:
R4 retains the compatibility theorem
`CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp` and adds the
paper-exact `CurveCertificate.exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized` in
[Squarefree/Sharp](../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean).
R12 includes `fullSetLevelWitness_interleaved_of_exactAgreement` and
`interleavedRS_tensorFoldBad_card_le_heightThree` in the
[Reed–Solomon tensor-fold specialization](../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean).

## Application results to read and review

The [application guide](../ArkLibExamples/ReedSolomon/PaperGuide.lean) gives exact names for
all 15 ProveKit, eight ZisK, and nine LambdaVM curve certificates. Review those families
through their common wrappers rather than copying 32 near-identical explanations.

| ID | Mathematical output | Primary source targets | Readability status |
|---|---|---|---|
| A1 | ProveKit certificate coverage, allocated errors, expected payload savings | [CurveMigration](../ArkLibExamples/ReedSolomon/CurveMigration.lean), [ProveKit](../ArkLibExamples/ReedSolomon/ProveKit.lean), [AnalyticalBudgets](../ArkLibExamples/ReedSolomon/ProveKit/AnalyticalBudgets.lean), [AnalyticalExpectedPayload](../ArkLibExamples/ReedSolomon/ProveKit/AnalyticalExpectedPayload.lean); guide-listed budget and saving theorems | Source-reviewed, annotated, and compiled |
| A2 | ZisK composed exceptional sets, 51-query target, 11,760-byte reduction | [ZisK](../ArkLibExamples/ReedSolomon/ZisK.lean): `ArkLibExamples.ReedSolomon.ZisK.exists_nested_exceptional`, `queries_at_target`, `proof_size` (see imported owner modules) | Source-reviewed, annotated, and compiled |
| A3 | LambdaVM CPU budget, 208-query local error, nominal and expected savings | [LambdaVM](../ArkLibExamples/ReedSolomon/LambdaVM.lean): `ArkLibExamples.ReedSolomon.LambdaVM.CPU.exists_certified_cpu_budget`, `proof_size`, `expectedNetSaving_bounds` (see imported owner modules) | Source-reviewed, annotated, and compiled |

For A1–A3, explain which quantities are measured inputs, which are assumptions about a
protocol, and which inequalities or byte identities Lean proves. Preserve separate phase
allocations and the distinction between a local subproof guarantee and whole-system security.

## Standard for readable theorem statements

Each headline docstring should let a mathematically trained reader answer:

1. What question does this theorem settle, and which paper result does it represent?
2. What do the rate, gap, length, message degree, integer agreement threshold, and degree
   bounds mean? State the useful formula, not just an internal recipe name.
3. Which quantities are fixed before the field, code, and received word? Which witnesses
   may depend on the challenge or candidate?
4. What are the field and characteristic hypotheses? Is the result over arbitrary fields,
   finite fields, or an explicitly presented field? Do not confuse characteristic with size.
5. Does the conclusion give a complete finite list, a bound, common witnesses, equality of
   full agreement sets, or a probability? Explain the distinction.

Place short inline comments before meaningful binder/conclusion groups: parameter choice,
code and agreement hypotheses, characteristic guard, exceptional set, candidate quantifiers,
and witness conclusion. Do not annotate every line or restate Lean syntax in English.
Keep proofs and theorem types unchanged during the readability-only pass.

Particular traps to explain are `degree < k` versus `natDegree`, `k/n` versus `(k-1)/n`,
`eta > 0` versus `eta + 1/n`, integer rounding, `Set.Finite` alongside `Set.ncard`, and the
single exceptional set that precedes both challenge and candidate. Explain the constant-code
and empty-list branches where the exported theorem includes them.

## Checking this entrypoint

After setting up the repository's pinned dependencies, build the mathematical and application
guides with `lake build ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide
ArkLibExamples.ReedSolomon.PaperGuide`. Before publication, run the full repository gate
`./scripts/validate.sh --axioms` and audit the mathematical import closure separately.
The full gate still tests the repository's retained decoder code; it is not a claim that this
branch implements the paper's fast decoder.
