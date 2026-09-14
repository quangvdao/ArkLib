/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CapacityDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SquareSystemDecoder
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.RepresentedExact
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.CoefficientCRT
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.FiberPreprocess

/-!
# Decoder map for the Reed--Solomon capacity paper

This module is a reader index for the algorithms in [DKTZ26]. It imports retained reference
interfaces and records their integration boundary. It adds no executable wrapper or cost claim.
Current implementation coordination is maintained in `docs/design/decoder-plan/README.md`.

## Exact hidden-derivative decoding

`HiddenDerivativeDecoder.runSupplied` and `runCertified` implement the paper branch order,
checked equation/support inputs, and the impossible-agreement, constant and bounded-fallback
branches. Their successful easy outputs are exact. The symbolic branch still returns
`symbolicBackendUnavailable`; success for all supported inputs is not yet proved.

`PositionSubsetDecoder.run_exact` is the authorized fallback's exactness theorem.
`ReedSolomon.capacity_decoder_exact_output_and_primitive_work` describes the retained coordinate
executor and its observed primitive-work ledger. It is not the paper's symbolic decoder.
Mathematical list theorems in `ReedSolomon.PaperGuide` describe finite sets; classical extraction
of those sets does not implement the missing symbolic algorithm.

## Recovering agreement from finite representations

`TowerRepresentation` stores canonical coefficients in `(E[U]/G)[V]/h` without extracting roots.
`AgreementRecovery.BatchedTower.recoverAgreement_represented_exact` proves represented-family
exactness for actual product-tree restriction, fiber-local splitting, stopping and interpolation,
final agreement filtering, and deduplication. `recoverAgreement_exact_of_coverage` promotes this
to the existing `ExactOutput` contract once an actual constructor's coverage theorem is supplied.
Coverage is proof-only, not an input to the runtime.

The univariate `FiniteRepresentation` and `AgreementRecovery.decode_represented_exact` remain
available as the special-case consumer and compatibility interfaces. Tower recovery is implemented;
the missing work is construction and coverage of the full symbolic candidate families.

## Finite-algebra split, preprocessing and materialization

`TowerAlgebra.SplitZeroUnit` uses a powered residual to retain full primary factors of a possibly
nonreduced fiber. `PrimaryAccounting` proves geometric disjointness and dimension accounting;
`LocalizeFiber` retains the open locus without radicalizing the fiber. The stronger squarefree
invariant and legacy preprocessing remain available as compatibility interfaces.

`ReductionAlgebra` proves quotient-normalization laws. `Inverse` and `GeometricSeparation` prove
unit completeness and the geometric nonvanishing criterion. `InverseElimination` executes a
verified elimination backend equal to the Cramer reference; `Materialize` uses it to produce
canonical message coefficients with correct rational specialization. These are complete finite
algebra foundations. The reduced multiplication-table consumer additionally handles the finite
boundary representation, once its producer is supplied.

## First-order curve candidates

`FirstOrderCurveCandidates.Producer.run` executes closed-primary-component removal,
lowest-resultant-coefficient filtering, the distinct-position threshold, one radical, localization,
actual-denominator inversion and centered materialization. Its `SourceCoverage` theorem proves
chart-local exact output from actual constructor/source coverage and source squarefreeness, with
no threshold-root, candidate-membership or payload-identity oracle. `ProducerBudget` bounds base
degree and full nonreduced dimension in terms of computed filter degrees.

Global common-center preparation and its ordinary/open/boundary family union remain unfinished.
The legacy norm/universal-component implementation is retained, not the new canonical filter.

## Selected systems and isolated roots

`SquareSystemDecoder.run_exact_of_torus_cover` is conditional on a `TorusBackend` satisfying
`CoversTorusIsolatedRoots`. Its older affine-shift and tail-coordinate construction does not
implement the current direct affine system. `HigherOrderProducer.RobustBallChart` now provides
actual direct systems in exhaustive and robust modes, with agreeing full-span selection, Jacobian
and isolation capture under the chart hypotheses. These hypotheses still need global instantiation.

The dense Rojas producer has unconditional univariate and affine-linear cases. General nonlinear
quotient success, input-derived perturbation factorization, algebraic-closure isolated-root coverage
and coordinate separation under the quadratic field-size guard remain open. Conditional safe-map
and root-data theorems must not be advertised as this completed producer.

## Regular Taylor and dedicated zeroth-order decoding

`ComputedTaylorMap` and the mathematical Taylor chart provide rational numerator identities and
regular-solution specialization. The existing `FastTaylor.construct?` computes a one-chart family
using its retained Newton backend. Checked division-free triangular preparation and recurrence now
have cleared-numerator provenance; switching the canonical constructor and transferring its global
agreement contract remain separate tasks. General relaxed-scheduler correspondence also remains.

`OrdinaryInterpolation` already executes Lee--O'Sullivan interpolation with the verified fast
Mulders--Storjohann reducer. `OrdinaryQuotientDecoder` executes quotient Newton doubling and shared
recovery. `OrdinaryInterpolatedDecoder.run_exact_of_regular_center` composes them conditionally.
`ZerothOrderDecoder.EffectivePublicDecoder.run?_exists_exact` gives a data-only public decoder
under its `Valid` contract over supplied effective fields. It computes interpolation, normalization,
centers, transport and recovery internally, including characteristic two and `k > p`. This exactness
result does not assert the prescribed fast interpolation backend or a bit-complexity theorem.
The normalized Jordan-module frames exist; JNSV minimal-basis execution remains unfinished.

## Verification boundary

The coordination handoff records exact source inputs and the current validation procedure.
The public positive-order decoder still needs concrete producers, global coverage and exactness
of its actual execution in both selection modes. Arithmetic, bit and RAM complexity proofs are
outside the implementation task. This reader index retains its reference imports; it does not
itself re-export every newer endpoint named above.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], decoding algorithms and appendices.
-/

@[expose] public section
