/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide
import ArkLibExamples.ReedSolomon.AppendixCurveMCA
import ArkLibExamples.ReedSolomon.CurveMigration
import ArkLibExamples.ReedSolomon.JohnsonTable
import ArkLibExamples.ReedSolomon.LambdaVM
import ArkLibExamples.ReedSolomon.ProveKit
import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalBudgets
import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalExpectedPayload
import ArkLibExamples.ReedSolomon.ZisK

/-!
# Concrete applications of the quantitative Reed--Solomon results

This is the application companion to the reusable `ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide`.
It imports maintained concrete parameter instantiations without introducing a dependency from
`ArkLib` to `ArkLibExamples`.

## Current curve-aware application rows

`ArkLibExamples.ReedSolomon.CurveMigration` is the semantic owner for the 32 application curves
used by the current paper. Every row applies
`ReedSolomon.CurveCertificate.exists_exceptional_exact_powerAgreement_best`, so the returned bound
is the minimum of independently proved optimized-hybrid and factorwise-squarefree compatibility
envelopes and still has an exact power-agreement theorem. The squarefree compatibility expression
keeps the historical ordinary threshold `L₀ = D+1`, preserving the application constants already
checked by the paper's arithmetic ledger. The reusable mathematical guide also exposes
`exists_exceptional_exact_powerAgreement_best_optimized`, whose independently minimized ordinary
threshold is the paper-exact factorwise objective and is proved no larger. The application rows
deliberately do not replace their frozen constants with that potentially smaller value.

* The 15 ProveKit curves are exposed by
  `ArkLibExamples.ReedSolomon.CurveMigration.ProveKit.passportOuter_exists_exceptional_best` for
  six Passport outer rows,
  `ArkLibExamples.ReedSolomon.CurveMigration.ProveKit.passportInternal_exists_exceptional_best`
  for four internal rows,
  `ArkLibExamples.ReedSolomon.CurveMigration.ProveKit.goldilocksWitness_exists_exceptional_best`
  for four lookup-witness rows, and
  `ArkLibExamples.ReedSolomon.CurveMigration.ProveKit.goldilocksBlind_exists_exceptional_best` for
  the remaining blinding row.
* `ArkLibExamples.ReedSolomon.CurveMigration.ZisK.exists_exceptional_best` covers all eight
  compressed-final-STARK curves.
* `ArkLibExamples.ReedSolomon.CurveMigration.LambdaVM.exists_exceptional_best` covers all nine
  LambdaVM CPU curves.

## Budget, query, and payload capstones

These theorems separate inputs from deductions. Curve dimensions, field sizes, proof-system
schedules, measured compressed sizes, and fitted compression ratios are explicit constants or
protocol assumptions. Lean proves the exceptional-set inequalities, query arithmetic, interval
bounds, and byte identities that follow from them. A phase-local certificate does not by itself
claim security for a deployed transcript, and an expected payload calculation is not a serializer
or a fresh measurement.

* ProveKit schedule witnesses are
  `ArkLibExamples.ReedSolomon.ProveKit.passportOuterWitness_budget`,
  `ArkLibExamples.ReedSolomon.ProveKit.passportInternalZk_budget`,
  `ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupWitness_budget`, and
  `ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupBlind_budget`. The analytical alternatives
  are `ArkLibExamples.ReedSolomon.ProveKit.passportOuterAnalytical_budget` and
  `ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupAnalytical_budget`. The current payload
  conclusions are `ArkLibExamples.ReedSolomon.ProveKit.passportExpectedSaving_interval`,
  `ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupExpectedSaving_interval`,
  `ArkLibExamples.ReedSolomon.ProveKit.passportAnalyticalExpectedSaving_interval`, and
  `ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupAnalyticalExpectedSaving_interval`, all in
  `ArkLibExamples.ReedSolomon.ProveKit`. The budgets certify the stated phase allocations from the
  supplied schedule and field assumptions. The payload theorems prove exact rational expectation
  intervals from the checked tree model and supplied measurement inputs; they do not measure a
  deployment or combine unrelated protocol phases.
  `ScheduleBudget` covers per-round and adjacent-transition obligations only. For the separate
  Passport phases, see `ProveKit.Passport.outer_localBudgets` and
  `ProveKit.Passport.internal_localBudgets`; their docstrings identify the companion checks.
  For Goldilocks, also read `goldilocksLookupBlindTail_transition`,
  `goldilocksLookupBlindTail_query`, `goldilocksLookupBlindTail_ood`, and
  `goldilocksLookupBlindTail_identity` in `ProveKit/Budgets.lean`.
  No theorem unions these phase bounds into whole-transcript security.
* `ArkLibExamples.ReedSolomon.ZisK.exists_nested_exceptional` composes the powers challenges fixed
  by the stated final-STARK profile; it is a local algebraic error certificate, not an end-to-end
  soundness theorem.
  `ArkLibExamples.ReedSolomon.ZisK.queries_at_target` proves the 51-query target and
  `ArkLibExamples.ReedSolomon.ZisK.proof_size` proves the 11,760-byte reduction.
* `ArkLibExamples.ReedSolomon.LambdaVM.CPU.exists_certified_cpu_budget` combines the nine curve
  sets, the complete candidate list, the early-anchor collision bound, and the 208-query local
  error.
  `ArkLibExamples.ReedSolomon.LambdaVM.CPU.proof_size` proves the 55,992-byte nominal reduction,
  while `ArkLibExamples.ReedSolomon.LambdaVM.CPU.expectedNetSaving_bounds` places the
  deduplicated expected saving strictly between 55,617 and 55,618 bytes. The trace dimensions,
  query schedule, and payload model are inputs; Lean proves the combined local bound and the
  resulting arithmetic, not whole-VM or whole-proof-system security.

## Optional companion and regression examples

The three declarations `ReedSolomon.weightedJohnsonTable_rate_one_sixteenth`,
`ReedSolomon.weightedJohnsonTable_rate_one_fourth`, and
`ReedSolomon.weightedJohnsonTable_rate_one_half` certify the finite
weighted Johnson rows retained in the quantitative companion. They are optional examples, not rows
of the current main paper.

`ArkLibExamples.ReedSolomon.AppendixCurveMCA` retains two 512-word BN254 curve certificates at gaps
`11/50` and `439/2000`. Their exact parameters do not occur in the current paper sources; treat them
as artifact and regression certificates rather than current-paper application rows.

These modules prove concrete mathematical certificates and explicit schedule or payload identities.
They do not formalize complete deployed transcripts, serializers, or an integrated implementation
of the paper's fast decoder.
-/
