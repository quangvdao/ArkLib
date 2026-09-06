/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.FiniteFieldBudget
import ArkLibExamples.ReedSolomon.ConcreteCurveBounds
import ArkLibExamples.ReedSolomon.ProveKitExpectedPayload
import ArkLibExamples.ReedSolomon.ZisK

/-!
# Acceptance checks for the shared finite-field budget engine

These checks exercise the generic predicates and pin the revised cubic-Goldilocks specialization.
-/

namespace ArkLibTest.FiniteFieldBudget

open ArkLib.FiniteFieldBudget
open ArkLibExamples.ReedSolomon

example : QueryMeetsTarget 4 0 1 2 1 1 := by norm_num [QueryMeetsTarget]

example : QueryFailsTarget 1 0 2 1 1 1 := by norm_num [QueryFailsTarget]

example : RepeatedOodMeetsTarget 2 2 4 2 1 := by norm_num [RepeatedOodMeetsTarget]

example : conservativePayloadSaving 127 113 64 32 24 = 424 := by decide

example :
    QueryMeetsTarget (2 ^ 64) ProveKit.goldilocksCubic113.powThreshold
      ProveKit.goldilocksCubic113.agreementNumerator ProveKit.goldilocksCubic113.n 113 128 :=
  ProveKit.goldilocksCubic113_query_selection.1

example :
    QueryFailsTarget (2 ^ 64) ProveKit.goldilocksCubic113.powThreshold
      ProveKit.goldilocksCubic113.agreementNumerator ProveKit.goldilocksCubic113.n 112 128 := by
  simpa [ProveKit.goldilocksCubic113] using ProveKit.goldilocksCubic113_query_selection.2

example :
    ReedSolomon.HiddenDerivative.TaylorExponentSufficient 1 262144 524285 :=
  ConcreteCurveBounds.proveKitGoldilocksCubic_taylorExponent_sufficient 1

example :
    (569315 : ℚ) / 100 <
      expectedPayloadSaving (2 ^ 20) 20 127 113 64 32 24 ∧
    expectedPayloadSaving (2 ^ 20) 20 127 113 64 32 24 < (569317 : ℚ) / 100 :=
  ProveKit.goldilocksCubic_expected_payload_saving

example : GroundCountMeetsTarget ZisK.suppliedBatchingCount ZisK.challengeCardinality 1 128 :=
  ZisK.supplied_batching_at_target

example :
    ReedSolomon.HiddenDerivative.TaylorExponentSufficient 1 131072 262141 :=
  ConcreteCurveBounds.zisKRevisedInitial_taylorExponent_sufficient 1

example :
    ReedSolomon.HiddenDerivative.firstOrderCurveBound 524288 131072 131072 136608 260512
        17 3 181 22707 262141
          (ReedSolomon.HiddenDerivative.firstOrderCurveDirectRatio 524288 131072 260512) ≤
      ZisK.suppliedBatchingCount := by
  simpa [ConcreteCurveBounds.zisKRevisedInitialSplit,
    ConcreteCurveBounds.zisKRevisedInitialHeight, ZisK.suppliedBatchingCount] using
      ConcreteCurveBounds.zisKRevisedInitial_envelope_le

end ArkLibTest.FiniteFieldBudget
