/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.NormNum

/-!
# ZisK Poseidon configuration arithmetic

Exact numerical checks for the Poseidon2 fixture in the ZisK proof backend at
revision `0f3fef8c`. The counts are supplied certificate outputs: this module
checks their arithmetic consequences, not the interpolation or curve theorems
needed to establish those counts. Two batching-grinding bits are a proposed
protocol change, not a hook claimed to exist in the pinned implementation.
The per-phase target below is not a bound on the sum of protocol errors.
-/
namespace ArkLibExamples.ReedSolomon.ZisK

/-- Cardinality parameter of the cubic Goldilocks challenge field. -/
def challengeCardinality : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- Supplied exceptional-count bound for powers batching of the 182 words. -/
def suppliedBatchingCount : ℕ := 60881724329658740667

/-- The selected agreement is beyond the finite Johnson threshold. -/
theorem agreement_beyond_johnson : (260512 : ℕ) ^ 2 < 524288 * (131072 - 1) := by
  norm_num

/-- Two batching-grinding bits suffice for the supplied algebraic count at 128 bits. -/
theorem supplied_batching_at_target :
    2 ^ 128 * suppliedBatchingCount ≤ 4 * challengeCardinality := by
  norm_num [suppliedBatchingCount, challengeCardinality]

/-- The supplied batching count does not fit the same target without additional grinding. -/
theorem supplied_batching_without_grinding_fails :
    challengeCardinality < 2 ^ 128 * suppliedBatchingCount := by
  norm_num [suppliedBatchingCount, challengeCardinality]

/-- Cross-multiplied query inequality with the existing 16 query-grinding bits. -/
theorem query_at_target : (2 : ℕ) ^ 112 * 260512 ^ 111 ≤ 524288 ^ 111 := by
  norm_num

/-- One fewer query fails that same query-only budget. -/
theorem fewer_queries_fail : (524288 : ℕ) ^ 110 < 2 ^ 112 * 260512 ^ 110 := by
  norm_num

/-- Supplied exceptional count for folding stage 1 meets 128 bits without grinding. -/
theorem supplied_fold_1_at_target :
    (2 : ℕ) ^ 128 * 36668433835251914 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- Supplied exceptional count for folding stage 2 meets 128 bits without grinding. -/
theorem supplied_fold_2_at_target :
    (2 : ℕ) ^ 128 * 554102788624746 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- Supplied exceptional count for folding stage 3 meets 128 bits without grinding. -/
theorem supplied_fold_3_at_target :
    (2 : ℕ) ^ 128 * 7211277004693 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- Supplied exceptional count for folding stage 4 meets 128 bits without grinding. -/
theorem supplied_fold_4_at_target :
    (2 : ℕ) ^ 128 * 43704620659 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- Supplied exceptional count for folding stage 5 meets 128 bits without grinding. -/
theorem supplied_fold_5_at_target :
    (2 : ℕ) ^ 128 * 477333081 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- The size calculator assigns 8784 bytes to each removed query. An additional
8-byte nonce leaves a net saving of 26344 bytes, with all other payload fixed. -/
theorem payload_reduction (unchanged : ℕ) :
    unchanged + 114 * 8784 = unchanged + 111 * 8784 + 8 + 26344 := by
  omega

end ArkLibExamples.ReedSolomon.ZisK
