/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.NormNum

/-!
# ZisK Poseidon2 parameter arithmetic

This module checks a proposed powers-batching profile for the Poseidon2 fixture in ZisK's pinned
FRI calculator at revision `0f3fef8cd1897df469532996e72e0c84ef69d6fb`. The Reed--Solomon
instance has block length `n = 524288`, message dimension `k = 131072`, and agreement threshold
`A = 260512`. It batches 182 words, uses 111 queries with the existing 16 query-grinding bits, and
adds two batching-grinding bits.

The initial powers certificate uses multiplicity `m = 9`, first-derivative cap `M = 3`, total
jet-degree cap `mu = 17`, and powers degree 181. The five folding certificates use the same support
parameters and batching degrees 7, 7, 7, 7, and 3.

## Reading the statements

The inequality `A^2 < n * (k - 1)` places the agreement below the finite Johnson agreement
threshold, and hence the decoding radius beyond Johnson. Each algebraic inequality has been
cross-multiplied against the per-phase target `2^-128`. For example, an exceptional-count bound
`E` over a field of cardinality `q` meets the target after two batching-grinding bits exactly when
`2^128 * E ≤ 4 * q`. The query theorem rewrites
`2^-16 * (A / n)^111 ≤ 2^-128` without rational division.

The five folding counts belong, in order, to output domains of sizes 65536, 8192, 1024, 128, and
32. Their inequalities use no grinding credit. The proof-size statement follows the pinned
calculator's model: each removed query contributes 8784 bytes, and the proposed batching nonce
costs eight bytes.

All error-budget statements are closed propositions about this fixed row. Only `payload_reduction`
quantifies a value, representing the part of the encoded payload unchanged by the replacement.

## Proof route and scope

Every theorem reduces a closed integer equality or inequality with `norm_num` or `omega`. The
exceptional counts are numerical inputs at this layer. `ConcreteCurveMCA` derives them from
interpolation and polynomial-curve geometry, and `ZisKCertifiedBudget` connects the constructed
exceptional sets to these slots over cubic Goldilocks. This module checks the parameter arithmetic.
The batching nonce also requires a prover/verifier
transcript hook that is absent from the pinned implementation.
-/

namespace ArkLibExamples.ReedSolomon.ZisK

/-! ## Fixed parameters -/

/-- Reed--Solomon block length of the Poseidon2 fixture. -/
def blockLength : ℕ := 524288

/-- Reed--Solomon message dimension of the Poseidon2 fixture. -/
def messageDimension : ℕ := 131072

/-- Agreement count used by the supplied powers certificate. -/
def agreement : ℕ := 260512

/-- Number of queries in the pinned calculator profile. -/
def originalQueries : ℕ := 114

/-- Number of queries in the proposed profile. -/
def replacementQueries : ℕ := 111

/-- Existing query-grinding budget, in bits. -/
def queryGrindingBits : ℕ := 16

/-- Proposed batching-grinding budget, in bits. -/
def batchingGrindingBits : ℕ := 2

/-- Cardinality of the cubic Goldilocks challenge field. -/
def challengeCardinality : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- Supplied exceptional-count bound for powers batching of 182 words. -/
def suppliedBatchingCount : ℕ := 60881724329658740667

/-! ## Agreement and error budgets -/

/-- The selected agreement is below the finite Johnson agreement threshold, so its decoding
radius is beyond Johnson. -/
theorem agreement_beyond_johnson :
    agreement ^ 2 < blockLength * (messageDimension - 1) := by
  norm_num [agreement, blockLength, messageDimension]

/-- Two batching-grinding bits suffice for the supplied algebraic count at 128 bits. -/
theorem supplied_batching_at_target :
    2 ^ 128 * suppliedBatchingCount ≤
      2 ^ batchingGrindingBits * challengeCardinality := by
  norm_num [suppliedBatchingCount, batchingGrindingBits, challengeCardinality]

/-- The supplied batching count does not fit the same target without additional grinding. -/
theorem supplied_batching_without_grinding_fails :
    challengeCardinality < 2 ^ 128 * suppliedBatchingCount := by
  norm_num [suppliedBatchingCount, challengeCardinality]

/-- The 111-query contribution meets `2^-128` with the existing 16 grinding bits. -/
theorem query_at_target :
    (2 : ℕ) ^ (128 - queryGrindingBits) * agreement ^ replacementQueries ≤
      blockLength ^ replacementQueries := by
  norm_num [queryGrindingBits, agreement, replacementQueries, blockLength]

/-- One fewer query fails that same query-only budget. -/
theorem fewer_queries_fail :
    blockLength ^ (replacementQueries - 1) <
      2 ^ (128 - queryGrindingBits) * agreement ^ (replacementQueries - 1) := by
  norm_num [blockLength, replacementQueries, queryGrindingBits, agreement]

/-- The supplied folding count on the output domain of size 65536 meets 128 bits. -/
theorem supplied_fold_1_at_target :
    (2 : ℕ) ^ 128 * 36668433835251914 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- The supplied folding count on the output domain of size 8192 meets 128 bits. -/
theorem supplied_fold_2_at_target :
    (2 : ℕ) ^ 128 * 554102788624746 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- The supplied folding count on the output domain of size 1024 meets 128 bits. -/
theorem supplied_fold_3_at_target :
    (2 : ℕ) ^ 128 * 7211277004693 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- The supplied folding count on the output domain of size 128 meets 128 bits. -/
theorem supplied_fold_4_at_target :
    (2 : ℕ) ^ 128 * 43704620659 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-- The supplied folding count on the output domain of size 32 meets 128 bits. -/
theorem supplied_fold_5_at_target :
    (2 : ℕ) ^ 128 * 477333081 ≤ challengeCardinality := by
  norm_num [challengeCardinality]

/-! ## Calculator payload -/

/-- The calculator assigns 8784 bytes to each query response. Removing three responses and adding
an eight-byte nonce leaves a net saving of 26344 modeled bytes, for any unchanged outer payload. -/
theorem payload_reduction (unchanged : ℕ) :
    unchanged + originalQueries * 8784 =
      unchanged + replacementQueries * 8784 + 8 + 26344 := by
  change unchanged + 1001376 = unchanged + 975024 + 8 + 26344
  omega

end ArkLibExamples.ReedSolomon.ZisK
