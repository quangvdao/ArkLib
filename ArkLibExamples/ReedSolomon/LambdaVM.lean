/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# LambdaVM equality-table arithmetic

The equality-table configuration at revision `8064a8ef` has 32768 trace rows,
65536 evaluation positions, and 219 queries. The proposed agreement threshold
45910 permits 212 queries at the displayed query-error target with 20 grinding bits.

These are arithmetic facts about supplied parameters, not a proof of MCA, a
field construction, or security of LambdaVM. The finite interpolation and curve
certificates must separately justify this agreement threshold. The payload model
counts separately serialized field elements and hashes, excluding archive framing.
-/
namespace ArkLibExamples.ReedSolomon.LambdaVM

/-- Number of evaluations in the rate-one-half equality-table code. -/
def length : ℕ := 65536

/-- Degree bound before the DEEP quotient is undone. -/
def dimension : ℕ := 32768

/-- Agreement count used by the proposed finite certificate. -/
def agreement : ℕ := 45910

/-- Number of queries in the pinned implementation. -/
def originalQueries : ℕ := 219

/-- Number of queries in the proposed replacement. -/
def replacementQueries : ℕ := 212

/-- The proposed agreement is strictly below the finite Johnson threshold. -/
theorem agreement_beyond_johnson : agreement ^ 2 < length * (dimension - 1) := by
  norm_num [agreement, length, dimension]

/-- Cross-multiplied form of `2⁻²⁰ (A/n)^212 ≤ 2⁻¹²⁸`.
Only the query term is asserted here; algebraic errors are separate. -/
theorem query_error_at_target :
    2 ^ 108 * agreement ^ replacementQueries ≤ length ^ replacementQueries := by
  norm_num [agreement, replacementQueries, length]

/-- The proposed query count is strictly smaller than the implemented count. -/
theorem queries_reduced : replacementQueries < originalQueries := by
  norm_num [replacementQueries, originalQueries]

/-- Exact cardinality of the cubic Goldilocks challenge field, supplied as a parameter. -/
def challengeCardinality : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- Sum of the supplied powers and folding exceptional-count upper bounds. -/
def suppliedExceptionalCount : ℕ := 7259570157652382599

/-- The supplied constraint-cancellation numerator is seven times the original-tuple list bound. -/
def suppliedConstraintCount : ℕ := 10043264819

/-- The supplied OOD numerator includes the residual and excluded-domain counts. -/
def suppliedOODCount : ℕ := 188055829610496

/-- The complete displayed local error expression fits below `2⁻¹²⁸`.
This checks the supplied numerical counts; it does not prove they bound the corresponding
bad events. Those mathematical certificate obligations are separate. -/
theorem supplied_local_error_at_target :
    ((suppliedExceptionalCount + suppliedConstraintCount : ℕ) : ℚ) / challengeCardinality +
      (1 / 2 ^ 20 : ℚ) * ((agreement : ℚ) / length) ^ replacementQueries +
      (suppliedOODCount : ℚ) / (challengeCardinality - length - dimension : ℕ) <
      (1 / 2 ^ 128 : ℚ) := by
  norm_num [suppliedExceptionalCount, suppliedConstraintCount, suppliedOODCount,
    challengeCardinality, agreement, length, dimension, replacementQueries]

/-- With the same supplied algebraic counts, 211 queries exceed the displayed local budget. -/
theorem supplied_local_error_fewer_queries :
    (1 / 2 ^ 128 : ℚ) <
      ((suppliedExceptionalCount + suppliedConstraintCount : ℕ) : ℚ) / challengeCardinality +
        (1 / 2 ^ 20 : ℚ) * ((agreement : ℚ) / length) ^ (replacementQueries - 1) +
        (suppliedOODCount : ℚ) / (challengeCardinality - length - dimension : ℕ) := by
  norm_num [suppliedExceptionalCount, suppliedConstraintCount, suppliedOODCount,
    challengeCardinality, agreement, length, dimension, replacementQueries]

/-- Bytes of field elements and hashes in each separately encoded query response. -/
def bytesPerQuery : ℕ :=
  2 * 12 * 8 + 2 * 3 * 24 + 2 * 2 * 24 + 3 * 15 * 32 +
    (14 + 13 + 12 + 11 + 10 + 9 + 8) * 32 + 7 * 24

/-- The response model consists of 4504 field/hash bytes per query. -/
theorem bytesPerQuery_eq : bytesPerQuery = 4504 := by
  norm_num [bytesPerQuery]

/-- Any unchanged payload cancels: the proposed response count removes 31528 bytes. -/
theorem payload_reduction (unchanged : ℕ) :
    unchanged + originalQueries * bytesPerQuery =
      unchanged + replacementQueries * bytesPerQuery + 31528 := by
  change unchanged + 986376 = unchanged + 954848 + 31528
  omega

end ArkLibExamples.ReedSolomon.LambdaVM
