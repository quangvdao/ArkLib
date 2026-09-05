/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# LambdaVM equality-table parameter arithmetic

This module checks the largest equality-table row in `lambda-beyond.json`, derived from LambdaVM
revision `8064a8efee4bd3edc9f064337d4e1d8bad54ae1a`. The table has 32768 trace rows. Blowup two
gives a Reed--Solomon block length `n = 65536` and message dimension `k = 32768`. The proposed
agreement threshold `A = 45910` permits 212 queries in place of the implementation's 219, while
retaining its 20 query-grinding bits.

The initial powers certificate uses multiplicity `m = 22`, first-derivative cap `M = 6`, total
jet-degree cap `mu = 30`, and powers degree 17. Eight binary-fold certificates use the same support
parameters and batching degree one, ending at a domain of size 256. The original-tuple list bound
uses message dimension `k + 1 = 32769`, as required when undoing the DEEP quotient.

## Reading the statements

The complete local error bound is

```text
(E + 7 * Lambda) / q
  + 2^-20 * (A / n)^t
  + (2 * n * Lambda + 2 * n) / (q - n - k) < 2^-128.
```

Here `E` is the sum of the initial powers-certificate count and eight binary-fold counts;
`Lambda = 1434752117` is the supplied list bound for the original tuple; `q` is the cubic
Goldilocks field cardinality; and `t = 212`. The theorem at 211 queries reverses the final strict
inequality while holding every supplied algebraic count fixed.

The response-size formula counts field elements and Merkle hashes serialized separately for each
query. It gives 4504 bytes per response, so removing seven responses removes 31528 bytes. Archive
descriptors and any enclosing proof framing are outside this model.

All error-budget statements are closed propositions about this fixed table. Only
`payload_reduction` quantifies a value, representing the outer payload left unchanged.

## Proof route and scope

The proof first evaluates the supplied count formulas and then normalizes the resulting rational
inequalities. It establishes the local equality-table budget conditional on the shared LogUp
prefix. The supplied counts still require their interpolation and polynomial-curve derivations,
and the VM wrapper needs a verifier-enforced per-table parameter policy. These statements therefore
do not constitute an end-to-end LambdaVM security theorem.
-/

namespace ArkLibExamples.ReedSolomon.LambdaVM

/-! ## Fixed code and query parameters -/

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

/-- The proposed agreement is below the finite Johnson agreement threshold, so its decoding
radius is beyond Johnson. -/
theorem agreement_beyond_johnson : agreement ^ 2 < length * (dimension - 1) := by
  norm_num [agreement, length, dimension]

/-- Cross-multiplied form of `2^-20 * (A / n)^212 ≤ 2^-128`. Only the query term is
asserted here; the complete local error is evaluated below. -/
theorem query_error_at_target :
    2 ^ 108 * agreement ^ replacementQueries ≤ length ^ replacementQueries := by
  norm_num [agreement, replacementQueries, length]

/-- The proposed query count is strictly smaller than the implemented count. -/
theorem queries_reduced : replacementQueries < originalQueries := by
  norm_num [replacementQueries, originalQueries]

/-! ## Supplied algebraic counts -/

/-- Exact cardinality of the cubic Goldilocks challenge field, supplied as a parameter. -/
def challengeCardinality : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- Sum of the supplied powers count and eight binary-fold exceptional-count bounds, from domain
sizes 65536 down through 256. -/
def suppliedExceptionalCount : ℕ :=
  7121894453107095641 + 104153502459085303 + 25452398473245907 +
    6227432721928317 + 1431419079833979 + 332364147255836 +
    63717950128569 + 13042232149662 + 1827481659385

/-- Supplied list bound for the original tuple, whose message dimension is `dimension + 1`. -/
def suppliedOriginalTupleListBound : ℕ := 1434752117

/-- Constraint-cancellation numerator: seven transition constraints per list candidate. -/
def suppliedConstraintCount : ℕ := 7 * suppliedOriginalTupleListBound

/-- Out-of-domain numerator: one degree-`2 * n` residual per candidate, plus `2 * n` excluded
points. -/
def suppliedOODCount : ℕ :=
  suppliedOriginalTupleListBound * (2 * length) + 2 * length

/-- The expanded certificate values give the three numerators used in the local error bound. -/
theorem supplied_counts_eq :
    suppliedExceptionalCount = 7259570157652382599 ∧
      suppliedConstraintCount = 10043264819 ∧
      suppliedOODCount = 188055829610496 := by
  norm_num [suppliedExceptionalCount, suppliedConstraintCount,
    suppliedOriginalTupleListBound, suppliedOODCount, length]

/-! ## Combined local error -/

/-- The complete displayed local error expression fits below `2^-128`. -/
theorem supplied_local_error_at_target :
    ((suppliedExceptionalCount + suppliedConstraintCount : ℕ) : ℚ) / challengeCardinality +
      (1 / 2 ^ 20 : ℚ) * ((agreement : ℚ) / length) ^ replacementQueries +
      (suppliedOODCount : ℚ) / (challengeCardinality - length - dimension : ℕ) <
      (1 / 2 ^ 128 : ℚ) := by
  norm_num [suppliedExceptionalCount, suppliedConstraintCount, suppliedOODCount,
    suppliedOriginalTupleListBound, challengeCardinality, agreement, length, dimension,
    replacementQueries]

/-- With the same supplied algebraic counts, 211 queries exceed the displayed local budget. -/
theorem supplied_local_error_fewer_queries :
    (1 / 2 ^ 128 : ℚ) <
      ((suppliedExceptionalCount + suppliedConstraintCount : ℕ) : ℚ) / challengeCardinality +
        (1 / 2 ^ 20 : ℚ) * ((agreement : ℚ) / length) ^ (replacementQueries - 1) +
        (suppliedOODCount : ℚ) / (challengeCardinality - length - dimension : ℕ) := by
  norm_num [suppliedExceptionalCount, suppliedConstraintCount, suppliedOODCount,
    suppliedOriginalTupleListBound, challengeCardinality, agreement, length, dimension,
    replacementQueries]

/-! ## Response payload -/

/-- Bytes of field elements and hashes in each separately encoded query response. -/
def bytesPerQuery : ℕ :=
  2 * 12 * 8 + 2 * 3 * 24 + 2 * 2 * 24 + 3 * 15 * 32 +
    (14 + 13 + 12 + 11 + 10 + 9 + 8) * 32 + 7 * 24

/-- The response model consists of 4504 field and hash bytes per query. -/
theorem bytesPerQuery_eq : bytesPerQuery = 4504 := by
  norm_num [bytesPerQuery]

/-- For any unchanged outer payload, the proposed response count removes exactly 31528 modeled
bytes. -/
theorem payload_reduction (unchanged : ℕ) :
    unchanged + originalQueries * bytesPerQuery =
      unchanged + replacementQueries * bytesPerQuery + 31528 := by
  change unchanged + 986376 = unchanged + 954848 + 31528
  omega

end ArkLibExamples.ReedSolomon.LambdaVM
