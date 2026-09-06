/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.UniformQueryBoundary
import ArkLibExamples.ReedSolomon.ProveKit
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-!
# Expected ProveKit authentication payload

This module checks the analytical authentication-data calculation in Appendix D for the pinned
ProveKit WHIR rows.  For `t` independent uniform queries into a binary tree with `n = 2^height`
leaves, a level-`j` subtree has `2^j` leaves.  The generic finite-sample theorem proves that one
oriented subtree boundary contributes

```text
((n - 2^j)^t - (n - 2^(j+1))^t) / n^t
```

in expectation.  There are `n / 2^j` oriented subtrees at that level.  Summing these derived
terms gives `expectedAuthenticationHashes`.

## Reading the byte statements

`expectedPayloadSaving` adds the queried-row bytes removed when the query count falls, adds the
change in 32-byte authentication hashes, and subtracts any extra out-of-domain field elements.
The exact rational comparisons below pin the displayed decimals to a one-hundredth-byte interval
and prove their integer ceilings.  They concern raw field-element and hash payload in the pinned
analytical model; they do not describe outer framing, compression, or a deployed serializer.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open scoped BigOperators
open ArkLib.UniformQueryBoundary

set_option maxRecDepth 16384

/-- Expected number of authentication hashes in the binary sibling-boundary model. -/
def expectedAuthenticationHashes (n height queries : ℕ) : ℚ :=
  ∑ j ∈ Finset.range height,
    (n / 2 ^ j : ℕ) *
      ((((n - 2 ^ j : ℕ) : ℚ) / n) ^ queries -
        (((n - 2 ^ (j + 1) : ℕ) : ℚ) / n) ^ queries)

/-- Expected raw byte saving between two query counts in the pinned payload model. -/
def expectedPayloadSaving (n height oldQueries newQueries rowBytes hashBytes
    extraOodBytes : ℕ) : ℚ :=
  ((oldQueries - newQueries) * rowBytes : ℕ) +
    hashBytes *
      (expectedAuthenticationHashes n height oldQueries -
        expectedAuthenticationHashes n height newQueries) -
    extraOodBytes

/-- The generic finite-sample theorem justifies each level term from subtree cardinalities:
`b` oriented disjoint sibling pairs of size `s` have the displayed expectation. -/
theorem expected_level_authentication_hashes
    {alpha node : Type*} [Fintype alpha] [Fintype node] [DecidableEq alpha]
    {queries s b : ℕ} (subtree sibling : node → Finset alpha)
    (hnonempty : 0 < Fintype.card alpha) (hnodes : Fintype.card node = b)
    (hsubtree : ∀ v, (subtree v).card = s)
    (hsibling : ∀ v, (sibling v).card = s)
    (hdisjoint : ∀ v, Disjoint (subtree v) (sibling v)) :
    uniformQueryExpectation queries (authenticationHashCount subtree sibling) =
      (b : ℚ) * ((((Fintype.card alpha - s : ℕ) : ℚ) /
          Fintype.card alpha) ^ queries -
        (((Fintype.card alpha - 2 * s : ℕ) : ℚ) /
          Fintype.card alpha) ^ queries) := by
  exact uniformQueryExpectation_authenticationHashCount_of_uniformSize_probability
    subtree sibling hnonempty hnodes hsubtree hsibling hdisjoint

set_option maxHeartbeats 8000000 in
-- Exact normalization expands twenty rational terms with exponents 109 and 127.
/-- The original 109-query BN254 row saves between 10820.93 and 10820.94 expected raw bytes
against the pinned 127-query profile. -/
theorem bn254_expected_payload_saving_109 :
    (1082093 : ℚ) / 100 < expectedPayloadSaving (2 ^ 20) 20 127 109 256 32 0 ∧
      expectedPayloadSaving (2 ^ 20) 20 127 109 256 32 0 < (1082094 : ℚ) / 100 := by
  norm_num [expectedPayloadSaving, expectedAuthenticationHashes, Finset.sum_range_succ]

/-- The preceding exact interval fixes the integer byte ceiling at 10821. -/
theorem bn254_expected_payload_saving_109_ceil :
    ⌈expectedPayloadSaving (2 ^ 20) 20 127 109 256 32 0⌉ = 10821 := by
  apply Int.ceil_eq_iff.mpr
  obtain ⟨hlower, hupper⟩ := bn254_expected_payload_saving_109
  constructor <;> norm_num at hlower hupper ⊢ <;> linarith

set_option maxHeartbeats 8000000 in
-- Exact normalization expands twenty rational terms with adjacent 108/109 exponents.
/-- Moving from 109 to 108 BN254 queries saves between 604.99 and 605 expected raw bytes. -/
theorem bn254_expected_extra_payload_saving_108 :
    (60499 : ℚ) / 100 < expectedPayloadSaving (2 ^ 20) 20 109 108 256 32 0 ∧
      expectedPayloadSaving (2 ^ 20) 20 109 108 256 32 0 < 605 := by
  norm_num [expectedPayloadSaving, expectedAuthenticationHashes, Finset.sum_range_succ]

/-- The exact additional saving from the 108-query retuning has byte ceiling 605. -/
theorem bn254_expected_extra_payload_saving_108_ceil :
    ⌈expectedPayloadSaving (2 ^ 20) 20 109 108 256 32 0⌉ = 605 := by
  apply Int.ceil_eq_iff.mpr
  obtain ⟨hlower, hupper⟩ := bn254_expected_extra_payload_saving_108
  constructor <;> norm_num at hlower hupper ⊢ <;> linarith

set_option maxHeartbeats 8000000 in
-- Exact normalization expands twenty rational terms with exponents 115 and 127.
/-- The original cubic-Goldilocks row saves between 4871.73 and 4871.74 expected raw bytes after
charging its additional 24-byte extension-field out-of-domain value. -/
theorem goldilocksCubic_expected_payload_saving :
    (487173 : ℚ) / 100 < expectedPayloadSaving (2 ^ 20) 20 127 115 64 32 24 ∧
      expectedPayloadSaving (2 ^ 20) 20 127 115 64 32 24 < (487174 : ℚ) / 100 := by
  norm_num [expectedPayloadSaving, expectedAuthenticationHashes, Finset.sum_range_succ]

/-- The exact cubic-Goldilocks expected saving has byte ceiling 4872. -/
theorem goldilocksCubic_expected_payload_saving_ceil :
    ⌈expectedPayloadSaving (2 ^ 20) 20 127 115 64 32 24⌉ = 4872 := by
  apply Int.ceil_eq_iff.mpr
  obtain ⟨hlower, hupper⟩ := goldilocksCubic_expected_payload_saving
  constructor <;> norm_num at hlower hupper ⊢ <;> linarith

end ArkLibExamples.ReedSolomon.ProveKit
