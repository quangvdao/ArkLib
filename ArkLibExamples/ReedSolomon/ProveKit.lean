/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Tactic.NormNum

/-!
# ProveKit WHIR parameter arithmetic

This module checks two proposed local replacements for the pinned ProveKit WHIR Standard witness
profile at revision `8804e80e8e890d01bb585f2bd5e5b564ac0fd80d`. Both rows have Reed--Solomon
block length `n = 2^20`, message dimension `k = 2^18`, interleaving width eight, batch size one,
and vector size `2^21`. The BN254 row selects agreement `492831 / 1048576` and 109 queries. The
cubic Goldilocks row selects agreement `512754 / 1048576`, 115 queries, and a second initial
out-of-domain sample.

The BN254 certificate supplies `E = 1126820196482631879700641773` and
`L = 147000408479737`. The cubic Goldilocks certificate supplies `E = 8210316778177167673` and
`L = 5089296970`.

## Reading the statements

For a row with field cardinality `q`, agreement numerator `A`, exceptional-count bound `E`, list
bound `L`, and query count `t`, the five changed error slots are

```text
choose(L, 2) * ((vectorSize - 1) / q)^initialOodSamples,
E / q,
2 * L / q,
(E + 2 * L) / q,
2 * (1 + t) * 160 / q.
```

`*_changed_slots_meet_target` states that each term is at most `2^-128`, using cross-multiplied
natural-number inequalities. `*_query_selection` checks the existing proof-of-work acceptance
probability `(powThreshold + 1) / 2^64` times `(A / n)^t`; it also shows that one fewer query
exceeds the same query-only target.

The payload theorem uses the conservative lower bound
`(oldQueries - t) * (rowBytes - 32) - extraOodBytes`. Here `rowBytes` is eight field elements, 32
bytes bounds the possible authentication-path increase when one query is removed, and
`extraOodBytes` charges the second cubic-Goldilocks sample. The nominal comparison uses 127
queries; the auxiliary zero-slack comparison uses 119.

Every theorem is a closed proposition about one of the two fixed rows; no received word, code, or
field instance is quantified.

## Proof route and scope

The two `Profile` values expose the parameters specific to each row, and `norm_num` verifies the
resulting closed inequalities. The exceptional and list counts are supplied by
`modular-whir-beyond-johnson.json`. Establishing them from ArkLib's interpolation, root-counting,
and polynomial-curve results remains a separate mathematical bridge. Thus these theorems certify
the local numerical calculation and modeled raw payload, not a complete WHIR coding-soundness
theorem or a measured serialized proof size.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

/-! ## Parameter rows -/

/-- A pinned row of the ProveKit WHIR parameter calculation. -/
structure Profile where
  /-- Reed--Solomon block length. -/
  n : Nat
  /-- Reed--Solomon dimension. -/
  k : Nat
  /-- Length of the interleaved vector tested by the initial out-of-domain check. -/
  vectorSize : Nat
  /-- Number of field elements in one queried row. -/
  interleavingWidth : Nat
  /-- Number of polynomials batched in this calculation. -/
  batchSize : Nat
  /-- Cardinality of the challenge field. -/
  fieldSize : Nat
  /-- Numerator of the agreement fraction, whose denominator is `n`. -/
  agreementNumerator : Nat
  /-- Multiplicity parameter in the concrete list-decoding certificate. -/
  multiplicity : Nat
  /-- First-derivative exponent cap in the concrete list-decoding certificate. -/
  firstJetCap : Nat
  /-- Total jet-degree cap in the concrete list-decoding certificate. -/
  totalJetDegreeCap : Nat
  /-- Upper bound for the exceptional challenge count. -/
  exceptionalCount : Nat
  /-- Upper bound for the decoded list size. -/
  listSize : Nat
  /-- Selected number of uniform queries. -/
  queries : Nat
  /-- Number of initial out-of-domain samples. -/
  initialOodSamples : Nat
  /-- Inclusive 64-bit proof-of-work acceptance threshold. -/
  powThreshold : Nat
  /-- Query count in the pinned nominal ProveKit profile. -/
  nominalQueries : Nat
  /-- Auxiliary zero-slack query reference used by the source checker. -/
  zeroSlackQueryReference : Nat
  /-- Encoded bytes per base-field element. -/
  fieldBytes : Nat
  /-- Encoded bytes per extension-field element. -/
  extensionBytes : Nat

/-- The pinned BN254 parameter row. -/
def bn254 : Profile where
  n := 1048576
  k := 262144
  vectorSize := 2097152
  interleavingWidth := 8
  batchSize := 1
  fieldSize := 21888242871839275222246405745257275088548364400416034343698204186575808495617
  agreementNumerator := 492831
  multiplicity := 384
  firstJetCap := 168
  totalJetDegreeCap := 688
  exceptionalCount := 1126820196482631879700641773
  listSize := 147000408479737
  queries := 109
  initialOodSamples := 1
  powThreshold := 18786624067678312
  nominalQueries := 127
  zeroSlackQueryReference := 119
  fieldBytes := 32
  extensionBytes := 32

/-- The pinned cubic Goldilocks parameter row. -/
def goldilocksCubic : Profile where
  n := 1048576
  k := 262144
  vectorSize := 2097152
  interleavingWidth := 8
  batchSize := 1
  fieldSize := 6277101731002175853884774869567645561244584131361410908161
  agreementNumerator := 512754
  multiplicity := 13
  firstJetCap := 5
  totalJetDegreeCap := 24
  exceptionalCount := 8210316778177167673
  listSize := 5089296970
  queries := 115
  initialOodSamples := 2
  powThreshold := 18786624067678312
  nominalQueries := 127
  zeroSlackQueryReference := 119
  fieldBytes := 8
  extensionBytes := 24

/-! ## BN254 checks -/

/-- The BN254 row has rate one quarter and the expected interleaved vector size. Its agreement is
below the finite Johnson agreement threshold, so its decoding radius is beyond Johnson. -/
theorem bn254_code_arithmetic :
    bn254.k * 4 = bn254.n ∧
      bn254.interleavingWidth * bn254.k = bn254.vectorSize ∧
      bn254.agreementNumerator ^ 2 < bn254.n * (bn254.k - 1) := by
  norm_num [bn254]

/-- Every changed BN254 error slot is at most `2^-128`, expressed without rational division. -/
theorem bn254_changed_slots_meet_target :
    bn254.listSize * (bn254.listSize - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
        2 * bn254.fieldSize ∧
      bn254.exceptionalCount * 2 ^ 128 ≤ bn254.fieldSize ∧
      2 * bn254.listSize * 2 ^ 128 ≤ bn254.fieldSize ∧
      (bn254.exceptionalCount + 2 * bn254.listSize) * 2 ^ 128 ≤ bn254.fieldSize ∧
      2 * (1 + bn254.queries) * 160 * 2 ^ 128 ≤ bn254.fieldSize := by
  norm_num [bn254]

/-- The BN254 query contribution meets `2^-128` at 109 queries and exceeds it at 108. -/
theorem bn254_query_selection :
    (bn254.powThreshold + 1) * bn254.agreementNumerator ^ bn254.queries * 2 ^ 128 ≤
        2 ^ 64 * bn254.n ^ bn254.queries ∧
      2 ^ 64 * bn254.n ^ (bn254.queries - 1) <
        (bn254.powThreshold + 1) *
          bn254.agreementNumerator ^ (bn254.queries - 1) * 2 ^ 128 := by
  norm_num [bn254]

/-- The checker's conservative BN254 raw-payload lower bounds are 4032 bytes against the nominal
profile and 2240 bytes against its auxiliary zero-slack reference. -/
theorem bn254_payload_lower_bounds :
    (bn254.nominalQueries - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 4032 ∧
      (bn254.zeroSlackQueryReference - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 2240 := by
  norm_num [bn254]

/-! ## Cubic Goldilocks checks -/

/-- The cubic Goldilocks row has rate one quarter and the expected interleaved vector size. Its
agreement is below the finite Johnson agreement threshold, so its decoding radius is beyond
Johnson. -/
theorem goldilocksCubic_code_arithmetic :
    goldilocksCubic.k * 4 = goldilocksCubic.n ∧
      goldilocksCubic.interleavingWidth * goldilocksCubic.k = goldilocksCubic.vectorSize ∧
      goldilocksCubic.agreementNumerator ^ 2 <
        goldilocksCubic.n * (goldilocksCubic.k - 1) := by
  norm_num [goldilocksCubic]

/-- Every changed cubic Goldilocks error slot is at most `2^-128`, expressed without rational
division. The initial out-of-domain term includes both extension-field samples. -/
theorem goldilocksCubic_changed_slots_meet_target :
    goldilocksCubic.listSize * (goldilocksCubic.listSize - 1) *
          (goldilocksCubic.vectorSize - 1) ^ 2 * 2 ^ 128 ≤
        2 * goldilocksCubic.fieldSize ^ 2 ∧
      goldilocksCubic.exceptionalCount * 2 ^ 128 ≤ goldilocksCubic.fieldSize ∧
      2 * goldilocksCubic.listSize * 2 ^ 128 ≤ goldilocksCubic.fieldSize ∧
      (goldilocksCubic.exceptionalCount + 2 * goldilocksCubic.listSize) * 2 ^ 128 ≤
        goldilocksCubic.fieldSize ∧
      2 * (1 + goldilocksCubic.queries) * 160 * 2 ^ 128 ≤ goldilocksCubic.fieldSize := by
  norm_num [goldilocksCubic]

/-- The cubic Goldilocks query contribution meets `2^-128` at 115 queries and exceeds it at 114. -/
theorem goldilocksCubic_query_selection :
    (goldilocksCubic.powThreshold + 1) *
          goldilocksCubic.agreementNumerator ^ goldilocksCubic.queries * 2 ^ 128 ≤
        2 ^ 64 * goldilocksCubic.n ^ goldilocksCubic.queries ∧
      2 ^ 64 * goldilocksCubic.n ^ (goldilocksCubic.queries - 1) <
        (goldilocksCubic.powThreshold + 1) *
          goldilocksCubic.agreementNumerator ^ (goldilocksCubic.queries - 1) * 2 ^ 128 := by
  norm_num [goldilocksCubic]

/-- The checker's conservative cubic Goldilocks raw-payload lower bounds are 360 bytes against the
nominal profile and 104 bytes against its auxiliary zero-slack reference. -/
theorem goldilocksCubic_payload_lower_bounds :
    (goldilocksCubic.nominalQueries - goldilocksCubic.queries) *
          (goldilocksCubic.interleavingWidth * goldilocksCubic.fieldBytes - 32) -
        (goldilocksCubic.initialOodSamples - 1) * goldilocksCubic.extensionBytes = 360 ∧
      (goldilocksCubic.zeroSlackQueryReference - goldilocksCubic.queries) *
          (goldilocksCubic.interleavingWidth * goldilocksCubic.fieldBytes - 32) -
        (goldilocksCubic.initialOodSamples - 1) * goldilocksCubic.extensionBytes = 104 := by
  norm_num [goldilocksCubic]

end ArkLibExamples.ReedSolomon.ProveKit
