/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.Cover

/-!
# Rate-cover rounding and boundary tests

These concrete checks distinguish ceiling, predecessor, and truncated-endpoint conventions.
-/

open ReedSolomon.RateCover

/-- A boundary canary: for gap `1/2`, zero selects the first quarter endpoint and the top feasible
rate selects the second, truncated endpoint.  This detects off-by-one errors in `binIndex`. -/
example :
    binCount (1 / 2 : ℝ) = 2 ∧
      binIndex (1 / 2 : ℝ) 0 = 0 ∧
      endpoint (1 / 2 : ℝ) 0 = 1 / 4 ∧
      binIndex (1 / 2 : ℝ) (1 / 2) = 1 ∧
      endpoint (1 / 2 : ℝ) 1 = 1 / 2 := by
  norm_num [binCount, binIndex, endpoint, halfGap]

/-- Nonintegral and single-bin boundary canaries for the ceiling and truncation conventions. -/
example :
    binCount (3 / 10 : ℝ) = 5 ∧
      endpoint (3 / 10 : ℝ) 0 = 3 / 20 ∧
      endpoint (3 / 10 : ℝ) 4 = 7 / 10 ∧
      binCount (4 / 5 : ℝ) = 1 ∧
      endpoint (4 / 5 : ℝ) 0 = 1 / 5 := by
  norm_num [binCount, endpoint, halfGap, Nat.ceil_eq_iff]

/-- At a nonintegral bin boundary, the source and requested integer thresholds agree exactly. -/
example :
    Nat.ceil
        (localAgreement (3 / 10 : ℝ)
          (endpoint (3 / 10 : ℝ) (binIndex (3 / 10 : ℝ) ((2 : ℝ) / 3))) * 3) = 3 ∧
      2 + Nat.ceil ((3 / 10 : ℝ) * 3) = 3 := by
  have hIndex : Nat.ceil ((((2 : ℝ) / 3) / ((3 / 10 : ℝ) / 2))) = 5 := by
    norm_num [Nat.ceil_eq_iff]
  have hThreshold : Nat.ceil ((9 : ℝ) / 10) = 1 := by
    norm_num [Nat.ceil_eq_iff]
  rw [show binIndex (3 / 10 : ℝ) ((2 : ℝ) / 3) = 4 by
    rw [binIndex, halfGap, hIndex]
    norm_num]
  rw [show endpoint (3 / 10 : ℝ) 4 = 7 / 10 by
    norm_num [endpoint, halfGap]]
  rw [show localAgreement (3 / 10 : ℝ) (7 / 10) = 17 / 20 by
    norm_num [localAgreement, halfGap]]
  norm_num [hThreshold, Nat.ceil_eq_iff]
