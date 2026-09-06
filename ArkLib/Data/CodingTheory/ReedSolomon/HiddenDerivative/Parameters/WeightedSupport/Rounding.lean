/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RankRounding

/-!
# Rounding the lower-cutoff weighted support

The lower cutoff uses `27g/50`. Together with the interpolation budget `m(1+g)`, this
leaves an error-coordinate window of width at most `1.541gm`, including both rounding
operations. The radius estimates are shared with every support using the same rounded
multiplicity and weighted radius.
-/

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The exact lower-cutoff window, with both floor and ceiling errors included. -/
theorem errorWindow_le (g : ℝ) (m : ℕ) (hg : 0 ≤ g) (hgmax : g ≤ 1)
    (hgm : 2000 ≤ g * m) :
    (Nat.ceil ((m : ℝ) * (1 + g) - Nat.floor ((1 - 27 * g / 50) * m)) : ℝ) ≤
      (1541 / 1000) * g * m := by
  have h := InterpolationRounding.errorWindow_lt (27 / 50) g m hg (by positivity) (by nlinarith)
  have he : (27 / 50 : ℝ) * g = 27 * g / 50 := by ring
  rw [he] at h
  nlinarith


end ReedSolomon.HiddenDerivative.WeightedSupportParameters
