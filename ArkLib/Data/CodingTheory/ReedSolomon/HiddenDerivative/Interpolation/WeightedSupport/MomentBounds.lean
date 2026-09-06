/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite estimates for the centered simplex moments

Once simplex integration supplies the moment identities, their estimates are elementary real
inequalities. This module isolates that arithmetic from integration: the variance uses a lower
bound on the second harmonic sum, and the third and fourth moments use upper harmonic bounds.
The identities themselves are separate obligations; these lemmas do not assume a probability
model or claim to construct one.
-/

namespace ReedSolomon.HiddenDerivative

/-- The normalized variance is strictly larger than `3/2` at every allowed dimension. -/
theorem weightedSupport_variance_factor_gt {d H H₂ : ℝ}
    (hd : 10000 ≤ d) (hH : H ^ 2 ≤ d / 100) (h₂ : 38 / 25 ≤ H₂) :
    (3 / 2 : ℝ) < d / (d + 1) * (H₂ - H ^ 2 / d) := by
  have hd0 : 0 < d := by linarith
  have hden : 0 < d + 1 := by linarith
  have hid : d / (d + 1) * (H₂ - H ^ 2 / d) =
      (d * H₂ - H ^ 2) / (d + 1) := by field_simp
  rw [hid, lt_div_iff₀ hden]
  nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr h₂)]

/-- The third centered moment numerator is nonnegative under the finite harmonic bounds. -/
theorem weightedSupport_third_moment_numerator_nonneg {d H H₂ H₃ : ℝ}
    (hd : 0 ≤ d) (hH0 : 0 ≤ H) (hH : H ≤ d / 10)
    (h₂ : H₂ ≤ 5 / 3) (h₃ : 1 ≤ H₃) :
    0 ≤ d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3 := by
  have hprod : H * H₂ ≤ (d / 10) * (5 / 3) :=
    (mul_le_mul_of_nonneg_left h₂ hH0).trans
      (mul_le_mul_of_nonneg_right hH (by norm_num))
  have hlow := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr h₃)
  have hhigh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3 * d by positivity)
  have hcube : 0 ≤ H ^ 3 := by positivity
  nlinarith

/-- In the fourth centered moment, the terms involving the first harmonic sum have
nonpositive total contribution. The remaining two terms have the stated uniform bound. -/
theorem weightedSupport_fourth_moment_factor_le {d H H₂ H₃ H₄ : ℝ}
    (hd : 6 ≤ d) (hH0 : 0 ≤ H) (h₂0 : 0 ≤ H₂) (h₃0 : 0 ≤ H₃)
    (hH : H ^ 2 ≤ (d - 1) * H₂)
    (h₂ : H₂ ≤ 329 / 200) (h₄ : H₄ ≤ 13 / 12) :
    (3 * d ^ 3 * H₂ ^ 2 + 6 * d ^ 3 * H₄ - 24 * d ^ 2 * H * H₃ -
        6 * d * (d - 6) * H ^ 2 * H₂ + 3 * (d - 6) * H ^ 4) /
      ((d + 1) * (d + 2) * (d + 3)) ≤ 584723 / 40000 := by
  have hd0 : 0 ≤ d := by linarith
  have hden : 0 < (d + 1) * (d + 2) * (d + 3) := by positivity
  have hH' : H ^ 2 ≤ 2 * d * H₂ := by
    nlinarith [mul_nonneg hd0 h₂0]
  have htail := mul_nonneg
    (show 0 ≤ 3 * (d - 6) * H ^ 2 by positivity)
    (sub_nonneg.mpr hH')
  have hnegative : 0 ≤ 24 * d ^ 2 * H * H₃ := by positivity
  have hsquare : H₂ ^ 2 ≤ (329 / 200 : ℝ) ^ 2 := by nlinarith
  have hmain : 3 * H₂ ^ 2 + 6 * H₄ ≤ 584723 / 40000 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmain
    (show 0 ≤ d ^ 3 by positivity)
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg d]

end ReedSolomon.HiddenDerivative
