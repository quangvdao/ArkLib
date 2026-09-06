/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A quartic lower bound for the weighted support count

The cubic amount of remaining degree is retained only above the lower cutoff. A quartic
minorant converts this discontinuous contribution into four polynomial moments. Its two
outer factors give the right sign outside the retained interval; completing a square
proves the comparison inside it.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- Cubic remaining degree after imposing the normalized lower cutoff. -/
def weightedSupportContribution (z : ℝ) : ℝ :=
  if -(181 / 200 : ℝ) ≤ z then (max (5 / 8 - z) 0) ^ 3 else 0

/-- Quartic minorant whose expectation depends only on the first four moments. -/
def weightedSupportQuartic (z : ℝ) : ℝ :=
  (1969 / 1000 : ℝ) * (5 / 8 - z) ^ 2 *
    (5 / 8 - z - 11 / 40) * (153 / 100 - (5 / 8 - z))

/-- Completing the square gives a strictly positive gap in the inner quadratic comparison. -/
theorem weightedSupport_quadratic_gap_pos (y : ℝ) :
    0 < y - (1969 / 1000 : ℝ) * (y - 11 / 40) * (153 / 100 - y) := by
  have hid : y - (1969 / 1000 : ℝ) * (y - 11 / 40) * (153 / 100 - y) =
      (1969 / 1000 : ℝ) * (y - 510809 / 787600) ^ 2 +
        71180039 / 315040000000 := by ring
  rw [hid]
  positivity

/-- The quartic never exceeds the retained cubic contribution, including both cut boundaries. -/
theorem weightedSupportQuartic_le_contribution (z : ℝ) :
    weightedSupportQuartic z ≤ weightedSupportContribution z := by
  let y : ℝ := 5 / 8 - z
  have hq : weightedSupportQuartic z =
      (1969 / 1000 : ℝ) * y ^ 2 * (y - 11 / 40) * (153 / 100 - y) := rfl
  rw [hq]
  by_cases hlo : y ≤ 11 / 40
  · have hnonpos : (1969 / 1000 : ℝ) * y ^ 2 *
        (y - 11 / 40) * (153 / 100 - y) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      · linarith
    apply hnonpos.trans
    unfold weightedSupportContribution
    split_ifs <;> positivity
  · by_cases hhi : 153 / 100 ≤ y
    · have hnonpos : (1969 / 1000 : ℝ) * y ^ 2 *
          (y - 11 / 40) * (153 / 100 - y) ≤ 0 := by
        have hfactor : 0 ≤ y - 11 / 40 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      apply hnonpos.trans
      unfold weightedSupportContribution
      split_ifs <;> positivity
    · have hy : 0 ≤ y := by linarith
      have hz : -(181 / 200 : ℝ) ≤ z := by dsimp [y] at hhi; linarith
      have hgap := mul_nonneg (sq_nonneg y) (weightedSupport_quadratic_gap_pos y).le
      rw [weightedSupportContribution, if_pos hz, max_eq_left hy]
      change (1969 / 1000 : ℝ) * y ^ 2 * (y - 11 / 40) * (153 / 100 - y) ≤ y ^ 3
      nlinarith

/-- Expanding around the mean exposes the four moment coefficients. -/
theorem weightedSupportQuartic_eq (z : ℝ) :
    weightedSupportQuartic z = (1969 / 1000 : ℝ) *
      (1267 / 10240 + (4959 / 8000) * z ^ 2 +
        (139 / 200) * z ^ 3 - z ^ 4 - (7843 / 12800) * z) := by
  unfold weightedSupportQuartic
  ring

/-- The second through fourth moment bounds leave a nonnegative correction to the constant
term. The small scale `s ≤ 1/4` is decisive: it absorbs the negative fourth moment. -/
theorem weightedSupport_moment_correction_nonneg {s v₂ v₃ v₄ : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1 / 4)
    (hv₂ : (3 / 2 : ℝ) * s ^ 2 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₄ : v₄ ≤ (584723 / 40000 : ℝ) * s ^ 4) :
    0 ≤ (4959 / 8000 : ℝ) * v₂ + (139 / 200) * v₃ - v₄ := by
  have hs₂ : s ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hs₄ : s ^ 4 ≤ s ^ 2 / 16 := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs₂)]
  nlinarith [sq_nonneg s]

/-- After centering eliminates the linear moment, the quartic contribution has the exact
constant lower bound used by weighted dimension counting. -/
theorem weightedSupport_quartic_moment_lower_bound {s v₂ v₃ v₄ : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1 / 4)
    (hv₂ : (3 / 2 : ℝ) * s ^ 2 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₄ : v₄ ≤ (584723 / 40000 : ℝ) * s ^ 4) :
    (2494723 / 10240000 : ℝ) ≤ (1969 / 1000 : ℝ) *
      (1267 / 10240 + (4959 / 8000) * v₂ + (139 / 200) * v₃ - v₄) := by
  have h := weightedSupport_moment_correction_nonneg hs hsmax hv₂ hv₃ hv₄
  linarith

end
end ReedSolomon.HiddenDerivative
