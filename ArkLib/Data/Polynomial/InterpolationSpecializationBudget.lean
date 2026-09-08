/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationParameters
import Mathlib.Tactic.GCongr

/-!
# Specialization costs within interpolation budgets

The coarse simultaneous-center cost from the public universal-numerator formalization fits
inside the leading term of the printed BCHKS exception bound. This is a numerical lemma:
it neither constructs an obstruction polynomial nor asserts that an inseparable resultant is
nonzero. Its callers must supply actual degree caps, rather than rounding strict caps upward.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Sections 3.1 and 4.3.

The cost being compared is from Jieyi Long's simultaneous primitive-specialization construction,
building on Remco Bloemen's BCHKS formalization. The symbolic comparison below is new:
https://github.com/proximity-prize/proximity-prize/blob/19bc7d3e21b2261257e1961acd720b2c395d87e1/ProximityPrize/SubmissionLower/BCHKSUniversalPrimitiveX0Avoidance6399.lean
-/

namespace Polynomial.SymbolicInterpolation

/-- The coefficient-selection cost also fits in the leading curve-exception term when
the X-degree budget is at least one. This pays a field-size gate, not an existence proof. -/
theorem coefficient_cost_le_curve_leading_term
    (z dx dy dz ell : ℝ) (hz : z ≤ ell * dz) (hdx : 1 ≤ dx)
    (hdy : 3 ≤ dy) (hdz : 3 ≤ dz) (hell : 1 ≤ ell) :
    z + 1 ≤ 2 * ell * dx * dy ^ 2 * dz := by
  have hdz0 : 0 ≤ dz := by linarith
  have hell0 : 0 ≤ ell := by linarith
  have hunit : 1 ≤ ell * dz := by
    calc
      1 ≤ 1 * 3 := by norm_num
      _ ≤ ell * dz := by gcongr
  have hmass : 2 ≤ 2 * dx * dy ^ 2 := by
    calc
      2 ≤ 2 * 1 * 3 ^ 2 := by norm_num
      _ ≤ 2 * dx * dy ^ 2 := by gcongr
  calc
    z + 1 ≤ ell * dz + ell * dz := add_le_add hz hunit
    _ = 2 * (ell * dz) := by ring
    _ ≤ (2 * dx * dy ^ 2) * (ell * dz) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg hell0 hdz0)
    _ = 2 * ell * dx * dy ^ 2 * dz := by ring

/-- The coarse aggregate specialization cost fits in the leading curve-exception term.
The parameter `a` is factor degree mass, whereas `ell` is the curve-degree multiplier. -/
theorem specialization_cost_le_curve_leading_term
    (a x z dx dy dz ell : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (ha_cap : a ≤ dy) (hx_cap : x ≤ dx) (hz_cap : z ≤ ell * dz)
    (hdy : 3 ≤ dy) (hdz : 3 ≤ dz) (hell : 1 ≤ ell) :
    2 * a * x * (z + 3) ≤ 2 * ell * dx * dy ^ 2 * dz := by
  have hdx : 0 ≤ dx := hx.trans hx_cap
  have hdy0 : 0 ≤ dy := by linarith
  have hdz0 : 0 ≤ dz := by linarith
  have hell0 : 0 ≤ ell := by linarith
  have hreserve : 3 ≤ ell * dz * (dy - 1) := by
    calc
      3 ≤ 1 * 3 * (3 - 1) := by norm_num
      _ ≤ ell * dz * (dy - 1) := by gcongr
  have hscale : ell * dz + 3 ≤ ell * dy * dz := by nlinarith [hreserve]
  calc
    2 * a * x * (z + 3) ≤ 2 * a * x * (ell * dz + 3) := by gcongr
    _ ≤ 2 * dy * dx * (ell * dz + 3) := by gcongr
    _ ≤ 2 * dy * dx * (ell * dy * dz) := by gcongr
    _ = 2 * ell * dx * dy ^ 2 * dz := by ring

/-- Actual coordinate-degree caps from the improved interpolant pay the simultaneous-center
cost using the printed exception bound. Here `r` is the square root of the reduced rate and
`k` is the paper's non-strict codeword degree bound. -/
theorem specialization_cost_le_curve_interpolation_bound
    (m r k n gamma ell a x z : ℝ) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hn : 0 ≤ n) (hgamma : 0 ≤ gamma) (hell : 1 ≤ ell)
    (ha : 0 ≤ a) (hx : 0 ≤ x)
    (ha_cap : a ≤ (m + 1 / 2) / r)
    (hx_cap : x ≤ k * ((m + 1 / 2) / r))
    (hz_cap : z ≤ ell * ((m + 1 / 2) ^ 2 / (3 * r ^ 2))) :
    2 * a * x * (z + 3) ≤
      ell * (2 * (k * ((m + 1 / 2) / r)) * ((m + 1 / 2) / r) ^ 2 *
        ((m + 1 / 2) ^ 2 / (3 * r ^ 2)) +
          (gamma * n + 1) * ((m + 1 / 2) / r)) := by
  have hdy : 3 ≤ (m + 1 / 2) / r := (le_div_iff₀ hr).mpr (by linarith)
  have hdz := hdy.trans (y_budget_le_coefficient_budget m r hm hr hr1)
  have hleading := specialization_cost_le_curve_leading_term a x z
    (k * ((m + 1 / 2) / r)) ((m + 1 / 2) / r)
    ((m + 1 / 2) ^ 2 / (3 * r ^ 2)) ell ha hx ha_cap hx_cap hz_cap hdy hdz hell
  have htail : 0 ≤ ell * ((gamma * n + 1) * ((m + 1 / 2) / r)) := by
    have hell0 : 0 ≤ ell := by linarith
    positivity
  nlinarith [hleading]

end Polynomial.SymbolicInterpolation
