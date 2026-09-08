/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.InterpolationSpecializationBudget

/-! Regression checks for the numerical specialization budget, including zero X degree,
the smallest permitted coordinate budgets, and a nontrivial curve multiplier. -/

open Polynomial.SymbolicInterpolation

example : (3 + 1 : ℝ) ≤ 2 * 1 * 1 * 3 ^ 2 * 3 := by
  exact coefficient_cost_le_curve_leading_term 3 1 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (2 * 3 * 3 * (3 + 3) : ℝ) ≤ 2 * 1 * 3 * 3 ^ 2 * 3 := by
  exact specialization_cost_le_curve_leading_term 3 3 3 3 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Zero X degree does not require a positive codeword degree hypothesis.
example (a z : ℝ) (ha : 0 ≤ a) (ha_cap : a ≤ 3) (hz_cap : z ≤ 3) :
    2 * a * 0 * (z + 3) ≤ 2 * 1 * 0 * 3 ^ 2 * 3 := by
  exact specialization_cost_le_curve_leading_term a 0 z 0 3 3 1
    ha (by norm_num) ha_cap (by norm_num) (by simpa using hz_cap)
    (by norm_num) (by norm_num) (by norm_num)

-- m = 3, reduced-rate square root 1/2, curve degree 2; actual integer caps are 6, 6, 32.
example (a x z : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x)
    (ha_cap : a ≤ 6) (hx_cap : x ≤ 6) (hz_cap : z ≤ 32) :
    2 * a * x * (z + 3) ≤ (67312 / 3 : ℝ) := by
  have h := specialization_cost_le_curve_interpolation_bound
    3 (1 / 2) 1 4 (1 / 4) 2 a x z
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ha hx
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  norm_num at h
  exact h
