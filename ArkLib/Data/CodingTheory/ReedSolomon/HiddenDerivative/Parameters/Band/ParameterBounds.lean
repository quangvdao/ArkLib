/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RankRounding
import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds


/-!
# Rounding bounds for asymmetric-band parameters

These elementary estimates retain the floor and ceiling errors in the parameter choice of
[DKTZ26].
No estimate on the cardinality of the band is used here.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26]
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

/-- The two rounding operations cost less than two in the error-coordinate window. -/
theorem band_errorWindow_lt (g : ℝ) (m : ℕ) (hg : 0 ≤ g) (hg' : g ≤ 1) :
    (Nat.ceil ((m : ℝ) * (1 + g) -
      Nat.floor ((1 - g / 10) * m)) : ℝ) < 11 / 10 * g * m + 2 := by
  have h := InterpolationRounding.errorWindow_lt (1 / 10) g m hg
    (by positivity) (by nlinarith)
  convert h using 1 <;> ring_nf

/-- The paper's `9/8` window constant requires only `80 ≤ g m`. -/
theorem band_errorWindow_le (g : ℝ) (m : ℕ) (hg : 0 ≤ g) (hg' : g ≤ 1)
    (hgm : 80 ≤ g * m) :
    (Nat.ceil ((m : ℝ) * (1 + g) -
      Nat.floor ((1 - g / 10) * m)) : ℝ) ≤ 9 / 8 * g * m := by
  have := band_errorWindow_lt g m hg hg'
  nlinarith

/-- The ambient-degree expression used by the actual local rank has the same window. -/
theorem band_errorWindow_degree_le (g : ℝ) (m D : ℕ) (hD : 0 < D)
    (hg : 0 ≤ g) (hg' : g ≤ 1) (hgm : 80 ≤ g * m) :
    (Nat.ceil ((m : ℝ) * D * (1 + g) / D -
      Nat.floor ((1 - g / 10) * m)) : ℝ) ≤ 9 / 8 * g * m := by
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have heq : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by
    field_simp
  rw [heq]
  exact band_errorWindow_le g m hg hg' hgm

/-- The paper's rounded choices satisfy all scalar κ prerequisites for the rank estimate. -/
theorem band_prescribed_kappa_bounds (g H : ℝ) (d : ℕ)
    (hg : 0 ≤ g) (hH : 0 < H) (hd : 1000 ≤ d) :
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let κ := ((d - 1 : ℕ) : ℝ) * m / W
    0 < m ∧ 0 < W ∧ 0 < κ ∧
      999 / 1000 * (H / a) ≤ κ ∧ κ ≤ H / a ∧
      κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100 ∧
      (d : ℝ) * κ / m ≤ 1 / 1000 ∧
      1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤ 101 / 100 * (1 / (H / a) ^ 2) := by
  exact InterpolationRounding.prescribed_kappa_bounds (1 + g / 2) H d (by linarith) hH hd

/-- A rational Taylor bound verifies the exponential constant without numerical evaluation. -/
theorem band_exp_error_lt : Real.exp (61 / 100) < 19 / 10 := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (61 / 100 : ℝ) ≤ 1) (by norm_num : 0 < (4 : ℕ))
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The final rational constant has strict room below `15/2`. -/
theorem band_rank_constant_lt :
    (9 / 8 : ℝ) * (100 / 29) * (101 / 100) * (19 / 10) < 15 / 2 := by
  norm_num

end ReedSolomon.HiddenDerivative
