/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Scalar prerequisites for the revised capacity parameters

The order is the ceiling of `exp(4/δ)`. Its logarithm and harmonic sum retain the same lower
bound, while its size makes the finite moment estimates applicable. The clipped gap
`min 1 (δ/ρ)` then controls the normalized simplex radius uniformly across both rate ranges.
-/

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The revised exponential order supplies the finite dimension and harmonic lower bounds. -/
theorem prescribed_order_lower (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    let d := Nat.ceil (Real.exp (4 / δ))
    10000 ≤ d ∧ 4 / δ ≤ Real.log d ∧
      4 / δ ≤ (harmonic (d - 1) : ℝ) := by
  let d := Nat.ceil (Real.exp (4 / δ))
  have hceil : Real.exp (4 / δ) ≤ (d : ℝ) := Nat.le_ceil _
  have hdp : (0 : ℝ) < d := (Real.exp_pos _).trans_le hceil
  have hlog := Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.log_exp] at hlog
  have he : (16 : ℝ) ≤ 4 / δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hexp := Real.exp_le_exp.mpr he
  have hnum : (10000 : ℝ) < Real.exp 16 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hd : 10000 ≤ d := by exact_mod_cast (hnum.trans_le (hexp.trans hceil)).le
  have hh := log_add_one_le_harmonic (d - 1)
  have heq : d - 1 + 1 = d := by omega
  rw [heq] at hh
  exact ⟨hd, hlog, hlog.trans hh⟩


/-- The normalized gap and harmonic radius satisfy the quarter-scale inequality at every rate. -/
theorem gap_harmonic_lower (δ ρ H : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) (hH : 4 / δ ≤ H) :
    let g := min 1 (δ / ρ)
    4 * (1 + 3 * g / 8) ≤ g * H := by
  have hδH := (div_le_iff₀ hδ).mp hH
  by_cases hlow : ρ ≤ δ
  · rw [min_eq_left ((le_div_iff₀ hρ).mpr (by simpa using hlow))]
    have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hH
    have h16 : 16 ≤ H := by nlinarith
    norm_num
    linarith
  · have hhigh : δ < ρ := lt_of_not_ge hlow
    rw [min_eq_right ((div_le_one hρ).mpr hhigh.le)]
    apply (mul_le_mul_iff_left₀ hρ).mp
    have he : ρ * (δ / ρ * H) = δ * H := by field_simp
    have he' : ρ * (4 * (1 + 3 * (δ / ρ) / 8)) = 4 * ρ + 3 * δ / 2 := by
      field_simp
      ring
    nlinarith [he, he']

/-- The harmonic square is small enough for the finite centered-moment estimates. -/
theorem harmonic_square_bound (d H : ℝ) (hd : 10000 ≤ d) (hH0 : 0 ≤ H)
    (hH : H ≤ Real.log d + 3 / 5) : H ^ 2 ≤ d / 100 := by
  have h := hH.trans (Real.log_add_three_fifths_le_sqrt_div_ten d hd)
  have hs := Real.sq_sqrt (show 0 ≤ d by linarith)
  nlinarith [Real.sqrt_nonneg d]

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
