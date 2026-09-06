/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Uniform endpoint comparison for the weighted support

The dimension-to-rank ratio contains a scalar factor depending on the rate. In the high-rate
regime, both its rational and exponential factors decrease toward the upper rate endpoint.
At that endpoint each factor dominates its zero-gap value, so differentiation is unnecessary.
The low-rate regime has a larger uniform bound. Together they produce `16 exp(3/2)`; the exact
rational estimates then yield the surplus and challenge-height constant used by capacity.
-/

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The rational prefactor decreases throughout the high-rate interval. -/
theorem endpoint_prefactor_antitone (δ ρ σ : ℝ)
    (hδ : 0 < δ) (hρ : δ ≤ ρ) (hρσ : ρ ≤ σ) :
    σ / (σ + 3 * δ / 8) ^ 2 ≤ ρ / (ρ + 3 * δ / 8) ^ 2 := by
  have hρp : 0 < ρ := hδ.trans_le hρ
  have hσp : 0 < σ := hρp.trans_le hρσ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul hρ (hρ.trans hρσ) hδ.le hρp.le
  have hp : 0 ≤ ρ * σ - (3 * δ / 8) ^ 2 := by nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hρσ) hp
  nlinarith

/-- The rational prefactor and exponential factor both decrease with the rate. -/
theorem endpoint_antitone (δ ρ σ : ℝ)
    (hδ : 0 < δ) (hρ : δ ≤ ρ) (hρσ : ρ ≤ σ) :
    16 * σ / (σ + 3 * δ / 8) ^ 2 * Real.exp ((3 / 2) / (σ + 3 * δ / 8)) ≤
      16 * ρ / (ρ + 3 * δ / 8) ^ 2 * Real.exp ((3 / 2) / (ρ + 3 * δ / 8)) := by
  have hρp : 0 < ρ := hδ.trans_le hρ
  have hσp : 0 < σ := hρp.trans_le hρσ
  have hp := endpoint_prefactor_antitone δ ρ σ hδ hρ hρσ
  have he : Real.exp ((3 / 2) / (σ + 3 * δ / 8)) ≤
      Real.exp ((3 / 2) / (ρ + 3 * δ / 8)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16))
    he (Real.exp_pos _).le (by positivity)
  simpa only [mul_div_assoc] using h

/-- At the upper-rate endpoint, each factor already dominates its value at zero gap. -/
theorem endpoint_upper (δ : ℝ) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1 / 4) :
    16 * Real.exp (3 / 2) ≤
      16 * (1 - δ) / (1 - 5 * δ / 8) ^ 2 * Real.exp ((3 / 2) / (1 - 5 * δ / 8)) := by
  have hden : 0 < 1 - 5 * δ / 8 := by linarith
  have hp : (1 : ℝ) ≤ (1 - δ) / (1 - 5 * δ / 8) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδmax)]
  have he : Real.exp (3 / 2) ≤ Real.exp ((3 / 2) / (1 - 5 * δ / 8)) := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16))
    he (Real.exp_pos _).le (by positivity)
  simpa only [mul_one, mul_div_assoc] using h

/-- The high-rate endpoint expression is uniformly at least `16 exp(3/2)`. -/
theorem endpoint_lower (δ ρ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ) :
    16 * Real.exp (3 / 2) ≤
      16 * ρ / (ρ + 3 * δ / 8) ^ 2 * Real.exp ((3 / 2) / (ρ + 3 * δ / 8)) := by
  have h := endpoint_antitone δ ρ (1 - δ) hδ hρ hρmax
  have heq : 1 - δ + 3 * δ / 8 = 1 - 5 * δ / 8 := by ring
  rw [heq] at h
  exact (endpoint_upper δ hδ.le hδmax).trans h

/-- A finite positive exponential sum proves the strict lower numerical constant. -/
theorem endpoint_exp_lower : (112 / 25 : ℝ) < Real.exp (3 / 2) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 9
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A finite exponential sum with its tail bound proves the upper rank constant. -/
theorem endpoint_exp_upper : Real.exp (61 / 100) < (37 / 20 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (61 / 100 : ℝ) ≤ 1) (by norm_num : 0 < (4 : ℕ))
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The low-rate endpoint has strict room above the common high-rate bound. -/
theorem low_rate_endpoint_constant :
    16 * Real.exp (3 / 2) < (64 / 3) / (11 / 8 : ℝ) ^ 2 * Real.exp (48 / 11) := by
  have h := Real.add_one_le_exp (63 / 22 : ℝ)
  have hgain : (1 : ℝ) < (256 / 363) * Real.exp (63 / 22) := by linarith
  have hscale := mul_lt_mul_of_pos_left hgain (by positivity : 0 < 16 * Real.exp (3 / 2))
  rw [show (48 / 11 : ℝ) = 3 / 2 + 63 / 22 by norm_num, Real.exp_add]
  nlinarith only [hscale]

/-- The moment, endpoint, and rank constants give exactly the advertised surplus. -/
theorem exact_surplus_identity :
    ((2494723 / 10240000 : ℝ) * 16 * (112 / 25)) / (173 / 10) = 17463061 / 17300000 := by
  norm_num

/-- The reciprocal surplus gap gives the strict challenge-height ratio below `107`. -/
theorem surplus_challenge_ratio_lt :
    1 / ((17463061 / 17300000 : ℝ) - 1) < 107 := by norm_num


/-- Harmonic and logarithmic lower bounds imply the endpoint comparison at high rates. -/
theorem high_rate_scalar_lower (δ ρ H ell : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : 4 / δ ≤ H) (hell : 4 / δ ≤ ell) :
    16 * Real.exp (3 / 2) ≤
      ρ * (δ / ρ) ^ 2 * H ^ 2 / (1 + 3 * (δ / ρ) / 8) ^ 2 *
        Real.exp (ell * ((3 * (δ / ρ) / 8) / (1 + 3 * (δ / ρ) / 8))) := by
  have hρp : 0 < ρ := hδ.trans_le hρ
  have hH0 : 0 < H := (by positivity : 0 < 4 / δ).trans_le hH
  have ha : 0 < 1 + 3 * (δ / ρ) / 8 := by positivity
  have hp : 16 * ρ / (ρ + 3 * δ / 8) ^ 2 ≤ ρ * (δ / ρ) ^ 2 * H ^ 2 / (1 + 3 * (δ / ρ) / 8) ^ 2 := by
    calc
      _ = ρ * (δ / ρ) ^ 2 * (4 / δ) ^ 2 / (1 + 3 * (δ / ρ) / 8) ^ 2 := by field_simp; ring
      _ ≤ _ := by gcongr
  have he : (3 / 2) / (ρ + 3 * δ / 8) ≤ ell * ((3 * (δ / ρ) / 8) / (1 + 3 * (δ / ρ) / 8)) := by
    calc
      _ = (4 / δ) * ((3 * (δ / ρ) / 8) / (1 + 3 * (δ / ρ) / 8)) := by field_simp; ring
      _ ≤ _ := by gcongr
  exact (endpoint_lower δ ρ hδ hδmax hρ hρmax).trans
    (mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity))

/-- At low rates, the lower rate bound and the small-gap condition suffice. -/
theorem low_rate_scalar_lower (δ ρ H ell : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ)
    (hH : 4 / δ ≤ H) (hell : 4 / δ ≤ ell) :
    16 * Real.exp (3 / 2) < ρ * H ^ 2 / (11 / 8) ^ 2 * Real.exp (ell * (3 / 11)) := by
  have hρp : 0 < ρ := (by positivity : 0 < δ / 3).trans_le hρ
  have hH0 : 0 < H := (by positivity : 0 < 4 / δ).trans_le hH
  have hH2 : (4 / δ) ^ 2 ≤ H ^ 2 := by gcongr
  have hsize : (64 / 3 : ℝ) ≤ ρ * H ^ 2 := by
    calc
      (64 / 3 : ℝ) ≤ 16 / (3 * δ) := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith
      _ = (δ / 3) * (4 / δ) ^ 2 := by field_simp; ring
      _ ≤ ρ * H ^ 2 := mul_le_mul hρ hH2 (by positivity) hρp.le
  have hell16 : 16 ≤ ell := by
    have h := (div_le_iff₀ hδ).mp hell
    nlinarith
  apply low_rate_endpoint_constant.trans_le
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right hsize (by positivity)
  · apply Real.exp_le_exp.mpr
    linarith
  · exact (Real.exp_pos _).le
  · positivity

/-- The clipped rate parameter gives one uniform scalar comparison at every allowed rate. -/
theorem all_rate_scalar_lower (δ ρ H ell : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : 4 / δ ≤ H) (hell : 4 / δ ≤ ell) :
    let g := min 1 (δ / ρ)
    let a := 1 + 3 * g / 8
    16 * Real.exp (3 / 2) ≤ ρ * g ^ 2 * H ^ 2 / a ^ 2 * Real.exp (ell * ((3 * g / 8) / a)) := by
  dsimp only
  have hρp : 0 < ρ := (by positivity : 0 < δ / 3).trans_le hρ
  by_cases hhigh : δ ≤ ρ
  · rw [min_eq_right ((div_le_one hρp).mpr hhigh)]
    exact high_rate_scalar_lower δ ρ H ell hδ hδmax hhigh hρmax hH hell
  · rw [min_eq_left ((one_le_div hρp).mpr (le_of_not_ge hhigh))]
    have hlow := (low_rate_scalar_lower δ ρ H ell hδ hδmax hρ hH hell).le
    norm_num at hlow ⊢
    exact hlow

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
