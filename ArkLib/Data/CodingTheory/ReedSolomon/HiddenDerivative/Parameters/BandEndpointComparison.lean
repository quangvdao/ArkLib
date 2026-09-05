/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandNormalizedRank
import Mathlib.NumberTheory.Harmonic.Bounds


/-!
# Endpoint scalar comparisons for the asymmetric band

Finite endpoint estimates for the optimized asymmetric-band parameter choice.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding up to Capacity at Every
Rate*][DKTZ26], source revision `9e4d6488ead94be47cca69e5be915b5667143b66`.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

/-- A rational partial exponential sum certifies the high-rate numerical margin. -/
theorem band_endpoint_exp_lower : (29 : ℝ) < Real.exp (169 / 50) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 169 / 50) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The high-rate endpoint margin exceeds the required scalar comparison. -/
theorem band_endpoint_constant_gt :
    (1215 : ℝ) < (169 / 25) ^ 2 * Real.exp (169 / 50) := by
  have := band_endpoint_exp_lower
  nlinarith

/-- The rational prefactor decreases throughout the high-rate interval. -/
theorem band_endpoint_prefactor_antitone (δ ρ σ : ℝ)
    (hδ : 0 < δ) (hρ : δ ≤ ρ) (hρσ : ρ ≤ σ) :
    σ / (2 * σ + δ) ^ 2 ≤ ρ / (2 * ρ + δ) ^ 2 := by
  have hρp : 0 < ρ := lt_of_lt_of_le hδ hρ
  have hσp : 0 < σ := lt_of_lt_of_le hρp hρσ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hprod : 0 ≤ 4 * ρ * σ - δ ^ 2 := by
    have hmul := mul_le_mul hρ (hρ.trans hρσ) hδ.le hρp.le
    nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hρσ) hprod
  nlinarith

/-- The endpoint function is antitone on the high-rate interval, without differentiation. -/
theorem band_endpoint_function_antitone (δ ρ σ x : ℝ)
    (hδ : 0 < δ) (hρ : δ ≤ ρ) (hρσ : ρ ≤ σ) (hx : 0 ≤ x) :
    4 * x ^ 2 * σ / (2 * σ + δ) ^ 2 * Real.exp (x / (2 * σ + δ)) ≤
      4 * x ^ 2 * ρ / (2 * ρ + δ) ^ 2 * Real.exp (x / (2 * ρ + δ)) := by
  have hρp : 0 < ρ := lt_of_lt_of_le hδ hρ
  have hσp : 0 < σ := lt_of_lt_of_le hρp hρσ
  have hp := band_endpoint_prefactor_antitone δ ρ σ hδ hρ hρσ
  have he : Real.exp (x / (2 * σ + δ)) ≤ Real.exp (x / (2 * ρ + δ)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hx (by positivity) (by linarith)
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * x ^ 2)) he
    (Real.exp_pos _).le (by positivity)
  simpa [mul_div_assoc] using h

/-- The exponential gain at the endpoint absorbs its rational prefactor loss. -/
theorem band_endpoint_at_upper (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    (169 / 25 : ℝ) ^ 2 * Real.exp (169 / 50) ≤
      4 * (169 / 25) ^ 2 * (1 - δ) / (2 - δ) ^ 2 *
        Real.exp ((169 / 25) / (2 - δ)) := by
  let t := δ / (2 - δ)
  have hden : 0 < 2 - δ := by linarith
  have ht : 0 ≤ t := div_nonneg hδ.le hden.le
  have ht' : t ≤ 1 / 7 := by
    dsimp [t]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hpref : 4 * (1 - δ) / (2 - δ) ^ 2 = 1 - t ^ 2 := by
    dsimp [t]
    field_simp
    ring
  have hexponent : (169 / 25 : ℝ) / (2 - δ) = 169 / 50 + 169 / 50 * t := by
    dsimp [t]
    field_simp
    ring
  have hlin := Real.add_one_le_exp (169 / 50 * t)
  have hpoly : 1 ≤ (1 - t ^ 2) * (1 + 169 / 50 * t) := by
    have ht2 : t ^ 2 ≤ 1 / 49 := by nlinarith
    have haux : 0 ≤ 169 / 50 * (1 - t ^ 2) - t := by nlinarith
    have := mul_nonneg ht haux
    nlinarith
  have hp : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hgain : 1 ≤ (1 - t ^ 2) * Real.exp (169 / 50 * t) := by
    have h := mul_le_mul_of_nonneg_left hlin hp
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hgain
    (by positivity : 0 ≤ (169 / 25 : ℝ) ^ 2 * Real.exp (169 / 50))
  rw [hexponent, Real.exp_add]
  have heq : 4 * (169 / 25 : ℝ) ^ 2 * (1 - δ) / (2 - δ) ^ 2 =
      (169 / 25) ^ 2 * (1 - t ^ 2) := by rw [← hpref]; ring
  rw [heq]
  nlinarith

/-- The high-rate endpoint function is uniformly greater than `1215`. -/
theorem band_endpoint_function_gt (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρ' : ρ ≤ 1 - δ) :
    (1215 : ℝ) < 4 * (169 / 25) ^ 2 * ρ / (2 * ρ + δ) ^ 2 *
      Real.exp ((169 / 25) / (2 * ρ + δ)) := by
  have h := band_endpoint_function_antitone δ ρ (1 - δ) (169 / 25)
    hδ hρ hρ' (by norm_num)
  have heq : 2 * (1 - δ) + δ = 2 - δ := by ring
  rw [heq] at h
  exact (band_endpoint_constant_gt.trans_le (band_endpoint_at_upper δ hδ hδ')).trans_le h

/-- The low-rate scalar comparison follows already from the high-rate exponential constant. -/
theorem band_low_rate_scalar_gt (δ ρ H ℓ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ)
    (hH : (169 / 25) / δ ≤ H) (hℓ : (169 / 25) / δ ≤ ℓ) :
    (1215 : ℝ) < Real.exp (ℓ / 3) * H ^ 2 * ρ / (3 / 2) ^ 2 := by
  have hHp : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hρp : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  have he : 4 ≤ ℓ / 3 := by
    have hl := (div_le_iff₀ hδ).mp hℓ
    have hlow : (169 / 25 : ℝ) / δ ≥ (169 / 25) * 4 := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith
    linarith
  have he' := Real.exp_le_exp.mpr he
  have hfactor : (4 * (169 / 25 : ℝ) ^ 2 / 27) / δ ≤ H ^ 2 * ρ / (3 / 2) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (169 / 25 : ℝ) / δ) hH 2
    have hmul := mul_le_mul hsq hρ (by positivity : 0 ≤ δ / 3) (sq_nonneg H)
    have hid : ((169 / 25 : ℝ) / δ) ^ 2 * (δ / 3) / (3 / 2) ^ 2 =
        (4 * (169 / 25 : ℝ) ^ 2 / 27) / δ := by field_simp; ring
    rw [← hid]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hfactor' : (16 * (169 / 25 : ℝ) ^ 2 / 27) ≤ H ^ 2 * ρ / (3 / 2) ^ 2 := by
    apply le_trans ?_ hfactor
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hbound := mul_le_mul he' hfactor' (by norm_num) (Real.exp_pos _).le
  have hnum : (1215 : ℝ) < Real.exp 4 * (16 * (169 / 25 : ℝ) ^ 2 / 27) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 10
    norm_num [Finset.sum_range_succ] at h
    nlinarith
  exact hnum.trans_le (by convert hbound using 1; ring)

/-- Lower harmonic and logarithmic estimates imply the high-rate scalar comparison. -/
theorem band_high_rate_scalar_gt (δ ρ H ℓ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρ' : ρ ≤ 1 - δ)
    (hH : (169 / 25) / δ ≤ H) (hℓ : (169 / 25) / δ ≤ ℓ) :
    (1215 : ℝ) < Real.exp (ℓ * (δ / ρ) / (2 + δ / ρ)) *
      H ^ 2 * ρ * (δ / ρ) ^ 2 / (1 + (δ / ρ) / 2) ^ 2 := by
  have hρp : 0 < ρ := lt_of_lt_of_le hδ hρ
  have hHp : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hden : 0 < 2 + δ / ρ := by positivity
  have he : (169 / 25 : ℝ) / (2 * ρ + δ) ≤ ℓ * (δ / ρ) / (2 + δ / ρ) := by
    have h := mul_le_mul_of_nonneg_right hℓ (by positivity : 0 ≤ δ / ρ)
    have h' := div_le_div_of_nonneg_right h hden.le
    have hid : ((169 / 25 : ℝ) / δ) * (δ / ρ) / (2 + δ / ρ) =
        (169 / 25) / (2 * ρ + δ) := by field_simp
    rwa [hid] at h'
  have he' := Real.exp_le_exp.mpr he
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (169 / 25 : ℝ) / δ) hH 2
  have hbound : Real.exp ((169 / 25) / (2 * ρ + δ)) *
      ((169 / 25 : ℝ) / δ) ^ 2 * ρ * (δ / ρ) ^ 2 / (1 + (δ / ρ) / 2) ^ 2 ≤
      Real.exp (ℓ * (δ / ρ) / (2 + δ / ρ)) *
        H ^ 2 * ρ * (δ / ρ) ^ 2 / (1 + (δ / ρ) / 2) ^ 2 := by
    gcongr
  have hid : Real.exp ((169 / 25) / (2 * ρ + δ)) *
      ((169 / 25 : ℝ) / δ) ^ 2 * ρ * (δ / ρ) ^ 2 / (1 + (δ / ρ) / 2) ^ 2 =
      4 * (169 / 25) ^ 2 * ρ / (2 * ρ + δ) ^ 2 *
        Real.exp ((169 / 25) / (2 * ρ + δ)) := by
    field_simp
    ring
  rw [hid] at hbound
  exact (band_endpoint_function_gt δ ρ hδ hδ' hρ hρ').trans_le hbound

/-- The prescribed rounded derivative order has the lower logarithmic and harmonic bounds. -/
theorem band_prescribed_order_lower (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    1000 ≤ d ∧ (169 / 25) / δ ≤ Real.log d ∧
      (169 / 25) / δ ≤ (harmonic (d - 1) : ℝ) := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  have hceil : Real.exp ((169 / 25) / δ) ≤ (d : ℝ) := Nat.le_ceil _
  have hdp : (0 : ℝ) < d := (Real.exp_pos _).trans_le hceil
  have hlog := Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.log_exp] at hlog
  have he : (7 : ℝ) ≤ (169 / 25) / δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hexp := Real.exp_le_exp.mpr he
  have hnum : (1000 : ℝ) < Real.exp 7 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7) 15
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hd : 1000 ≤ d := by exact_mod_cast (hnum.trans_le (hexp.trans hceil)).le
  have hh := log_add_one_le_harmonic (d - 1)
  have heq : d - 1 + 1 = d := by omega
  rw [heq] at hh
  exact ⟨hd, hlog, hlog.trans hh⟩

/-- The prescribed order satisfies the manuscript's scalar comparison in both rate regimes. -/
theorem band_prescribed_endpoint_gt (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := (harmonic (d - 1) : ℝ)
    let g := min 1 (δ / ρ)
    let a := 1 + g / 2
    (1215 : ℝ) < (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ρ * g ^ 2 / a ^ 2 := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  have hρp : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  obtain ⟨hd, hlog, hH⟩ := band_prescribed_order_lower δ hδ hδ'
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  dsimp only
  rw [Real.rpow_def_of_pos hdp]
  by_cases hhigh : δ ≤ ρ
  · have hg : min (1 : ℝ) (δ / ρ) = δ / ρ :=
      min_eq_right ((div_le_one hρp).mpr hhigh)
    rw [hg]
    have h := band_high_rate_scalar_gt δ ρ (harmonic (d - 1)) (Real.log d)
      hδ hδ' hhigh hρ' hH hlog
    dsimp [d] at h ⊢
    convert h using 1; ring_nf
  · have hg : min (1 : ℝ) (δ / ρ) = 1 :=
      min_eq_left ((one_le_div hρp).mpr (by linarith))
    rw [hg]
    have h := band_low_rate_scalar_gt δ ρ (harmonic (d - 1)) (Real.log d)
      hδ hδ' hρ hH hlog
    dsimp [d] at h ⊢
    convert h using 1; ring_nf

/-- The prescribed multiplicity satisfies the discrete band threshold. -/
theorem band_prescribed_gap_multiplicity (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := (harmonic (d - 1) : ℝ)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let g := min 1 (δ / ρ)
    100 * ((d : ℝ) + 1) ≤ g * m := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := (harmonic (d - 1) : ℝ)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  obtain ⟨hd, hlog, hH⟩ := band_prescribed_order_lower δ hδ hδ'
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hHp : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hδH : 169 / 25 ≤ δ * H := by
    have := (div_le_iff₀ hδ).mp hH
    nlinarith
  have hg : δ ≤ min 1 (δ / ρ) := by
    apply le_min (by linarith)
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hscaled := mul_le_mul_of_nonneg_left hsize hδ.le
  have hscaledH := mul_le_mul_of_nonneg_left hδH
    (by positivity : 0 ≤ 100 * (d : ℝ) ^ 2)
  have hgscaled := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg m)
  have hpoly : 100 * ((d : ℝ) + 1) ≤ 100 * (d : ℝ) ^ 2 * (169 / 25) := by
    nlinarith
  dsimp only
  change 100 * ((d : ℝ) + 1) ≤ min 1 (δ / ρ) * m
  nlinarith

end ReedSolomon.HiddenDerivative
