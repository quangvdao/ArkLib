/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandRankBound
import Mathlib.NumberTheory.Harmonic.EulerMascheroni


/-!
# Rounding bounds for asymmetric-band parameters

These elementary estimates retain the floor and ceiling errors in the parameter choice of
[DKTZ26], source revision `9e4d6488ead94be47cca69e5be915b5667143b66`.
No estimate on the cardinality of the band is used here.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding up to Capacity at Every Rate*][DKTZ26]
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

/-- The two rounding operations cost less than two in the error-coordinate window. -/
theorem band_errorWindow_lt (g : ℝ) (m : ℕ) (hg : 0 ≤ g) (hg' : g ≤ 1) :
    (Nat.ceil ((m : ℝ) * (1 + g) -
      Nat.floor ((1 - g / 10) * m)) : ℝ) < 11 / 10 * g * m + 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : 0 ≤ (1 - g / 10) * (m : ℝ) := mul_nonneg (by linarith) hm
  have hlo := Nat.floor_le hc
  have hhi := Nat.lt_floor_add_one ((1 - g / 10) * (m : ℝ))
  have hgm : 0 ≤ g * (m : ℝ) := mul_nonneg hg hm
  have hnonneg : 0 ≤ (m : ℝ) * (1 + g) -
      Nat.floor ((1 - g / 10) * m) := by nlinarith
  have hceil := Nat.ceil_lt_add_one hnonneg
  nlinarith

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

/-- A floor of a radius at least two is positive. -/
theorem band_floor_pos (R : ℝ) (hR : 2 ≤ R) : 0 < Nat.floor R := by
  have : 1 ≤ Nat.floor R := Nat.le_floor (by norm_num; linarith)
  omega

/-- Reciprocal floor loss, with the full error `2/R` retained. -/
theorem band_floor_reciprocal_le (R : ℝ) (hR : 2 ≤ R) :
    1 / (Nat.floor R : ℝ) ≤ (1 + 2 / R) / R := by
  have hRp : 0 < R := by linarith
  have hFp : (0 : ℝ) < Nat.floor R := by exact_mod_cast band_floor_pos R hR
  have hfloor := Nat.lt_floor_add_one R
  apply (div_le_div_iff₀ hFp hRp).mpr
  have haux : 0 ≤ (R - 2) / R := div_nonneg (by linarith) hRp.le
  have hid : (1 + 2 / R) * (R - 1) = R + (R - 2) / R := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left (by linarith : R - 1 ≤
    (Nat.floor R : ℝ)) (by positivity : 0 ≤ 1 + 2 / R)
  nlinarith

/-- The multiplicity ceiling provides the exact lower bound before later estimates. -/
theorem band_multiplicity_lower (d : ℕ) (H : ℝ) :
    100 * (d : ℝ) ^ 2 * H ≤ (Nat.ceil (100 * (d : ℝ) ^ 2 * H) : ℝ) :=
  Nat.le_ceil _

/-- Floor rounding bounds a nonnegative numerator divided by the width on both sides. -/
theorem band_floor_ratio_bounds (R N : ℝ) (hR : 2 ≤ R) (hN : 0 ≤ N) :
    N / R ≤ N / (Nat.floor R : ℝ) ∧
      N / (Nat.floor R : ℝ) ≤ N / R * (1 + 2 / R) := by
  have hRp : 0 < R := by linarith
  have hFp : (0 : ℝ) < Nat.floor R := by exact_mod_cast band_floor_pos R hR
  constructor
  · exact div_le_div_of_nonneg_left hN hFp (Nat.floor_le hRp.le)
  · have h := mul_le_mul_of_nonneg_left (band_floor_reciprocal_le R hR) hN
    simpa only [div_eq_mul_inv, mul_one, mul_assoc, mul_left_comm, mul_comm] using h

/-- The prescribed radius is large before taking its floor. -/
theorem band_radius_lower (a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H)
    (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    100 * (d : ℝ) ^ 3 ≤ a * d * m / H := by
  apply (le_div_iff₀ hH).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h := mul_le_mul_of_nonneg_left hm hd
  have h' := mul_le_mul_of_nonneg_right ha (mul_nonneg hd hm')
  nlinarith

/-- The reciprocal radius error has the paper's explicit cubic bound. -/
theorem band_radius_error_le (a H : ℝ) (d m : ℕ) (ha : 1 ≤ a) (hH : 0 < H)
    (hd : 0 < d) (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    1 / (a * d * m / H) ≤ 1 / (100 * (d : ℝ) ^ 3) := by
  have hpos : (0 : ℝ) < 100 * (d : ℝ) ^ 3 := by positivity
  exact one_div_le_one_div_of_le hpos (band_radius_lower a H d m ha hH hm)

/-- Exact lower and upper bounds for κ, including the full width-floor error. -/
theorem band_kappa_floor_bounds (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1 ≤ d) (hm : 0 < m)
    (hR : 2 ≤ a * d * m / H) :
    let R := a * d * m / H
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor R
    H / a * (1 - 1 / d) ≤ κ ∧
      κ ≤ H / a * (1 - 1 / d) * (1 + 2 / R) := by
  dsimp only
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have heq : ((d - 1 : ℕ) : ℝ) * m / (a * d * m / H) =
      H / a * (1 - 1 / d) := by
    rw [Nat.cast_sub hd]
    push_cast
    field_simp
  have h := band_floor_ratio_bounds (a * d * m / H)
    (((d - 1 : ℕ) : ℝ) * m) hR (by positivity)
  rw [heq] at h
  exact h

/-- The loss from `d-1` absorbs the entire floor error once the radius is at least `2d`. -/
theorem band_kappa_interval (a H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hH : 0 < H) (hd : 1000 ≤ d) (hm : 0 < m)
    (hR : 2 * (d : ℝ) ≤ a * d * m / H) :
    let κ := ((d - 1 : ℕ) : ℝ) * m / Nat.floor (a * d * m / H)
    999 / 1000 * (H / a) ≤ κ ∧ κ ≤ H / a := by
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hRp : 0 < a * d * m / H := by positivity
  have hb := band_kappa_floor_bounds a H d m ha hH (by omega) hm (by linarith)
  dsimp only at hb ⊢
  have ht : 0 ≤ H / a := (div_pos hH ha).le
  have hrec : 1 / (d : ℝ) ≤ 1 / 1000 :=
    one_div_le_one_div_of_le (by norm_num) hd'
  constructor
  · have := mul_le_mul_of_nonneg_left
      (by linarith : (999 / 1000 : ℝ) ≤ 1 - 1 / d) ht
    nlinarith [hb.1]
  · have herr : 2 / (a * d * m / H) ≤ 1 / (d : ℝ) := by
      apply (div_le_div_iff₀ hRp hdp).mpr
      simpa using hR
    have hbase : 0 ≤ 1 - 1 / (d : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left herr hbase
    have hs := sq_nonneg (1 / (d : ℝ))
    have hfactor : (1 - 1 / (d : ℝ)) * (1 + 2 / (a * d * m / H)) ≤ 1 := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hfactor ht
    nlinarith [hb.2]

/-- The quadratic multiplicity choice implies the radius condition for the κ interval. -/
theorem band_radius_ge_twice_order (a H : ℝ) (d m : ℕ)
    (ha : 1 ≤ a) (hH : 0 < H) (hd : 1 ≤ d)
    (hm : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    2 * (d : ℝ) ≤ a * d * m / H := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ d)
  have := band_radius_lower a H d m ha hH hm
  nlinarith

/-- The binomial shift over the prescribed multiplicity retains its finite bound. -/
theorem band_binomial_error_le (H : ℝ) (d m : ℕ) (hH : 0 < H) (hm : 0 < m)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d.choose 2 : ℝ) / m ≤ 1 / (200 * H) := by
  rw [Nat.cast_choose_two]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < m) (by positivity)).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- The κ interval implies the required exponent estimate with room in the constant. -/
theorem band_kappa_exponent_le (κ a H : ℝ) (d m : ℕ)
    (ha : 1 ≤ a) (hH : 0 < H) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hκa : κ ≤ H / a) (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100 := by
  have hB := band_binomial_error_le H d m hH hm hsize
  have ha' : 0 < a := by linarith
  have hκH : κ ≤ H := hκa.trans ((div_le_iff₀ ha').mpr (by nlinarith))
  have hmul := mul_le_mul_of_nonneg_left hB hκ
  have hsmall : κ * (1 / (200 * H)) ≤ 1 / 200 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  nlinarith

/-- The multiplicity lower bound makes the second reciprocal term negligible. -/
theorem band_kappa_multiplicity_error_le (κ H : ℝ) (d m : ℕ)
    (hH : 0 < H) (hd : 1000 ≤ d) (hm : 0 < m) (hκH : κ ≤ H)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m) :
    (d : ℝ) * κ / m ≤ 1 / 1000 := by
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hκH (by positivity : (0 : ℝ) ≤ d)
  have hprod : (10 : ℝ) * d ≤ (d : ℝ) ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hprod hH.le
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
  nlinarith

/-- A useful scalar form of the last rounding step in the reciprocal κ factor. -/
theorem band_kappa_reciprocal_factor_le (κ t d m : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) (hm : 0 < m)
    (hlo : 999 / 1000 * t ≤ κ) (herr : d * κ / m ≤ 1 / 1000) :
    1 / κ ^ 2 + d / (m * κ) ≤ 101 / 100 * (1 / t ^ 2) := by
  have hsq : (999 / 1000 * t) ^ 2 ≤ κ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hfactor : 1 + d * κ / m ≤ 1001 / 1000 := by linarith
  have hid : 1 / κ ^ 2 + d / (m * κ) = (1 + d * κ / m) / κ ^ 2 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (sq_pos_of_pos hκ)).mpr
  have hnum : (1001 / 1000 : ℝ) ≤
      101 / 100 * (1 / t ^ 2) * κ ^ 2 := by
    have heq : 101 / 100 * (1 / t ^ 2) * κ ^ 2 =
        (101 / 100 * κ ^ 2) / t ^ 2 := by ring
    rw [heq]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    have hscale := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 101 / 100)
    have ht2 := sq_nonneg t
    nlinarith
  exact hfactor.trans hnum

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
  dsimp only
  let a := 1 + g / 2
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  let κ := ((d - 1 : ℕ) : ℝ) * m / W
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := by exact_mod_cast hmp
  have hR := band_radius_ge_twice_order a H d m ha hH (by omega) hsize
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hW : 0 < W := band_floor_pos _ (by linarith)
  have hpred : 0 < d - 1 := by omega
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hint := band_kappa_interval a H d m hap hH hd hm hR
  have he := band_kappa_exponent_le κ a H d m ha hH hm hκ.le hint.2 hsize
  have hκH : κ ≤ H := hint.2.trans ((div_le_iff₀ hap).mpr (by nlinarith))
  have herr := band_kappa_multiplicity_error_le κ H d m hH hd hm hκH hsize
  have hrec := band_kappa_reciprocal_factor_le κ (H / a) d m hκ
    (div_pos hH hap) hmp hint.1 herr
  exact ⟨hm, hW, hκ, hint.1, hint.2, he, herr, hrec⟩

/-- The harmonic upper bound used by the paper holds already from index 32. -/
theorem band_harmonic_le_log (n : ℕ) (hn : 32 ≤ n) :
    (harmonic n : ℝ) ≤ Real.log n + 3 / 5 := by
  have hbase : Real.eulerMascheroniSeq' 32 < 3 / 5 := by
    have hlog : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 5
      norm_num at h
      exact h
    rw [Real.eulerMascheroniSeq']
    norm_num only [OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [hlog]
    have htwo := Real.log_two_gt_d9
    norm_num [harmonic, Finset.sum_range_succ] at *
    linarith
  have hmono := (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt hbase
  have hn0 : n ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', hn0, ↓reduceIte] at hmono
  linarith

/-- The shifted harmonic index in the prescribed parameters has the required logarithmic bound. -/
theorem band_harmonic_pred_le_log (d : ℕ) (hd : 33 ≤ d) :
    (harmonic (d - 1) : ℝ) ≤ Real.log d + 3 / 5 := by
  have h := band_harmonic_le_log (d - 1) (by omega)
  have hp : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
  have hle : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have := Real.log_le_log hp hle
  linarith

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
