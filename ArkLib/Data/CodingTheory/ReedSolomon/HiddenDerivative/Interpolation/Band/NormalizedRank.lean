/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Band.ParameterBounds
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.LocalRank
import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# Normalized asymmetric-band rank bound conditional on band counting

The cardinality lower bound is an explicit premise throughout. This module assembles the
finite geometric budget and rounding estimates from the prescribed parameters of
[DKTZ26].
The harmonic identity is stated for the finite sum, independently of the top-level contract.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26]
-/

open PolynomialDifferential


open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- The real finite sum in the parameter contract equals Mathlib's rational harmonic number. -/
theorem band_harmonic_sum_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)) = (harmonic n : ℝ) := by
  simp [harmonic, Rat.cast_sum, Nat.cast_add, Nat.cast_one, one_div]

/-- The parameter harmonic sum is positive whenever its index is nonzero. -/
theorem band_harmonic_sum_pos (n : ℕ) (hn : 0 < n) :
    0 < ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1) := by
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · exact ⟨0, Finset.mem_range.mpr hn, by norm_num⟩

/-- The harmonic upper bound and finite exponent error imply the paper's `19/10` factor. -/
theorem band_exp_le_rpow (g H E : ℝ) (d : ℕ) (hg : 0 ≤ g) (hd : 0 < d)
    (hH : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / (1 + g / 2) + 1 / 100) :
    Real.exp E ≤ 19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2)) := by
  exact InterpolationRounding.exp_le_rpow (1 + g / 2) H E (19 / 10) d
    (by linarith) hd hH hE band_exp_error_lt.le

/-- Dividing the positive power by the derivative order gives the gap-decay exponent. -/
theorem band_rpow_div_order (g : ℝ) (d : ℕ) (hg : 0 ≤ g) (hd : 0 < d) :
    (d : ℝ) ^ (1 / (1 + g / 2)) / d = (d : ℝ) ^ (-g / (2 + g)) := by
  have hdp : (0 : ℝ) < d := by positivity
  have ha : (1 + g / 2) ≠ 0 := by linarith
  have hg2 : (2 + g) ≠ 0 := by linarith
  have he : 1 / (1 + g / 2) - 1 = -g / (2 + g) := by
    field_simp
    ring
  rw [← he, Real.rpow_sub hdp, Real.rpow_one]

/-- Scalar assembly of the normalized estimate, with every external numerical premise exposed. -/
theorem localCoordinateBudget_le_normalized_of_scalar_bounds
    (g H B : ℝ) (d m W Be : ℕ) (hg : 0 ≤ g) (hH : 0 < H) (hB : 0 ≤ B)
    (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hBe : (Be : ℝ) ≤ 9 / 8 * g * m)
    (hvolume : (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤ 100 / 29 * B)
    (hexp : Real.exp ((((d - 1 : ℕ) : ℝ) * m / W) *
      (1 + (d.choose 2 : ℝ) / m)) ≤ 19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2)))
    (hrec : 1 / (((d - 1 : ℕ) : ℝ) * m / W) ^ 2 +
      (d : ℝ) / (m * (((d - 1 : ℕ) : ℝ) * m / W)) ≤
        101 / 100 * (1 / (H / (1 + g / 2)) ^ 2)) :
    (localCoordinateBudget d m W Be : ℝ) ≤
      15 / 2 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
  have hk : 0 < κ := by
    have : 0 < d - 1 := by omega
    dsimp [κ]
    positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have ha : 1 + g / 2 ≠ 0 := by linarith
  have hbase := localCoordinateBudget_le_kappa d m W Be hd hm hW
  change (localCoordinateBudget d m W Be : ℝ) ≤ _ at hbase
  have hid : (m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ =
      (m : ℝ) ^ 2 / d * (1 / κ ^ 2 + (d : ℝ) / (m * κ)) := by
    field_simp
  change _ ≤ Be * _ * Real.exp (κ * _) *
    ((m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ) at hbase
  rw [hid] at hbase
  have hupper : (Be : ℝ) *
      ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
      Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
      ((m : ℝ) ^ 2 / d * (1 / κ ^ 2 + (d : ℝ) / (m * κ))) ≤
      (9 / 8 * g * m) * (100 / 29 * B) *
      (19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2))) *
      ((m : ℝ) ^ 2 / d * (101 / 100 * (1 / (H / (1 + g / 2)) ^ 2))) := by
    gcongr
  have heq : (9 / 8 * g * (m : ℝ)) * (100 / 29 * B) *
      (19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2))) *
      ((m : ℝ) ^ 2 / d * (101 / 100 * (1 / (H / (1 + g / 2)) ^ 2))) =
      ((9 / 8 : ℝ) * (100 / 29) * (101 / 100) * (19 / 10)) *
      (g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        ((d : ℝ) ^ (1 / (1 + g / 2)) / d)) := by
    field_simp
  rw [heq, band_rpow_div_order g d hg (by omega)] at hupper
  have hconst := mul_le_mul_of_nonneg_right band_rank_constant_lt.le
    (by positivity : 0 ≤ g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
      (d : ℝ) ^ (-g / (2 + g)))
  exact (hbase.trans hupper).trans (by convert hconst using 1; ring)

/-- The prescribed parameter budget satisfies the normalized bound conditional on band counting.
The support lower bound is the sole counting premise; the window threshold is explicit. -/
theorem localCoordinateBudget_le_normalized_of_band_card_lower
    (g : ℝ) (d : ℕ) (hg : 0 ≤ g) (hg' : g ≤ 1) (hd : 1000 ≤ d) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    let B := (asymmetricBandTuples d W Cmin Cmax).card
    80 ≤ g * m →
    29 / 100 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤ B →
    (localCoordinateBudget d m W Be : ℝ) ≤
      15 / 2 * g * a ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  dsimp only
  let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
  let a := 1 + g / 2
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
  let B := (asymmetricBandTuples d W Cmin Cmax).card
  intro hgm hcount
  have hH : 0 < H := band_harmonic_sum_pos (d - 1) (by omega)
  have hHlog : H ≤ Real.log d + 3 / 5 := by
    dsimp [H]
    rw [band_harmonic_sum_eq]
    exact Real.harmonic_pred_le_log_add_three_fifths d (by omega)
  obtain ⟨hm, hW, hκ, hlo, hhi, he, herr, hrec⟩ :=
    band_prescribed_kappa_bounds g H d hg hH hd
  have hBe : (Be : ℝ) ≤ 9 / 8 * g * m := band_errorWindow_le g m hg hg' hgm
  have hvolume : (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      100 / 29 * (B : ℝ) := by
    change 29 / 100 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤
      (B : ℝ) at hcount
    linarith
  have hexp := band_exp_le_rpow g H
    ((((d - 1 : ℕ) : ℝ) * m / W) * (1 + (d.choose 2 : ℝ) / m)) d
    hg (by omega) hHlog he
  exact localCoordinateBudget_le_normalized_of_scalar_bounds g H B d m W Be
    hg hH (Nat.cast_nonneg B) (by omega) hm hW hBe hvolume hexp hrec

/-- The actual local constraint rank has the normalized bound, conditional on band counting.
This applies at any center and received value over any field. -/
theorem finrank_asymmetricBandLocalConstraint_le_normalized_of_band_card_lower
    {F : Type*} [Field F] (g : ℝ) (d D : ℕ) (center received : F)
    (hg : 0 ≤ g) (hg' : g ≤ 1) (hd : 1000 ≤ d) (hD : 0 < D) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let B := (asymmetricBandTuples d W Cmin Cmax).card
    80 ≤ g * m →
    29 / 100 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤ B →
    (Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := (m : ℝ) * D * (1 + g))
        hD center received)) : ℝ) ≤
      15 / 2 * g * a ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  dsimp only
  let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  intro hgm hcount
  have hbudget := localCoordinateBudget_le_normalized_of_band_card_lower
    g d hg hg' hd hgm hcount
  have hrank := finrank_asymmetricBandLocalConstraint_le
    (d := d) (m := m) (W := W) (Cmin := Cmin) (Cmax := Cmax)
    (L := (m : ℝ) * D * (1 + g)) (by omega) hD center received
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have heq : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by field_simp
  rw [heq] at hrank
  exact (Nat.cast_le.mpr hrank).trans hbudget

end ReedSolomon.HiddenDerivative
