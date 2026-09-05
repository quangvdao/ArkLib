/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.PrescribedBand


/-!
# Fixed dimension margin for symbolic band interpolation

The prescribed numerical endpoint gives a strict fixed ratio between the actual band
space dimension and the sum of the local constraint ranks. The resulting kernel-height
ratio is bounded uniformly, including the zero-local-rank case.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The high-rate endpoint retains the fixed margin used by symbolic interpolation. -/
theorem band_endpoint_constant_gt_fixed_margin :
    (456976 / 375 : ℝ) < (169 / 25) ^ 2 * Real.exp (169 / 50) := by
  have h := mul_lt_mul_of_pos_left band_endpoint_exp_lower
    (by positivity : (0 : ℝ) < (169 / 25) ^ 2)
  norm_num at h ⊢
  linarith

/-- The high-rate endpoint function retains the fixed symbolic-interpolation margin. -/
theorem band_endpoint_function_gt_fixed_margin (delta rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 4)
    (hrho : delta ≤ rho) (hrho' : rho ≤ 1 - delta) :
    (456976 / 375 : ℝ) <
      4 * (169 / 25) ^ 2 * rho / (2 * rho + delta) ^ 2 *
        Real.exp ((169 / 25) / (2 * rho + delta)) := by
  have h := band_endpoint_function_antitone delta rho (1 - delta) (169 / 25)
    hdelta hrho hrho' (by norm_num)
  have heq : 2 * (1 - delta) + delta = 2 - delta := by ring
  rw [heq] at h
  exact (band_endpoint_constant_gt_fixed_margin.trans_le
    (band_endpoint_at_upper delta hdelta hdelta')).trans_le h

/-- Lower harmonic and logarithmic estimates preserve the fixed margin in the high-rate regime. -/
theorem band_high_rate_scalar_gt_fixed_margin (delta rho H ell : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 4)
    (hrho : delta ≤ rho) (hrho' : rho ≤ 1 - delta)
    (hH : (169 / 25) / delta ≤ H) (hell : (169 / 25) / delta ≤ ell) :
    (456976 / 375 : ℝ) <
      Real.exp (ell * (delta / rho) / (2 + delta / rho)) *
        H ^ 2 * rho * (delta / rho) ^ 2 /
          (1 + (delta / rho) / 2) ^ 2 := by
  have hrhop : 0 < rho := lt_of_lt_of_le hdelta hrho
  have hden : 0 < 2 + delta / rho := by positivity
  have he : (169 / 25 : ℝ) / (2 * rho + delta) ≤
      ell * (delta / rho) / (2 + delta / rho) := by
    have h := mul_le_mul_of_nonneg_right hell (by positivity : 0 ≤ delta / rho)
    have h' := div_le_div_of_nonneg_right h hden.le
    have hid : ((169 / 25 : ℝ) / delta) * (delta / rho) /
        (2 + delta / rho) = (169 / 25) / (2 * rho + delta) := by
      field_simp
    rwa [hid] at h'
  have he' := Real.exp_le_exp.mpr he
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (169 / 25 : ℝ) / delta) hH 2
  have hbound :
      Real.exp ((169 / 25) / (2 * rho + delta)) *
          ((169 / 25 : ℝ) / delta) ^ 2 * rho * (delta / rho) ^ 2 /
            (1 + (delta / rho) / 2) ^ 2 ≤
        Real.exp (ell * (delta / rho) / (2 + delta / rho)) *
          H ^ 2 * rho * (delta / rho) ^ 2 /
            (1 + (delta / rho) / 2) ^ 2 := by
    gcongr
  have hid :
      Real.exp ((169 / 25) / (2 * rho + delta)) *
          ((169 / 25 : ℝ) / delta) ^ 2 * rho * (delta / rho) ^ 2 /
            (1 + (delta / rho) / 2) ^ 2 =
        4 * (169 / 25) ^ 2 * rho / (2 * rho + delta) ^ 2 *
          Real.exp ((169 / 25) / (2 * rho + delta)) := by
    field_simp
    ring
  rw [hid] at hbound
  exact (band_endpoint_function_gt_fixed_margin delta rho
    hdelta hdelta' hrho hrho').trans_le hbound

/-- The elementary lower bound on `exp 4` needed at the low-rate endpoint. -/
theorem forty_five_lt_exp_four : (45 : ℝ) < Real.exp 4 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The low-rate endpoint retains the same fixed margin. -/
theorem band_low_rate_scalar_gt_fixed_margin (delta rho H ell : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 4)
    (hrho : delta / 3 ≤ rho)
    (hH : (169 / 25) / delta ≤ H) (hell : (169 / 25) / delta ≤ ell) :
    (456976 / 375 : ℝ) <
      Real.exp (ell / 3) * H ^ 2 * rho / (3 / 2) ^ 2 := by
  have hHp : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hrhop : 0 < rho := lt_of_lt_of_le (by positivity) hrho
  have he : 4 ≤ ell / 3 := by
    have hl := (div_le_iff₀ hdelta).mp hell
    have hlow : (169 / 25 : ℝ) / delta ≥ (169 / 25) * 4 := by
      apply (le_div_iff₀ hdelta).mpr
      nlinarith
    linarith
  have he' := Real.exp_le_exp.mpr he
  have hfactor : (4 * (169 / 25 : ℝ) ^ 2 / 27) / delta ≤
      H ^ 2 * rho / (3 / 2) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (169 / 25 : ℝ) / delta) hH 2
    have hmul := mul_le_mul hsq hrho (by positivity : 0 ≤ delta / 3) (sq_nonneg H)
    have hid : ((169 / 25 : ℝ) / delta) ^ 2 * (delta / 3) / (3 / 2) ^ 2 =
        (4 * (169 / 25 : ℝ) ^ 2 / 27) / delta := by
      field_simp
      ring
    rw [← hid]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hfactor' : (16 * (169 / 25 : ℝ) ^ 2 / 27) ≤
      H ^ 2 * rho / (3 / 2) ^ 2 := by
    apply le_trans ?_ hfactor
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hbound := mul_le_mul he' hfactor' (by norm_num) (Real.exp_pos _).le
  have hnum : (456976 / 375 : ℝ) <
      Real.exp 4 * (16 * (169 / 25 : ℝ) ^ 2 / 27) := by
    have h := mul_lt_mul_of_pos_right forty_five_lt_exp_four
      (by positivity : (0 : ℝ) < 16 * (169 / 25 : ℝ) ^ 2 / 27)
    norm_num at h ⊢
    linarith
  exact hnum.trans_le (by convert hbound using 1; ring)

/-- The prescribed rounded band parameters retain the strict fixed endpoint margin. -/
theorem band_prescribed_endpoint_gt_fixed_margin (delta rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1 / 4)
    (hrho : delta / 3 ≤ rho) (hrho' : rho ≤ 1 - delta) :
    let d := Nat.ceil (Real.exp ((169 / 25) / delta))
    let H := (harmonic (d - 1) : ℝ)
    let g := min 1 (delta / rho)
    let a := 1 + g / 2
    (456976 / 375 : ℝ) <
      (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * rho * g ^ 2 / a ^ 2 := by
  let d := Nat.ceil (Real.exp ((169 / 25) / delta))
  have hrhop : 0 < rho := lt_of_lt_of_le (by positivity) hrho
  obtain ⟨hd, hlog, hH⟩ := band_prescribed_order_lower delta hdelta hdelta'
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  dsimp only
  rw [Real.rpow_def_of_pos hdp]
  by_cases hhigh : delta ≤ rho
  · have hg : min (1 : ℝ) (delta / rho) = delta / rho :=
      min_eq_right ((div_le_one hrhop).mpr hhigh)
    rw [hg]
    have h := band_high_rate_scalar_gt_fixed_margin delta rho
      (harmonic (d - 1)) (Real.log d)
      hdelta hdelta' hhigh hrho' hH hlog
    dsimp [d] at h ⊢
    convert h using 1
    all_goals ring_nf
  · have hg : min (1 : ℝ) (delta / rho) = 1 :=
      min_eq_left ((one_le_div hrhop).mpr (by linarith))
    rw [hg]
    have h := band_low_rate_scalar_gt_fixed_margin delta rho
      (harmonic (d - 1)) (Real.log d) hdelta hdelta' hrho hH hlog
    dsimp [d] at h ⊢
    convert h using 1
    all_goals ring_nf

private theorem band_scalar_fixed_margin
    (g H B m n D p : ℝ)
    (hg : 0 < g) (hH : 0 < H) (hB : 0 < B) (hm : 0 < m)
    (hn : 0 < n) (hp : 0 < p)
    (hendpoint : (456976 / 375 : ℝ) <
      p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2) :
    (456976 / 455625 : ℝ) * n *
        (15 / 2 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * m ^ 3 / p) <
      B * D * m ^ 3 * g ^ 3 / 162 := by
  have ha : 0 < 1 + g / 2 := by linarith
  have hid : p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2 =
      (p * H ^ 2 * D * g ^ 2) / (n * (1 + g / 2) ^ 2) := by
    field_simp
  rw [hid] at hendpoint
  have hcross :=
    (lt_div_iff₀ (by positivity : 0 < n * (1 + g / 2) ^ 2)).mp hendpoint
  field_simp
  nlinarith only [hcross]

open ReedSolomon in
/-- The prescribed band dimension exceeds the block length times its actual local rank by the
fixed factor needed for a challenge-degree bound independent of the block length. -/
theorem band_prescribed_fixed_margin_finrank {F : Type*} [Field F]
    (delta : ℝ) (n k : ℕ) (center received : F)
    (hdelta : 0 < delta) (hdelta' : delta < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / delta)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / delta)) - 1)) ≤ n)
    (hA : agreementThreshold delta n k ≤ n) :
    let d := Nat.ceil (Real.exp ((169 / 25) / delta))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let D := asymmetricBandAmbientDimension delta n k - 1
    let g := min 1 (delta / ((D : ℝ) / n))
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    ∃ hD : 0 < D,
      (456976 / 455625 : ℝ) * n *
          Module.finrank F (LinearMap.range
            (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
              (Cmin := Cmin) (Cmax := Cmax)
              (L := (m : ℝ) * D * (1 + g)) hD center received)) <
        Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
          ((D : ℝ) * m * (1 + g)) hD) := by
  let d := Nat.ceil (Real.exp ((169 / 25) / delta))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let D := asymmetricBandAmbientDimension delta n k - 1
  let rho := (D : ℝ) / n
  let g := min 1 (delta / rho)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let B := (asymmetricBandTuples d W Cmin Cmax).card
  obtain ⟨_hsize, hD, _hdD, hrhoLow, hrhoHigh⟩ :=
    band_block_size_bounds delta n k hdelta hdelta' hk hblock hA
  have hrho : 0 < rho := lt_of_lt_of_le (by positivity) hrhoLow
  obtain ⟨hd, hH, _hHd, _hdeltaH, hg, hg1, _hag, hgm, hm, _hW, hmass⟩ :=
    band_rate_parameter_estimates delta rho hdelta hdelta'.le hrho hrhoHigh
  have hB : (0 : ℝ) < B := by
    have hp : (0 : ℝ) < (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) /
        ((d - 1).factorial : ℝ) ^ 2 := by positivity
    exact hp.trans_le hmass
  have hn : 0 < n := by
    have hblock' : 8 * m ≤ n := hblock
    omega
  have hgm80 : (80 : ℝ) ≤ g * m := by
    have hdNonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hrank := finrank_asymmetricBandLocalConstraint_le_normalized_of_band_card_lower
    g d D center received hg.le hg1 hd hD
    (by simpa only [H, harmonicNumber, m] using hgm80)
    (by
      simpa only [H, harmonicNumber, m, W, Cmin, Cmax, B, mul_div_assoc]
        using hmass)
  have hdim := finrank_asymmetricBandSpace_ge_paper_cubic
    (F := F) (d := d) (m := m) (W := W) (Cmin := Cmin)
    (by omega) hD hg.le hg1 hgm
  have hendpoint : (456976 / 375 : ℝ) <
      (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * rho * g ^ 2 /
        (1 + g / 2) ^ 2 := by
    have h := band_prescribed_endpoint_gt_fixed_margin
      delta rho hdelta hdelta'.le hrhoLow hrhoHigh
    dsimp [H, d, g]
    simpa only [harmonicNumber_eq_harmonic] using h
  have hdp : (0 : ℝ) < d := by positivity
  have hpow : (d : ℝ) ^ (-g / (2 + g)) =
      1 / (d : ℝ) ^ (g / (2 + g)) := by
    rw [neg_div, Real.rpow_neg hdp.le]
    simp only [one_div]
  rw [hpow, mul_one_div] at hrank
  have hrankScaled := mul_le_mul_of_nonneg_left hrank
    (by positivity : 0 ≤ (456976 / 455625 : ℝ) * n)
  have hstrict := band_scalar_fixed_margin g H B m n D
    ((d : ℝ) ^ (g / (2 + g))) hg hH hB (by positivity) (by positivity)
      (Real.rpow_pos_of_pos hdp _) hendpoint
  refine ⟨hD, ?_⟩
  exact (hrankScaled.trans_lt hstrict).trans_le hdim

/-- A `456976 / 455625` dimension margin gives the exact kernel-height ratio.  The zero-rank
case is included rather than hidden behind a positivity hypothesis. -/
theorem fixed_margin_kernel_ratio_lt (N R : ℕ)
    (hmargin : (456976 / 455625 : ℝ) * R < N) :
    (R : ℝ) / (N - R) < 455625 / 1351 ∧
      (R : ℝ) / (N - R) < 338 := by
  by_cases hR : R = 0
  · subst R
    norm_num
  · have hRPos : (0 : ℝ) < R := by positivity
    have hRN : R < N := by
      have hscale : (R : ℝ) < (456976 / 455625 : ℝ) * R := by
        nlinarith
      exact_mod_cast hscale.trans hmargin
    have hden : (0 : ℝ) < N - R := by
      exact sub_pos.mpr (by exact_mod_cast hRN)
    have hsharp : (R : ℝ) / (N - R) < 455625 / 1351 := by
      apply (div_lt_iff₀ hden).2
      norm_num at hmargin ⊢
      nlinarith
    exact ⟨hsharp, hsharp.trans (by norm_num)⟩

/-- Multiplying the fixed-margin kernel ratio by a positive entry-degree bound yields the
manuscript's strict challenge-height inequalities. -/
theorem fixed_margin_kernel_height_lt (N R nu : ℕ) (hnu : 0 < nu)
    (hmargin : (456976 / 455625 : ℝ) * R < N) :
    ((R * nu / (N - R) : ℕ) : ℝ) < (455625 / 1351 : ℝ) * nu ∧
      ((R * nu / (N - R) : ℕ) : ℝ) < 338 * nu := by
  have hratio := (fixed_margin_kernel_ratio_lt N R hmargin).1
  have hRN : R < N := by
    have hscale : (R : ℝ) ≤ (456976 / 455625 : ℝ) * R := by
      have hRNonneg : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      nlinarith
    exact_mod_cast hscale.trans_lt hmargin
  have hcast : ((R * nu / (N - R) : ℕ) : ℝ) ≤
      (R * nu : ℝ) / (N - R) := by
    calc
      ((R * nu / (N - R) : ℕ) : ℝ) ≤
          (((R * nu : ℕ) : ℝ) / ((N - R : ℕ) : ℝ)) :=
        Nat.cast_div_le
      _ = (R * nu : ℝ) / (N - R) := by
        rw [Nat.cast_mul, Nat.cast_sub hRN.le]
  have hsharp : ((R * nu / (N - R) : ℕ) : ℝ) <
      (455625 / 1351 : ℝ) * nu := by
    apply hcast.trans_lt
    calc
      (R * nu : ℝ) / (N - R) = ((R : ℝ) / (N - R)) * nu := by
        ring
      _ < (455625 / 1351 : ℝ) * nu :=
        mul_lt_mul_of_pos_right hratio (by positivity)
  refine ⟨hsharp, hsharp.trans ?_⟩
  have hnuReal : (0 : ℝ) < nu := by positivity
  nlinarith

end

end ReedSolomon.HiddenDerivative
