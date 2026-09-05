/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Band.Ambient
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Band.EndpointComparison
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Band.MassBound
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.DimensionBound


/-!
# Prescribed asymmetric-band parameter assembly

The block-size and feasibility hypotheses imply the scalar prerequisites for finite band
counting and the strict dimension comparison. The construction of a polynomial in the common
kernel belongs to the construction layer.
-/

open PolynomialDifferential


namespace ReedSolomon

open HiddenDerivative
open scoped BigOperators

/-- The contract harmonic number is the real cast of Mathlib's harmonic number. -/
theorem harmonicNumber_eq_harmonic (r : ℕ) : harmonicNumber r = (harmonic r : ℝ) :=
  band_harmonic_sum_eq r

/-- The harmonic parameter is the reciprocal-weight sum and is at most the derivative order. -/
theorem band_harmonic_parameter_bounds (d : ℕ) :
    harmonicNumber (d - 1) = ∑ i : Fin (d - 1), simplexReciprocalWeights d i ∧
      harmonicNumber (d - 1) ≤ d := by
  constructor
  · simpa only [harmonicNumber, simplexReciprocalWeights, Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range (fun i ↦ (1 : ℝ) / (i + 1)) (d - 1)).symm
  · have hsum : harmonicNumber (d - 1) ≤ ((d - 1 : ℕ) : ℝ) := by
      unfold harmonicNumber
      calc
        _ ≤ ∑ _i ∈ Finset.range (d - 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          apply (div_le_one (by positivity)).mpr
          have := Nat.cast_nonneg (α := ℝ) i
          linarith
        _ = _ := by simp
    exact hsum.trans (by exact_mod_cast Nat.sub_le d 1)

/-- The prescribed order and multiplicity force enough finite ambient room. -/
theorem band_block_size_bounds (δ : ℝ) (n k : ℕ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let D := asymmetricBandAmbientDimension δ n k - 1
    12 ≤ δ * n ∧ 0 < D ∧ d < D ∧ δ / 3 ≤ (D : ℝ) / n ∧
      (D : ℝ) / n ≤ 1 - δ := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  obtain ⟨hd, hlog, hH⟩ := band_prescribed_order_lower δ hδ hδ'.le
  have hδH : 169 / 25 ≤ δ * H := by
    dsimp [H]
    rw [harmonicNumber_eq_harmonic]
    have := (div_le_iff₀ hδ).mp hH
    nlinarith
  have hm : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hscaled := mul_le_mul_of_nonneg_left hm hδ.le
  have hscaledH := mul_le_mul_of_nonneg_left hδH
    (by positivity : 0 ≤ 100 * (d : ℝ) ^ 2)
  have hblock' : 8 * m ≤ n := hblock
  have hmn : 8 * (m : ℝ) ≤ n := by exact_mod_cast hblock'
  have hδmn := mul_le_mul_of_nonneg_left hmn hδ.le
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hbig : 5408 * (d : ℝ) ^ 2 ≤ δ * n := by nlinarith
  have hsize : 12 ≤ δ * n := by nlinarith
  obtain ⟨hD, hlo, hhi⟩ := asymmetricBandAmbientRate_bounds hδ hδ' hk hsize hA
  have hn : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [hz, mul_zero] at hsize
    norm_num at hsize
  have hlow := (le_div_iff₀ hn).mp hlo
  have hdD : d < asymmetricBandAmbientDimension δ n k - 1 := by
    have : (d : ℝ) < (asymmetricBandAmbientDimension δ n k - 1 : ℕ) := by nlinarith
    exact_mod_cast this
  exact ⟨hsize, hD, hdD, hlo, hhi⟩

/-- A single rate-parameter package supplies the actual finite mass and all its scalar premises. -/
theorem band_rate_parameter_estimates (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let g := min 1 (δ / ρ)
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    1000 ≤ d ∧ 0 < H ∧ H ≤ d ∧ 169 / 25 ≤ δ * H ∧
      0 < g ∧ g ≤ 1 ∧ (1 + g / 2) * δ ≤ g ∧
      100 * ((d : ℝ) + 1) ≤ g * m ∧ 0 < m ∧ 0 < W ∧
      (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
        (asymmetricBandTuples d W ⌊(1 - g / 10) * m⌋₊
          ⌈(1 + 13 * g / 20) * m⌉₊).card := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let g := min 1 (δ / ρ)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  obtain ⟨hd, hlog, hH⟩ := band_prescribed_order_lower δ hδ hδ'
  have hδH : 169 / 25 ≤ δ * H := by
    dsimp [H]
    rw [harmonicNumber_eq_harmonic]
    have := (div_le_iff₀ hδ).mp hH
    nlinarith
  have hHp : 0 < H := by nlinarith
  obtain ⟨hg, hg1, hratio, hgap, hag⟩ :=
    band_relativeSlack_bounds hδ (by linarith) hρ hρ'
  have hgm : 100 * ((d : ℝ) + 1) ≤ g * m := by
    have h := band_prescribed_gap_multiplicity δ ρ hδ hδ' hρ hρ'
    dsimp [d, g, m, H]
    simpa only [harmonicNumber_eq_harmonic] using h
  obtain ⟨hm, hW, hκ, hlo, hhi, he, herr, hrec⟩ :=
    band_prescribed_kappa_bounds g H d hg.le hHp hd
  have hHB := band_harmonic_parameter_bounds d
  have hmass := asymmetricBand_mass_of_parameters (d := d) (m := m) (W := W)
    g δ H hd hg1 hδ hHB.1 hHB.2 hδH hag hgm (Nat.le_ceil _) rfl
  exact ⟨hd, hHp, hHB.2, hδH, hg, hg1, hag, hgm, hm, hW, hmass⟩

private theorem band_scalar_comparison (g H B m n D p : ℝ)
    (hg : 0 < g) (hH : 0 < H) (hB : 0 < B) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p)
    (hendpoint : 1215 < p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2) :
    n * (15 / 2 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * m ^ 3 / p) <
      B * D * m ^ 3 * g ^ 3 / 162 := by
  have ha : 0 < 1 + g / 2 := by linarith
  have hid : p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2 =
      (p * H ^ 2 * D * g ^ 2) / (n * (1 + g / 2) ^ 2) := by field_simp
  rw [hid] at hendpoint
  have hcross := (lt_div_iff₀ (by positivity : 0 < n * (1 + g / 2) ^ 2)).mp hendpoint
  field_simp
  nlinarith only [hcross]

/-- The prescribed finite band has strictly more dimensions than all local budgets combined.
Only the original block-size, positive-dimension, and agreement-feasibility assumptions remain. -/
theorem band_prescribed_budget_lt_finrank {F : Type*} [Field F]
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let D := asymmetricBandAmbientDimension δ n k - 1
    let g := min 1 (δ / ((D : ℝ) / n))
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    ∃ hD : 0 < D,
      n * asymmetricBandLocalBudget d m W Be <
        Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
          ((D : ℝ) * m * (1 + g)) hD) := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let D := asymmetricBandAmbientDimension δ n k - 1
  let ρ := (D : ℝ) / n
  let g := min 1 (δ / ρ)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
  let B := (asymmetricBandTuples d W Cmin Cmax).card
  obtain ⟨hsize, hD, hdD, hρlo, hρhi⟩ := band_block_size_bounds δ n k hδ hδ' hk hblock hA
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hρlo
  obtain ⟨hd, hH, hHd, hδH, hg, hg1, hag, hgm, hm, hW, hmass⟩ :=
    band_rate_parameter_estimates δ ρ hδ hδ'.le hρ hρhi
  change (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) /
    ((d - 1).factorial : ℝ) ^ 2 ≤ (B : ℝ) at hmass
  have hB : (0 : ℝ) < B := by
    have hp : (0 : ℝ) < (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) /
        ((d - 1).factorial : ℝ) ^ 2 := by positivity
    exact hp.trans_le hmass
  have hn : 0 < n := by
    have hblock' : 8 * m ≤ n := hblock
    omega
  have hbudget : (asymmetricBandLocalBudget d m W Be : ℝ) ≤
      15 / 2 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
    have hmass' : 29 / 100 * ((W : ℝ) ^ (d - 1) /
        ((d - 1).factorial : ℝ) ^ 2) ≤ B := by simpa only [mul_div_assoc] using hmass
    have hgm' : 80 ≤ g * m := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    exact asymmetricBandLocalBudget_le_normalized_of_band_card_lower g d hg.le hg1 hd hgm' hmass'
  have hdim := finrank_asymmetricBandSpace_ge_paper_cubic
    (F := F) (d := d) (m := m) (W := W) (Cmin := Cmin)
    (by omega) hD hg.le hg1 hgm
  have hendpoint : (1215 : ℝ) < (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ρ * g ^ 2 /
      (1 + g / 2) ^ 2 := by
    have h := band_prescribed_endpoint_gt δ ρ hδ hδ'.le hρlo hρhi
    dsimp [H, d, g]
    simpa only [harmonicNumber_eq_harmonic] using h
  have hdp : (0 : ℝ) < d := by positivity
  have hstrict := band_scalar_comparison g H B m n D ((d : ℝ) ^ (g / (2 + g)))
    hg hH hB (by positivity) (by positivity) (Real.rpow_pos_of_pos hdp _) hendpoint
  have hpow : (d : ℝ) ^ (-g / (2 + g)) = 1 / (d : ℝ) ^ (g / (2 + g)) := by
    rw [neg_div, Real.rpow_neg hdp.le]
    simp only [one_div]
  rw [hpow, mul_one_div] at hbudget
  have htotal := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  refine ⟨hD, ?_⟩
  have hfinal := (htotal.trans_lt hstrict).trans_le hdim
  change n * asymmetricBandLocalBudget d m W Be <
    Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g)) hD)
  exact_mod_cast hfinal

/-- The same strict comparison in the exact combinatorial dimension-count interface. -/
theorem band_prescribed_budget_lt_dimensionCount
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let D := asymmetricBandAmbientDimension δ n k - 1
    let g := min 1 (δ / ((D : ℝ) / n))
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    n * asymmetricBandLocalBudget d m W Be <
      asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g)) := by
  obtain ⟨hD, h⟩ := band_prescribed_budget_lt_finrank (F := ℚ) δ n k hδ hδ' hk hblock hA
  have hd := (band_prescribed_order_lower δ hδ hδ'.le).1
  rw [finrank_asymmetricBandSpace_eq_dimensionCount (by omega) hD] at h
  exact h

/-- The numerical field-size conditions used by the prime-field construction.
No assertion about characteristic is inferred from cardinality for an arbitrary field. -/
theorem band_prescribed_field_size_bounds
    (δ : ℝ) (n k q : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) (hq : n ≤ q) :
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let D := asymmetricBandAmbientDimension δ n k - 1
    d < D ∧ D < n ∧ d < q ∧ 2 * m < q ∧
      8 * (m * agreementThreshold δ n k) ≤ q ^ 2 := by
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let D := asymmetricBandAmbientDimension δ n k - 1
  obtain ⟨hsize, hD, hdD, hlo, hhi⟩ := band_block_size_bounds δ n k hδ hδ' hk hblock hA
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz] at hsize
    norm_num at hsize
  have hDn : D < n := by
    have hlt : (D : ℝ) / n < 1 := lt_of_le_of_lt hhi (by linarith)
    have := (div_lt_one (by positivity : (0 : ℝ) < n)).mp hlt
    exact_mod_cast this
  have hblock' : 8 * m ≤ n := hblock
  exact ⟨hdD, hDn, (hdD.trans hDn).trans_le hq, by omega,
    band_contact_budget_le_eighth hblock' hA hq⟩

end ReedSolomon
