/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Band.SimplexCantelli


/-!
# Explicit asymmetric-band mass

Rational Cantelli estimates and stars and bars give an actual lattice count. All uses of
variance refer to the exact discrete simplex; no continuous-volume distribution is assumed.
-/

open PolynomialDifferential


open DiscreteSimplex

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

private theorem reciprocal_square_tail_step (n : ℕ) :
    (1 / (n + 1 : ℝ)) ^ 2 + 2 / (2 * (n + 1 : ℝ) + 1) ≤ 2 / (2 * (n : ℝ) + 1) := by
  have h₁ : (0 : ℝ) < n + 1 := by positivity
  have h₂ : (0 : ℝ) < 2 * (n + 1 : ℝ) + 1 := by positivity
  have h₃ : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  field_simp
  nlinarith

private theorem reciprocal_square_initial :
    (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2) + 2 / 25 < 329 / 200 := by
  norm_num [Finset.sum_range_succ]

/-- A twelve-term rational calculation and a midpoint telescoping tail bound the second
harmonic sum. The tail estimate is valid for every dimension, including zero. -/
theorem reciprocal_square_sum_lt (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 2) < 329 / 200 := by
  by_cases hn : 12 ≤ n
  · have hbound : ∀ k, 12 ≤ k →
        (∑ i ∈ Finset.range k, (1 / (i + 1 : ℝ)) ^ 2) + 2 / (2 * (k : ℝ) + 1) ≤
          (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2) + 2 / 25 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        push_cast
        have h := reciprocal_square_tail_step k
        linarith
    have h := hbound n hn
    have hp : (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) := by positivity
    linarith [reciprocal_square_initial]
  · have hsum : (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 2) ≤
        ∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ ↦ sq_nonneg _)
    linarith [reciprocal_square_initial]

/-- The manuscript's margins yield mass at least `29/100` when the exact variance is
at most `9/250` times the squared scale. -/
theorem band_cantelli_mass_scalar (V s : ℝ) (hV : 0 ≤ V) (hs : 0 < s)
    (hsmall : V ≤ 9 / 250 * s ^ 2) :
    (29 / 100 : ℝ) ≤ 1 - V / (V + (59 / 100 * s) ^ 2) -
      V / (V + (3 / 20 * s) ^ 2) := by
  have hdenL : 0 < V + (59 / 100 * s) ^ 2 := by positivity
  have hdenR : 0 < V + (3 / 20 * s) ^ 2 := by positivity
  have hL : V / (V + (59 / 100 * s) ^ 2) ≤ 360 / 3841 := by
    apply (div_le_iff₀ hdenL).mpr
    nlinarith
  have hR : V / (V + (3 / 20 * s) ^ 2) ≤ 8 / 13 := by
    apply (div_le_iff₀ hdenR).mpr
    nlinarith
  linarith

/-- A purely rational finite-correction bound. The factor `100001/100000` is retained. -/
theorem band_variance_rational_slack :
    (100001 / 100000 : ℝ) * (25 / 169) ^ 2 * (329 / 200) ≤ 9 / 250 := by
  norm_num

/-- Mean and variance of the reciprocal-weight statistic in dimension `d-1`. -/
theorem band_simplex_moments {d W : ℕ} (hd : 0 < d) :
    simplexWeightedMean W (simplexReciprocalWeights d) =
        (W : ℝ) / d * (∑ i : Fin (d - 1), simplexReciprocalWeights d i) ∧
      simplexWeightedVariance W (simplexReciprocalWeights d) =
        (W : ℝ) * (W + d) / ((d : ℝ) ^ 2 * (d + 1)) *
          ((d : ℝ) * (∑ i : Fin (d - 1), simplexReciprocalWeights d i ^ 2) -
            (∑ i : Fin (d - 1), simplexReciprocalWeights d i) ^ 2) := by
  have heq : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hd
  constructor
  · simp only [simplexWeightedMean, heq]
  · unfold simplexWeightedVariance
    rw [heq]
    have heq' : ((d - 1 : ℕ) : ℝ) + 2 = (d : ℝ) + 1 := by linarith
    rw [heq']

/-- A usable exact-variance certificate. The large budget bounds the discrete correction;
`W/d ≤ (25/169)s` carries the gap/harmonic estimate independently of parameter rounding. -/
theorem band_finite_variance_bound {d W : ℕ} (hd : 0 < d) (s : ℝ)
    (hbudget : (100000 : ℝ) * d ≤ W)
    (hscale : (W : ℝ) / d ≤ 25 / 169 * s) :
    simplexWeightedVariance W (simplexReciprocalWeights d) ≤ 9 / 250 * s ^ 2 := by
  let H := ∑ i : Fin (d - 1), simplexReciprocalWeights d i
  let H₂ := ∑ i : Fin (d - 1), simplexReciprocalWeights d i ^ 2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hH₂ : H₂ ≤ 329 / 200 := by
    have h := reciprocal_square_sum_lt (d - 1)
    have heq : H₂ = ∑ i ∈ Finset.range (d - 1), (1 / (i + 1 : ℝ)) ^ 2 := by
      simpa only [H₂, simplexReciprocalWeights, Nat.cast_add, Nat.cast_one] using
        Fin.sum_univ_eq_sum_range (fun i ↦ (1 / (i + 1 : ℝ)) ^ 2) (d - 1)
    rw [heq]
    exact h.le
  have hcoeff : 0 ≤ (W : ℝ) * (W + d) / ((d : ℝ) ^ 2 * (d + 1)) := by positivity
  have hraw := (band_simplex_moments (W := W) hd).2
  change _ = (W : ℝ) * (W + d) / ((d : ℝ) ^ 2 * (d + 1)) * ((d : ℝ) * H₂ - H ^ 2) at hraw
  have hfirst : simplexWeightedVariance W (simplexReciprocalWeights d) ≤
      (W : ℝ) * (W + d) / ((d : ℝ) ^ 2 * (d + 1)) * ((d : ℝ) * (329 / 200)) := by
    rw [hraw]
    apply mul_le_mul_of_nonneg_left _ hcoeff
    nlinarith [sq_nonneg H]
  have hcorrection : (W : ℝ) + d ≤ 100001 / 100000 * W := by linarith
  have hsecond : (W : ℝ) * (W + d) / ((d : ℝ) ^ 2 * (d + 1)) * ((d : ℝ) * (329 / 200)) ≤
      (100001 / 100000 : ℝ) * ((W : ℝ) / d) ^ 2 * (329 / 200) := by
    have hden : 0 < (d : ℝ) ^ 2 * (d + 1) := by positivity
    field_simp
    have hprod := mul_le_mul_of_nonneg_left hcorrection hW
    nlinarith [mul_le_mul_of_nonneg_left hprod hdR.le, mul_nonneg hW hW]
  have hsquare : ((W : ℝ) / d) ^ 2 ≤ (25 / 169 * s) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hW hdR.le) hscale 2
  calc
    _ ≤ (100001 / 100000 : ℝ) * ((W : ℝ) / d) ^ 2 * (329 / 200) := hfirst.trans hsecond
    _ ≤ (100001 / 100000 : ℝ) * (25 / 169 * s) ^ 2 * (329 / 200) := by nlinarith
    _ ≤ 9 / 250 * s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right band_variance_rational_slack (sq_nonneg s)
      nlinarith only [h]

/-- Exact finite mass, assuming explicit mean margins and an exact-variance certificate.
The power bound is derived from stars and bars, not assumed as a volume estimate. -/
theorem asymmetricBand_mass_of_variance {d W Cmin Cmax : ℕ}
    (s : ℝ) (hs : 0 < s)
    (hlo : (Cmin : ℝ) + (d - 1 : ℕ) ≤
      simplexWeightedMean W (simplexReciprocalWeights d) - 59 / 100 * s)
    (hhi : simplexWeightedMean W (simplexReciprocalWeights d) + 3 / 20 * s ≤ Cmax)
    (hV : simplexWeightedVariance W (simplexReciprocalWeights d) ≤ 9 / 250 * s ^ 2) :
    (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W Cmin Cmax).card := by
  have hmass := band_cantelli_mass_scalar _ s (simplexWeightedVariance_nonneg _ _) hs hV
  have hcount := asymmetricBand_card_lower_of_simplex_cantelli
    (59 / 100 * s) (3 / 20 * s) (by positivity) (by positivity) hlo hhi
  have hC : (29 / 100 : ℝ) * Fintype.card (OrdinarySimplex (d - 1) W) ≤
      (asymmetricBandTuples d W Cmin Cmax).card * ((d - 1).factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hmass
      (Nat.cast_nonneg (Fintype.card (OrdinarySimplex (d - 1) W)) : (0 : ℝ) ≤ _)
    push_cast at hcount
    nlinarith only [h, hcount]
  have hpow : (W : ℝ) ^ (d - 1) ≤ (d - 1).factorial *
      (Fintype.card (OrdinarySimplex (d - 1) W) : ℝ) := by
    exact_mod_cast pow_le_factorial_mul_card_ordinarySimplex (d - 1) W
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  apply (div_le_iff₀ (sq_pos_of_pos hfac)).mpr
  have h := mul_le_mul_of_nonneg_left hC hfac.le
  nlinarith

/-- Elementary parameter prerequisites suffice for the actual `29/100` band-mass bound.
The ceiling prescription for `m` may be replaced by its lower bound. The harmonic sum and
gap inequalities are explicit hypotheses to be supplied by the global parameter choice. -/
theorem asymmetricBand_mass_of_parameters {d m W : ℕ} (g δ H : ℝ)
    (hd : 1000 ≤ d) (hg : g ≤ 1) (hδ : 0 < δ)
    (hH : H = ∑ i : Fin (d - 1), simplexReciprocalWeights d i)
    (hHd : H ≤ d) (hδH : 169 / 25 ≤ δ * H)
    (hag : (1 + g / 2) * δ ≤ g)
    (hgm : 100 * ((d : ℝ) + 1) ≤ g * m)
    (hm : 100 * (d : ℝ) ^ 2 * H ≤ m)
    (hW : W = ⌊(1 + g / 2) * d * m / H⌋₊) :
    (29 / 100 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W ⌊(1 - g / 10) * m⌋₊ ⌈(1 + 13 * g / 20) * m⌉₊).card := by
  have hdN : 0 < d := by omega
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hWnonneg : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hHpos : 0 < H := by nlinarith
  have hgpos : 0 < g := by nlinarith
  have hs : 0 < g * (m : ℝ) := by nlinarith
  have hrawnonneg : 0 ≤ (1 + g / 2) * d * m / H := by positivity
  have hupper : (W : ℝ) * H ≤ (1 + g / 2) * d * m := by
    apply (le_div_iff₀ hHpos).mp
    rw [hW]
    exact Nat.floor_le hrawnonneg
  have hlower : (1 + g / 2) * d * m < ((W : ℝ) + 1) * H := by
    apply (div_lt_iff₀ hHpos).mp
    rw [hW]
    exact Nat.lt_floor_add_one _
  have hbudget : (100000 : ℝ) * d ≤ W := by
    have ha : (d : ℝ) * m ≤ (1 + g / 2) * d * m := by
      nlinarith [mul_nonneg hgpos.le (mul_nonneg hdpos.le hmnonneg)]
    have hmd := mul_le_mul_of_nonneg_left hm hdpos.le
    have hcubic : 100 * (d : ℝ) ^ 3 < (W : ℝ) + 1 := by
      apply (mul_lt_mul_iff_left₀ hHpos).mp
      nlinarith only [ha, hmd, hlower]
    have hsquare : (1000000 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hc := mul_le_mul_of_nonneg_right hsquare hdpos.le
    nlinarith only [hcubic, hc, hdR]
  have hscale : (W : ℝ) / d ≤ 25 / 169 * (g * m) := by
    apply (div_le_iff₀ hdpos).mpr
    have h₁ := mul_le_mul_of_nonneg_left hupper hδ.le
    have h₂ := mul_le_mul_of_nonneg_right hδH hWnonneg
    have h₃ := mul_le_mul_of_nonneg_right hag (mul_nonneg hdpos.le hmnonneg)
    nlinarith only [h₁, h₂, h₃]
  have hmean : simplexWeightedMean W (simplexReciprocalWeights d) = (W : ℝ) * H / d := by
    rw [(band_simplex_moments (W := W) hdN).1, ← hH]
    ring
  have hmeanhi : simplexWeightedMean W (simplexReciprocalWeights d) ≤ (1 + g / 2) * m := by
    rw [hmean]
    apply (div_le_iff₀ hdpos).mpr
    nlinarith only [hupper]
  have hmeanlo : (1 + g / 2) * m - 1 ≤
      simplexWeightedMean W (simplexReciprocalWeights d) := by
    rw [hmean]
    apply (le_div_iff₀ hdpos).mpr
    nlinarith only [hlower, hHd]
  apply asymmetricBand_mass_of_variance (g * m) hs
  · have hfloor := Nat.floor_le (show (0 : ℝ) ≤ (1 - g / 10) * m by
      apply mul_nonneg _ hmnonneg
      linarith)
    have hpred : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hdN
    nlinarith only [hfloor, hpred, hmeanlo, hgm]
  · have hceil := Nat.le_ceil ((1 + 13 * g / 20) * (m : ℝ))
    nlinarith only [hmeanhi, hceil]
  · exact band_finite_variance_bound hdN (g * m) hbudget hscale

end
end ReedSolomon.HiddenDerivative
