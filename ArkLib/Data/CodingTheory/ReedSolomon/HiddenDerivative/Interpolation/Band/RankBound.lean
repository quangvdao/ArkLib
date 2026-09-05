/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Lattice.ScaledLattice
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp


/-!
# Finite weighted upper bounds for the asymmetric-band rank budget

This follows equations `band-lattice-ratio` and `band-geometric-rank` of [DKTZ26].
The lattice estimate reuses the proved integer sandwich. The `T`-degree dependence is
retained through the finite sum; no concentration or asymptotic premise is assumed.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26]
-/

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- The ceiling in the local contact count is bounded with its full additive error. -/
theorem band_ceilDiv_le (d j : ℕ) (hd : 0 < d) :
    ((j ⌈/⌉ (d + 1) : ℕ) : ℝ) ≤ (j : ℝ) / d + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have heq : j + (d + 1) - 1 = j + d := by omega
  rw [heq]
  have hcast : (((j + d) / (d + 1) : ℕ) : ℝ) ≤ (j + d : ℕ) / (d + 1 : ℕ) :=
    Nat.cast_div_le
  apply hcast.trans
  push_cast
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hdiv : (0 : ℝ) ≤ (j : ℝ) / d := div_nonneg hj hd'.le
  have heq' : (j : ℝ) / d * d = j := div_mul_cancel₀ _ hd'.ne'
  nlinarith

/-- The exact shifted geometric sum bounds every finite initial segment. -/
theorem band_geometric_sum_le (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ Finset.range m, q ^ (j + 1)) ≤ q / (1 - q) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hs := (hasSum_geometric_of_norm_lt_one hnorm).mul_left q
  have hs' : HasSum (fun j : ℕ ↦ q ^ (j + 1)) (q / (1 - q)) := by
    simpa [pow_succ, mul_comm, div_eq_mul_inv] using hs
  rw [← hs'.tsum_eq]
  exact hs'.summable.sum_le_tsum _ (fun j hj ↦ pow_nonneg hq0 _)

/-- The weighted geometric identity retains the saving from the distance to `m`. -/
theorem band_weighted_geometric_sum_le (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * q ^ (j + 1)) ≤ q / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have h := hs.summable.sum_le_tsum (Finset.range (m + 1))
    (fun j hj ↦ mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hq0 j))
  rw [hs.tsum_eq] at h
  rw [Finset.sum_range_succ'] at h
  simpa using h

/-- Combining the two geometric sums, with the ceiling's additive error still visible. -/
theorem band_linear_geometric_sum_le (d m : ℕ) (hd : 0 < d)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ) / d + 1) * q ^ (j + 1)) ≤
      q / ((d : ℝ) * (1 - q) ^ 2) + q / (1 - q) := by
  have hD : (0 : ℝ) ≤ d := (Nat.cast_pos.mpr hd).le
  have h := add_le_add
    (div_le_div_of_nonneg_right (band_weighted_geometric_sum_le m hq0 hq1) hD)
    (band_geometric_sum_le m hq0 hq1)
  simp_rw [add_mul, one_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
    ← Finset.sum_div]
  simpa only [div_div, mul_comm] using h

/-- The unweighted exponential tail is at most `1/x`. -/
theorem band_exp_geometric_ratio_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ≤ 1 / x := by
  have hq : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he := Real.add_one_le_exp x
  have hid : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_pos (-x)).le
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-x)) hx).mpr
  nlinarith

/-- The weighted exponential tail is at most `1/x²`, using the elementary sinh inequality. -/
theorem band_exp_weighted_geometric_ratio_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 ≤ 1 / x ^ 2 := by
  have hq : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hs := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ x / 2)
  rw [Real.sinh_eq] at hs
  have hab : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hb : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(x / 2))).le
  have hlinear : x * Real.exp (-(x / 2)) ≤ 1 - Real.exp (-x) := by nlinarith
  have hnonneg : 0 ≤ x * Real.exp (-(x / 2)) := by positivity
  have hsq := pow_le_pow_left₀ hnonneg hlinear 2
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - Real.exp (-x)))
    (sq_pos_of_pos hx)).mpr
  nlinarith

/-- Smooth version of the finite linear-geometric estimate used by the manuscript. -/
theorem band_linear_exp_sum_le (d m : ℕ) (hd : 0 < d) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ Finset.range m,
      (((j + 1 : ℕ) : ℝ) / d + 1) * Real.exp (-x) ^ (j + 1)) ≤
        1 / ((d : ℝ) * x ^ 2) + 1 / x := by
  have hq : Real.exp (-x) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  apply (band_linear_geometric_sum_le d m hd (Real.exp_pos _).le hq).trans
  have h := add_le_add
    (div_le_div_of_nonneg_right (band_exp_weighted_geometric_ratio_le hx)
      (Nat.cast_nonneg d)) (band_exp_geometric_ratio_le hx)
  simpa only [div_div, mul_comm] using h

/-- Exponential upper envelope of the proved lattice sandwich, keeping the offset `choose d 2`. -/
theorem band_weightedHigherJetCount_le_exp (d W r : ℕ) (hW : 0 < W) :
    (weightedHigherJetCount d (W + r) : ℝ) ≤
      (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2)) := by
  have h := scaledExponentCount_mul_factorial_sq_le_pow d (W + r)
  rw [scaledExponentCount_eq_weightedHigherJetCount, ← Nat.choose_two_right] at h
  have hnat : (weightedHigherJetCount d (W + r) : ℝ) * ((d - 1).factorial : ℝ) ^ 2 ≤
      ((W : ℝ) + r + d.choose 2) ^ (d - 1) := by exact_mod_cast h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have he := Real.add_one_le_exp (((r : ℝ) + d.choose 2) / W)
  have he' := mul_le_mul_of_nonneg_left he hW'.le
  have hbase : (W : ℝ) + r + d.choose 2 ≤
      W * Real.exp (((r : ℝ) + d.choose 2) / W) := by
    have heq : (W : ℝ) * (((r : ℝ) + d.choose 2) / W + 1) = W + r + d.choose 2 := by
      field_simp
      ring
    rwa [heq] at he'
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ W + r + d.choose 2)
    hbase (d - 1)
  have hp' : ((W : ℝ) + r + d.choose 2) ^ (d - 1) ≤
      (W : ℝ) ^ (d - 1) *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2)) := by
    calc
      _ ≤ (W * Real.exp (((r : ℝ) + d.choose 2) / W)) ^ (d - 1) := hp
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hfac : (0 : ℝ) < ((d - 1).factorial : ℝ) ^ 2 := by positivity
  calc
    _ ≤ ((W : ℝ) ^ (d - 1) *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2))) /
          ((d - 1).factorial : ℝ) ^ 2 := (le_div_iff₀ hfac).mpr (hnat.trans hp')
    _ = _ := by ring

/-- Finite contact sum with its `T`-degree dependence and offset retained until reindexing. -/
theorem band_contact_exp_sum_le (d m : ℕ) (hd : 0 < d) {x B : ℝ} (hx : 0 < x) :
    (∑ r ∈ Finset.range m,
      ((m - r) ⌈/⌉ (d + 1) : ℕ) * Real.exp (x * (r + B))) ≤
        Real.exp (x * (m + B)) * (1 / ((d : ℝ) * x ^ 2) + 1 / x) := by
  rw [← Finset.sum_range_reflect
    (fun r ↦ (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) * Real.exp (x * (r + B))) m]
  have hterm : ∀ j ∈ Finset.range m,
      (((m - (m - 1 - j)) ⌈/⌉ (d + 1) : ℕ) : ℝ) *
          Real.exp (x * ((m - 1 - j : ℕ) + B)) ≤
        Real.exp (x * (m + B)) *
          ((((j + 1 : ℕ) : ℝ) / d + 1) * Real.exp (-x) ^ (j + 1)) := by
    intro j hj
    have hjm := Finset.mem_range.mp hj
    have heq : m - (m - 1 - j) = j + 1 := by omega
    have hadd : m - 1 - j + (j + 1) = m := by omega
    have hcast : ((m - 1 - j : ℕ) : ℝ) + (j + 1 : ℕ) = m := by exact_mod_cast hadd
    have hexp : Real.exp (x * ((m - 1 - j : ℕ) + B)) =
        Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast at hcast ⊢
      nlinarith
    rw [heq, hexp]
    have h := mul_le_mul_of_nonneg_right (band_ceilDiv_le d (j + 1) hd)
      (by positivity : 0 ≤ Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (band_linear_exp_sum_le d m hd hx)
    (Real.exp_pos _).le)

/-- Absolute upper bound for the actual band's numerical rank budget.
For `x=(d-1)/W`, this is the manuscript's geometric estimate before dividing by band size. -/
theorem asymmetricBandLocalBudget_le_geometric (d m W Be : ℕ)
    (hd : 2 ≤ d) (hW : 0 < W) :
    (asymmetricBandLocalBudget d m W Be : ℝ) ≤
      Be * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp ((((d - 1 : ℕ) : ℝ) / W) * (m + d.choose 2)) *
          (1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) +
            1 / (((d - 1 : ℕ) : ℝ) / W)) := by
  let x : ℝ := ((d - 1 : ℕ) : ℝ) / W
  let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
  have hx : 0 < x := div_pos (by exact_mod_cast (show 0 < d - 1 by omega))
    (by exact_mod_cast hW)
  have hV : 0 ≤ V := by positivity
  have hsum : (∑ r ∈ Finset.range m,
      (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) * weightedHigherJetCount d (W + r)) ≤
        V * ∑ r ∈ Finset.range m,
          (((m - r) ⌈/⌉ (d + 1) : ℕ) : ℝ) * Real.exp (x * (r + d.choose 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have h := mul_le_mul_of_nonneg_left (band_weightedHigherJetCount_le_exp d W r hW)
      (Nat.cast_nonneg ((m - r) ⌈/⌉ (d + 1)))
    simpa [V, x, mul_assoc, mul_left_comm, mul_comm] using h
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left
    (band_contact_exp_sum_le d m (by omega) (B := (d.choose 2 : ℝ)) hx) hV)
  have h := mul_le_mul_of_nonneg_left hsum' (Nat.cast_nonneg Be)
  simpa [asymmetricBandLocalBudget, Nat.cast_sum, Nat.cast_mul, V, x, mul_assoc] using h

/-- The geometric budget bound in the manuscript's `κ=(d-1)m/W` notation.
The `choose d 2 / m` offset and both reciprocal error terms remain explicit. -/
theorem asymmetricBandLocalBudget_le_kappa (d m W Be : ℕ)
    (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W) :
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (asymmetricBandLocalBudget d m W Be : ℝ) ≤
      Be * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
          ((m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ) := by
  dsimp only
  have h := asymmetricBandLocalBudget_le_geometric d m W Be hd hW
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hk' : ((d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show d - 1 ≠ 0 by omega)
  have hexp : (((d - 1 : ℕ) : ℝ) / W) * (m + d.choose 2) =
      (((d - 1 : ℕ) : ℝ) * m / W) * (1 + (d.choose 2 : ℝ) / m) := by
    field_simp
  have hrecip : 1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) +
      1 / (((d - 1 : ℕ) : ℝ) / W) =
        (m : ℝ) ^ 2 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) * m / W) ^ 2) +
          m / (((d - 1 : ℕ) : ℝ) * m / W) := by
    field_simp
  rw [hexp, hrecip] at h
  exact h

end ReedSolomon.HiddenDerivative
