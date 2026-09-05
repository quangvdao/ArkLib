/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Elementary budgets for correlated-agreement charts

The midpoint threshold supplies two positive agreement gaps. The primary bound retains the
actual stage order; only the final uniform bound replaces it by an ambient order.
-/

namespace ReedSolomon

open scoped BigOperators

/-- Midpoint between the message dimension and the guaranteed agreement threshold. -/
noncomputable def correlatedMidpoint (δ : ℝ) (n k : ℕ) : ℕ :=
  k + ⌊δ * n / 2⌋₊

/-- Both integer agreement gaps retain half the real margin, including subunit margins. -/
theorem correlatedMidpoint_bounds (δ : ℝ) (n k A : ℕ)
    (hδ : 0 ≤ δ) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    k ≤ correlatedMidpoint δ n k ∧ correlatedMidpoint δ n k ≤ A ∧
      correlatedMidpoint δ n k ≤ n ∧
      δ * n / 2 ≤ ((A - correlatedMidpoint δ n k + 1 : ℕ) : ℝ) ∧
      δ * n / 2 ≤ ((correlatedMidpoint δ n k - k + 1 : ℕ) : ℝ) := by
  have hx : 0 ≤ δ * n / 2 := by positivity
  have hf := Nat.floor_le hx
  have hf' := Nat.lt_floor_add_one (δ * n / 2)
  have hkL : k ≤ correlatedMidpoint δ n k := Nat.le_add_right _ _
  have hLA : correlatedMidpoint δ n k ≤ A := by
    unfold correlatedMidpoint
    exact_mod_cast (show (k : ℝ) + ⌊δ * n / 2⌋₊ ≤ A by linarith)
  refine ⟨hkL, hLA, hLA.trans hAn, ?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_sub hLA, Nat.cast_one]
    unfold correlatedMidpoint
    push_cast
    linarith
  · rw [Nat.cast_add, Nat.cast_sub hkL, Nat.cast_one]
    unfold correlatedMidpoint
    push_cast
    linarith

/-- A convenient common prefactor for the ordinary and joint cut degrees. -/
noncomputable def correlatedChartScale (δ : ℝ) (v h : ℕ) : ℝ :=
  2 * (1 + 2 * ((v : ℝ) + h)) / δ

/-- The numerator degree budget is linear in block length whenever the Taylor cap is. -/
theorem correlatedCutDegree_le (n K v h : ℕ) (hn : 0 < n) (hKn : K ≤ n) :
    (1 + 2 * K * (v - 1 + h) : ℕ) ≤ n * (1 + 2 * (v + h)) := by
  have hv : v - 1 + h ≤ v + h := Nat.add_le_add_right (Nat.sub_le _ _) _
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hKn) hv
  nlinarith

/-- Dividing either cut budget by a half-margin leaves one power of block length. -/
theorem correlatedCutRatio_le (δ : ℝ) (n K v h D : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hD : δ * n / 2 ≤ (D : ℝ)) :
    ((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℝ) / D ≤
      correlatedChartScale δ v h * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  have hb : ((1 + 2 * K * (v - 1 + h) : ℕ) : ℝ) ≤
      n * (1 + 2 * ((v : ℝ) + h)) := by
    exact_mod_cast correlatedCutDegree_le n K v h hn hKn
  have hc : 0 ≤ correlatedChartScale δ v h := by
    unfold correlatedChartScale
    positivity
  apply (div_le_iff₀ hDpos).mpr
  have hm := mul_le_mul_of_nonneg_left hD (mul_nonneg hc hn'.le)
  have he : correlatedChartScale δ v h * n * (δ * n / 2) =
      (n : ℝ) * (n * (1 + 2 * ((v : ℝ) + h))) := by
    unfold correlatedChartScale
    field_simp
  rw [he] at hm
  apply le_trans ?_ hm
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hb hn'.le

/-- The primary stage budget retains the actual order `r` and the exact accidental factor. -/
theorem correlated_actualOrder_budget (δ : ℝ) (n K k A v h r : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let L := correlatedMidpoint δ n k
    let c := correlatedChartScale δ v h
    ((v + h : ℕ) : ℝ) *
        (((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℝ) / ((A - L + 1 : ℕ) : ℝ)) ^ (r + 1) +
      ((n - L : ℕ) : ℝ) * v *
        (((n * (1 + 2 * K * (v - 1)) : ℕ) : ℝ) / ((L - k + 1 : ℕ) : ℝ)) ^ r ≤
      (((v + h : ℕ) : ℝ) * c ^ (r + 1) + v * c ^ r) * (n : ℝ) ^ (r + 1) := by
  dsimp only
  let L := correlatedMidpoint δ n k
  let c := correlatedChartScale δ v h
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have ho := correlatedCutRatio_le δ n K v h (A - L + 1) hδ hn hKn hL.2.2.2.1
  have hp₀ := correlatedCutRatio_le δ n K v 0 (L - k + 1) hδ hn hKn hL.2.2.2.2
  have hc : 0 ≤ c := by dsimp [c, correlatedChartScale]; positivity
  have hscale : correlatedChartScale δ v 0 ≤ c := by
    unfold c correlatedChartScale
    apply div_le_div_of_nonneg_right _ hδ.le
    simp only [Nat.cast_zero, add_zero]
    linarith [Nat.cast_nonneg h (α := ℝ)]
  have hp : (((n * (1 + 2 * K * (v - 1)) : ℕ) : ℝ) /
      ((L - k + 1 : ℕ) : ℝ)) ≤ c * n := by
    simpa only [Nat.add_zero] using hp₀.trans
      (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n))
  have ho' := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) ho (r + 1)) (Nat.cast_nonneg (v + h) : (0 : ℝ) ≤ _)
  have hp' := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hp r)
    (show (0 : ℝ) ≤ ((n - L : ℕ) : ℝ) * v by positivity)
  have hnl : ((n - L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n L
  have hp'' := mul_le_mul_of_nonneg_right hnl
    (show (0 : ℝ) ≤ (v : ℝ) * (c * n) ^ r by positivity)
  calc
    _ ≤ ((v + h : ℕ) : ℝ) * (c * n) ^ (r + 1) +
        ((n - L : ℕ) : ℝ) * v * (c * n) ^ r := add_le_add ho' hp'
    _ ≤ ((v + h : ℕ) : ℝ) * (c * n) ^ (r + 1) +
        (n : ℝ) * v * (c * n) ^ r := by nlinarith only [hp'']
    _ = _ := by simp only [mul_pow, pow_succ]; ring

/-- Uniformization is isolated here: an actual stage order at most `d` may be replaced
by the ambient exponent using block length at least one. -/
theorem correlated_order_uniform_budget (δ : ℝ) (n v h r d : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hr : r ≤ d) :
    (((v + h : ℕ) : ℝ) * correlatedChartScale δ v h ^ (r + 1) +
      v * correlatedChartScale δ v h ^ r) * (n : ℝ) ^ (r + 1) ≤
      ((2 * v + h : ℕ) : ℝ) * (max 1 (correlatedChartScale δ v h)) ^ (d + 1) *
        (n : ℝ) ^ (d + 1) := by
  let c := correlatedChartScale δ v h
  let C := max 1 c
  have hc : 0 ≤ c := by dsimp [c, correlatedChartScale]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hp (j : ℕ) (hj : j ≤ d + 1) : c ^ j ≤ C ^ (d + 1) :=
    (pow_le_pow_left₀ hc (le_max_right _ _) j).trans (pow_le_pow_right₀ hC hj)
  have hv := mul_le_mul_of_nonneg_left (hp (r + 1) (Nat.add_le_add_right hr 1))
    (Nat.cast_nonneg (v + h) : (0 : ℝ) ≤ _)
  have hv' := mul_le_mul_of_nonneg_left (hp r (hr.trans (Nat.le_succ d)))
    (Nat.cast_nonneg v : (0 : ℝ) ≤ _)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp := pow_le_pow_right₀ hn' (Nat.add_le_add_right hr 1)
  apply mul_le_mul _ hnp (by positivity) (by positivity)
  dsimp only [C, c] at hv hv'
  push_cast at hv ⊢
  nlinarith only [hv, hv']

/-- A finite stage family is summed only after preserving its individual order bounds.
The terminal exceptional challenge budget is absorbed using `n ≥ 1`. -/
theorem correlated_finiteStage_budget {ι : Type*} (S : Finset ι)
    (order : ι → ℕ) (cost : ι → ℝ) (δ : ℝ) (n v h d ν : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hcard : S.card ≤ ν)
    (horder : ∀ i ∈ S, order i ≤ d)
    (hcost : ∀ i ∈ S, cost i ≤
      (((v + h : ℕ) : ℝ) * correlatedChartScale δ v h ^ (order i + 1) +
        v * correlatedChartScale δ v h ^ order i) * (n : ℝ) ^ (order i + 1)) :
    (h : ℝ) + ∑ i ∈ S, cost i ≤
      ((h : ℝ) + ν * (2 * v + h) *
        (max 1 (correlatedChartScale δ v h)) ^ (d + 1)) * (n : ℝ) ^ (d + 1) := by
  let B : ℝ := ((2 * v + h : ℕ) : ℝ) *
    (max 1 (correlatedChartScale δ v h)) ^ (d + 1) * (n : ℝ) ^ (d + 1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : ∑ i ∈ S, cost i ≤ (S.card : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum fun i hi ↦
        (hcost i hi).trans (correlated_order_uniform_budget δ n v h (order i) d
          hδ hn (horder i hi))
      _ = _ := by simp
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right
    (show (S.card : ℝ) ≤ ν by exact_mod_cast hcard) hB)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterminal := mul_le_mul_of_nonneg_left (one_le_pow₀ hn' (n := d + 1))
    (Nat.cast_nonneg h : (0 : ℝ) ≤ _)
  have ht : (h : ℝ) ≤ h * (n : ℝ) ^ (d + 1) := by simpa using hterminal
  calc
    _ ≤ (h : ℝ) * (n : ℝ) ^ (d + 1) + ν * B := add_le_add ht hsum'
    _ = _ := by dsimp only [B]; push_cast; ring

end ReedSolomon
