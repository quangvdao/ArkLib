/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexBandCounting


/-!
# Exact finite Cantelli bounds for asymmetric bands

The shifted-square argument bounds each one-sided tail using the exact discrete variance.
Distinct left and right margins give a central event that transports through the quotient
fiber bound. Zero variance is allowed; only the margins must be positive.
-/

open PolynomialDifferential


open DiscreteSimplex

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- One-sided Cantelli, with `sign = 1` for the upper tail and `sign = -1` for the lower.
The variance may vanish: the shifted square never divides by it. -/
theorem simplex_cantelli_tail_count {r S : ℕ} (w : Fin r → ℝ)
    (t : ℝ) (ht : 0 < t) (sign : ℝ) (hsign : sign ^ 2 = 1)
    (tail : Finset (OrdinarySimplex r S))
    (hTail : ∀ u ∈ tail,
      t ≤ sign * (simplexWeightedStatistic w u - simplexWeightedMean S w)) :
    (tail.card : ℝ) ≤ Fintype.card (OrdinarySimplex r S) *
      (simplexWeightedVariance S w / (simplexWeightedVariance S w + t ^ 2)) := by
  let V := simplexWeightedVariance S w
  let Y := fun u : OrdinarySimplex r S ↦ simplexWeightedStatistic w u - simplexWeightedMean S w
  let C : ℝ := Fintype.card (OrdinarySimplex r S)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  have hV : 0 ≤ V := simplexWeightedVariance_nonneg S w
  have hden : 0 < V + t ^ 2 := by positivity
  have hMean := simplex_average_weighted (S := S) w
  unfold simplexAverage at hMean
  have hFirst : ∑ u, Y u = 0 := by
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h := (div_eq_iff hC).mp hMean
    change _ - C * simplexWeightedMean S w = 0
    linarith
  have hSecond : ∑ u, Y u ^ 2 = C * V := by
    have h := simplex_average_centered_square (S := S) w
    unfold simplexAverage at h
    simpa [Y, C, V, mul_comm] using (div_eq_iff hC).mp h
  have hShift : ∑ u, (t * sign * Y u + V) ^ 2 = C * V * (V + t ^ 2) := by
    calc
      _ = ∑ u, (t ^ 2 * Y u ^ 2 + (2 * t * sign * V) * Y u + V ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        nlinarith [congrArg (fun a : ℝ ↦ t ^ 2 * Y u ^ 2 * a) hsign]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hFirst, hSecond]
        simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change t ^ 2 * (C * V) + C * V ^ 2 = _
        ring
  have hBound : (V + t ^ 2) ^ 2 * (tail.card : ℝ) ≤ C * V * (V + t ^ 2) := by
    calc
      _ = ∑ _u ∈ tail, (V + t ^ 2) ^ 2 := by simp [mul_comm]
      _ ≤ ∑ u ∈ tail, (t * sign * Y u + V) ^ 2 := by
        apply Finset.sum_le_sum
        intro u hu
        have h := mul_le_mul_of_nonneg_left (hTail u hu) ht.le
        change t * t ≤ t * (sign * Y u) at h
        nlinarith [sq_nonneg (t * sign * Y u + V - (V + t ^ 2))]
      _ ≤ ∑ u, (t * sign * Y u + V) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
      _ = _ := hShift
  have hCancel : (tail.card : ℝ) * (V + t ^ 2) ≤ C * V := by
    apply (mul_le_mul_iff_left₀ hden).mp
    nlinarith only [hBound]
  change _ ≤ C * (V / (V + t ^ 2))
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hden).mpr hCancel

/-- Distinct positive margins allow different Cantelli losses on the two sides. -/
theorem simplex_asymmetric_central_event_count {r S : ℕ} (w : Fin r → ℝ)
    (left right : ℝ) (hleft : 0 < left) (hright : 0 < right) :
    (Fintype.card (OrdinarySimplex r S) : ℝ) *
        (1 - simplexWeightedVariance S w / (simplexWeightedVariance S w + left ^ 2) -
          simplexWeightedVariance S w / (simplexWeightedVariance S w + right ^ 2)) ≤
      ((Finset.univ.filter fun u : OrdinarySimplex r S ↦
        -left < simplexWeightedStatistic w u - simplexWeightedMean S w ∧
          simplexWeightedStatistic w u - simplexWeightedMean S w < right).card : ℝ) := by
  classical
  let Y := fun u : OrdinarySimplex r S ↦ simplexWeightedStatistic w u - simplexWeightedMean S w
  let good := Finset.univ.filter fun u ↦ -left < Y u ∧ Y u < right
  let lower := Finset.univ.filter fun u ↦ Y u ≤ -left
  let upper := Finset.univ.filter fun u ↦ right ≤ Y u
  have hl := simplex_cantelli_tail_count (S := S) w left hleft (-1) (by norm_num) lower
    (fun u hu ↦ by
      have h : Y u ≤ -left := (Finset.mem_filter.mp hu).2
      change left ≤ -1 * Y u
      linarith)
  have hr := simplex_cantelli_tail_count (S := S) w right hright 1 (by norm_num) upper
    (fun u hu ↦ by simpa only [one_mul] using (Finset.mem_filter.mp hu).2)
  have hcover : Finset.univ ⊆ (good ∪ lower) ∪ upper := by
    intro u _
    by_cases hl : -left < Y u
    · by_cases hr : Y u < right
      · simp only [Finset.mem_union]
        exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hr⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, le_of_not_gt hr⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hl⟩))))
  have hcard : Fintype.card (OrdinarySimplex r S) ≤ good.card + lower.card + upper.card := by
    calc
      _ ≤ ((good ∪ lower) ∪ upper).card := Finset.card_le_card hcover
      _ ≤ (good ∪ lower).card + upper.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hcard' : (Fintype.card (OrdinarySimplex r S) : ℝ) ≤
      good.card + lower.card + upper.card := by exact_mod_cast hcard
  change _ ≤ (good.card : ℝ)
  nlinarith

/-- Cantelli concentration followed by the actual quotient/remainder fiber bound.
The lower margin includes rounding loss; the variance is the exact finite-simplex formula. -/
theorem asymmetricBand_card_lower_of_simplex_cantelli {d W Cmin Cmax : ℕ}
    (left right : ℝ) (hleft : 0 < left) (hright : 0 < right)
    (hlo : (Cmin : ℝ) + (d - 1 : ℕ) ≤
      simplexWeightedMean W (simplexReciprocalWeights d) - left)
    (hhi : simplexWeightedMean W (simplexReciprocalWeights d) + right ≤ Cmax) :
    (Fintype.card (OrdinarySimplex (d - 1) W) : ℝ) *
        (1 - simplexWeightedVariance W (simplexReciprocalWeights d) /
          (simplexWeightedVariance W (simplexReciprocalWeights d) + left ^ 2) -
          simplexWeightedVariance W (simplexReciprocalWeights d) /
          (simplexWeightedVariance W (simplexReciprocalWeights d) + right ^ 2)) ≤
      ((asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial : ℕ) := by
  let event := Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
    -left < simplexWeightedStatistic (simplexReciprocalWeights d) u -
        simplexWeightedMean W (simplexReciprocalWeights d) ∧
      simplexWeightedStatistic (simplexReciprocalWeights d) u -
        simplexWeightedMean W (simplexReciprocalWeights d) < right
  have hcard := simplex_event_card_le_band_mul_factorial (Cmin := Cmin) (Cmax := Cmax)
    event (fun u hu ↦ by
      have h := (Finset.mem_filter.mp hu).2.1
      linarith) (fun u hu ↦ by
      have h := (Finset.mem_filter.mp hu).2.2
      linarith)
  have hcard' : (event.card : ℝ) ≤
      ((asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial : ℕ) := by
    exact_mod_cast hcard
  exact (simplex_asymmetric_central_event_count (S := W) (simplexReciprocalWeights d)
    left right hleft hright).trans hcard'


end
end ReedSolomon.HiddenDerivative
