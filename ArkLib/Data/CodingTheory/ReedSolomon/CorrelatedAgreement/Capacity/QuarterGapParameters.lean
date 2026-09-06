/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting

/-!
# Finite first-order parameters for the quarter-gap regime

This file verifies the fixed local-rank and column-height inequalities for the order-one
certificate used when the capacity gap lies between one quarter and one half.  The ambient
degree `max k 3 - 1` handles the small message dimensions without assuming it is below `k`.
-/

namespace ReedSolomon

open HiddenDerivative
open scoped BigOperators

set_option maxRecDepth 4096

/-- The unrestricted numerical rank profile dominates every support-cutoff slice rank. -/
private def quarterGapGradedRankBound (t : ℕ) : ℕ :=
  Finset.sum (Finset.range 64) fun s ↦
    min (64 - s) (min t s + 1 - (t - 16))

private theorem firstOrderGradedRankBound_le_quarterGap (D A t : ℕ) :
    firstOrderGradedRankBound D A 64 16 t ≤ quarterGapGradedRankBound t := by
  apply Finset.sum_le_sum
  intro s hs
  apply min_le_min le_rfl
  simp only [firstOrderGradedSourceCount]
  split <;> omega

/-- Total shifted source multiplicity after grouping by total jet grade. -/
private def quarterGapShiftedHeightWeightSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun _ ↦ 1450 - t

/-- Total shifted source grade weighted by its remaining coefficient slots. -/
private def quarterGapShiftedHeightTotalDegreeSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun _ ↦ t * (1450 - t)

/-- Total first-jet exponent contribution within the shifted source slots. -/
private def quarterGapShiftedHeightFirstJetSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun b ↦ b * (1450 - t)

/-- Total unrestricted compressed-row slots with total-grade shifting. -/
private def quarterGapShiftedRowWeightSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    quarterGapGradedRankBound t * (1450 - t)

private theorem quarterGapShiftedHeightWeightSum_eq :
    quarterGapShiftedHeightWeightSum = 2640100 := by decide

private theorem quarterGapShiftedHeightTotalDegreeSum_eq :
    quarterGapShiftedHeightTotalDegreeSum = 165350500 := by decide

private theorem quarterGapShiftedHeightFirstJetSum_eq :
    quarterGapShiftedHeightFirstJetSum = 20532260 := by decide

private theorem quarterGapShiftedRowWeightSum_eq :
    quarterGapShiftedRowWeightSum = 40063696 := by decide

private theorem quarterGap_shiftedHeightSlot_accounting (D A : ℕ) :
    64 * A * 2640100 + 20532260 ≤
      firstOrderCurveShiftedHeightSlotCount D A 64 16 119 1 1449 + D * 165350500 := by
  rw [← quarterGapShiftedHeightWeightSum_eq,
    ← quarterGapShiftedHeightTotalDegreeSum_eq,
    ← quarterGapShiftedHeightFirstJetSum_eq]
  have hleft :
      64 * A * quarterGapShiftedHeightWeightSum + quarterGapShiftedHeightFirstJetSum =
        Finset.sum (Finset.range 120) fun t ↦
          Finset.sum (Finset.range (min t 16 + 1)) fun b ↦
            (64 * A + b) * (1450 - t) := by
    simp only [quarterGapShiftedHeightWeightSum, quarterGapShiftedHeightFirstJetSum,
      Nat.add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hright :
      firstOrderCurveShiftedHeightSlotCount D A 64 16 119 1 1449 +
          D * quarterGapShiftedHeightTotalDegreeSum =
        Finset.sum (Finset.range 120) fun t ↦
          Finset.sum (Finset.range (min t 16 + 1)) fun b ↦
            ((64 * A + b - D * t) * (1450 - t) + D * t * (1450 - t)) := by
    simp only [firstOrderCurveShiftedHeightSlotCount,
      quarterGapShiftedHeightTotalDegreeSum, Nat.reduceAdd, Nat.one_mul, Nat.mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro b hb
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The fixed first-order support has enough finite challenge-height slots throughout the
quarter-gap regime.  The four conclusions are precisely the ambient-degree, positive-budget,
message-degree, and height-slot hypotheses of the finite first-order curve constructor. -/
theorem quarterGap_firstOrderCurve_parameters (δ : ℝ) (n k A : ℕ)
    (hn : 512 ≤ n) (hk : 0 < k) (hkn : k ≤ n) (_hAn : A ≤ n)
    (hδ : (1 / 4 : ℝ) ≤ δ) (_hδhalf : δ < 1 / 2)
    (hgap : (k : ℝ) + δ * n ≤ A) :
    let D := max k 3 - 1
    1 < D ∧ 0 < 64 * A ∧ k ≤ D + 1 ∧
      firstOrderCurveShiftedRowSlotBound D A 64 16 119 n 1 1449 <
        firstOrderCurveShiftedHeightSlotCount D A 64 16 119 1 1449 := by
  dsimp only
  let D := max k 3 - 1
  have hquarterGap : (k : ℝ) + (n : ℝ) / 4 ≤ A := by
    calc
      (k : ℝ) + (n : ℝ) / 4 = k + (1 / 4 : ℝ) * n := by ring
      _ ≤ k + δ * n := by
        gcongr
      _ ≤ A := hgap
  have hfour : n + 4 * k ≤ 4 * A := by
    exact_mod_cast (show (n : ℝ) + 4 * k ≤ 4 * A by nlinarith [hquarterGap])
  have hD : 1 < D := by dsimp only [D]; omega
  have hkD : k ≤ D + 1 := by dsimp only [D]; omega
  have hDk : D ≤ k + 1 := by dsimp only [D]; omega
  have hbudget : 0 < 64 * A := by omega
  refine ⟨hD, hbudget, hkD, ?_⟩
  have hrow' := firstOrderCurveShiftedRowSlotBound_le_of_rankBound
    D A 64 16 119 n 1 1449 quarterGapGradedRankBound
      (firstOrderGradedRankBound_le_quarterGap D A)
  have hrow : firstOrderCurveShiftedRowSlotBound D A 64 16 119 n 1 1449 ≤
      n * 40063696 := by
    calc
      firstOrderCurveShiftedRowSlotBound D A 64 16 119 n 1 1449 ≤
          ∑ t ∈ Finset.range (119 + 1),
            n * quarterGapGradedRankBound t * (1449 + 1 - 1 * t) := hrow'
      _ = n * quarterGapShiftedRowWeightSum := by
        rw [quarterGapShiftedRowWeightSum, show 119 + 1 = 120 by norm_num,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        norm_num only [Nat.reduceAdd, Nat.one_mul]
        ring
      _ = n * 40063696 := by rw [quarterGapShiftedRowWeightSum_eq]
  have haccount := quarterGap_shiftedHeightSlot_accounting D A
  have hstrict :
      n * 40063696 + D * 165350500 < 64 * A * 2640100 + 20532260 := by
    omega
  exact Nat.add_lt_add_iff_right.mp
    ((Nat.add_le_add_right hrow _).trans_lt (hstrict.trans_le haccount))

end ReedSolomon
