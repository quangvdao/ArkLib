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

/-- The exact certified local-rank budget at the fixed quarter-gap parameters. -/
theorem quarterGap_certifiedEnlargedRankBound :
    certifiedEnlargedRankBound 1 64 16 0 = 28152 := by
  rfl

private def quarterGapHeightWeightSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun b ↦ 1450 - (t - b)

private def quarterGapHeightWeightedTotalDegreeSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun b ↦ t * (1450 - (t - b))

private def quarterGapHeightWeightedFirstJetSum : ℕ :=
  Finset.sum (Finset.range 120) fun t ↦
    Finset.sum (Finset.range (min t 16 + 1)) fun b ↦ b * (1450 - (t - b))

private theorem quarterGapHeightWeightSum_eq : quarterGapHeightWeightSum = 2654924 := by
  norm_num [quarterGapHeightWeightSum, Finset.sum_range_succ]

private theorem quarterGapHeightWeightedTotalDegreeSum_eq :
    quarterGapHeightWeightedTotalDegreeSum = 166313040 := by
  norm_num [quarterGapHeightWeightedTotalDegreeSum, Finset.sum_range_succ]

private theorem quarterGapHeightWeightedFirstJetSum_eq :
    quarterGapHeightWeightedFirstJetSum = 20693284 := by
  norm_num [quarterGapHeightWeightedFirstJetSum, Finset.sum_range_succ]

private theorem quarterGap_heightSlot_accounting (D A : ℕ) :
    64 * A * 2654924 + 20693284 ≤
      firstOrderCurveHeightSlotCount D A 64 16 119 1 1449 + D * 166313040 := by
  rw [← quarterGapHeightWeightSum_eq, ← quarterGapHeightWeightedTotalDegreeSum_eq,
    ← quarterGapHeightWeightedFirstJetSum_eq]
  have hleft :
      64 * A * quarterGapHeightWeightSum + quarterGapHeightWeightedFirstJetSum =
        Finset.sum (Finset.range 120) fun t ↦
          Finset.sum (Finset.range (min t 16 + 1)) fun b ↦
            (64 * A + b) * (1450 - (t - b)) := by
    simp only [quarterGapHeightWeightSum, quarterGapHeightWeightedFirstJetSum,
      Nat.add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hright :
      firstOrderCurveHeightSlotCount D A 64 16 119 1 1449 +
          D * quarterGapHeightWeightedTotalDegreeSum =
        Finset.sum (Finset.range 120) fun t ↦
          Finset.sum (Finset.range (min t 16 + 1)) fun b ↦
            ((64 * A + b - D * t) * (1450 - (t - b)) +
              D * t * (1450 - (t - b))) := by
    simp only [firstOrderCurveHeightSlotCount, quarterGapHeightWeightedTotalDegreeSum,
      Nat.reduceAdd, Nat.one_mul, Nat.mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
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
      n * certifiedEnlargedRankBound 1 64 16 0 * (1449 + 1) <
        firstOrderCurveHeightSlotCount D A 64 16 119 1 1449 := by
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
  have haccount := quarterGap_heightSlot_accounting D A
  have hstrict :
      n * 28152 * 1450 + D * 166313040 < 64 * A * 2654924 + 20693284 := by
    omega
  rw [quarterGap_certifiedEnlargedRankBound]
  norm_num only [Nat.reduceAdd]
  exact Nat.add_lt_add_iff_right.mp (hstrict.trans_le haccount)

end ReedSolomon
