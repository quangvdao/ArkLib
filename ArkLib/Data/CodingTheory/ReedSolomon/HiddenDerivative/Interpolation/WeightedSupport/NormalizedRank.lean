/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.RankBound
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Rounding
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.EndpointComparison

/-!
# Assembling the weighted-support rank estimate

The lattice estimate uses the full simplex volume. Three scalar bounds control its error
window, exponential factor, and reciprocal radius factor. Keeping this assembly separate
makes the rounding constants explicit before comparison with the support dimension.
-/

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- Assemble the three scalar factors without introducing a retained-mass denominator. -/
theorem rank_scalar (R g a H E d m κ Be : ℝ)
    (hg : 0 ≤ g) (ha : 0 < a) (hH : 0 < H) (hd : 0 < d)
    (hm : 0 < m) (hk : 0 < κ)
    (hbase : R ≤ Be / m * Real.exp E * (1 / (d * κ ^ 2) + 1 / (m * κ)))
    (hBe : Be ≤ 1541 / 1000 * g * m)
    (he : Real.exp E ≤ 37 / 20 * d ^ (1 / a))
    (hrec : 1 / κ ^ 2 + d / (m * κ) ≤ 101 / 100 * (1 / (H / a) ^ 2)) :
    R ≤ ((1541 / 1000 : ℝ) * (37 / 20) * (101 / 100)) *
      g * a ^ 2 / H ^ 2 * (d ^ (1 / a) / d) := by
  have hwindow : Be / m ≤ 1541 / 1000 * g := (div_le_iff₀ hm).mpr hBe
  have hid : 1 / (d * κ ^ 2) + 1 / (m * κ) =
      (1 / κ ^ 2 + d / (m * κ)) / d := by field_simp
  rw [hid] at hbase
  have hbound : Be / m * Real.exp E * ((1 / κ ^ 2 + d / (m * κ)) / d) ≤
      (1541 / 1000 * g) * (37 / 20 * d ^ (1 / a)) *
        ((101 / 100 * (1 / (H / a) ^ 2)) / d) := by
    apply mul_le_mul
    · exact mul_le_mul hwindow he (Real.exp_pos E).le (by positivity)
    · exact (div_le_div_iff_of_pos_right hd).mpr hrec
    · positivity
    · positivity
  refine hbase.trans (hbound.trans_eq ?_)
  field_simp

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
