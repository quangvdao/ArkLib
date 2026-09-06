/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.RankBudget

/-!
# Volume-normalized rank of the weighted support

The lattice bound uses the full weighted simplex volume, rather than the cardinality of a
retained band. Dividing the local coordinate count by this volume and by `m³` leaves the
first-derivative slot factor and the two reciprocal geometric-series terms. The dimension
proof will use this same normalization, so no retained-mass denominator is needed.
-/

namespace ReedSolomon.HiddenDerivative

/-- The actual local rank obeys the volume-normalized coordinate bound over every field. -/
theorem finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
    {F : Type*} [Field F] {d D m W Cmin : ℕ} {L : ℝ}
    (hd : 2 ≤ d) (hD : 0 < D) (hm : 0 < m) (hW : 0 < W)
    (center received : F) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (Cmin := Cmin) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) ≤
      ((⌈L / D - Cmin⌉₊ : ℝ) / m) * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  have h := finrank_weightedSupportLocalConstraint_le (d := d) (m := m) (W := W)
    (Cmin := Cmin) (L := L) (by omega) hD center received
  have hcast : (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (Cmin := Cmin) (L := L)
        m hD center received)) : ℝ) ≤ localCoordinateBudget d m W ⌈L / D - Cmin⌉₊ := by
    exact_mod_cast h
  exact (div_le_div_of_nonneg_right hcast (by positivity)).trans
    (localCoordinateBudget_div_volume_mul_cube_le d m W ⌈L / D - Cmin⌉₊ hd hm hW)

end ReedSolomon.HiddenDerivative
