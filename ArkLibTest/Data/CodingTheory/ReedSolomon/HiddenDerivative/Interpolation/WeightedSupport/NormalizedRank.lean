/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.NormalizedRank

/-!
# Acceptance clients for the weighted residual rank integral

These checks cover the empty contact sum and the smallest supported derivative order.  The latter
exercises the natural subtraction `d - 1`, the triangular cube enlargement, the harmonic mean,
the variance correction, and the extra unit from the integer ceiling.
-/

open SimplexIntegration

namespace ReedSolomon.HiddenDerivative

example (d W : ℕ) (T : ℝ) : localResidualCoordinateBudget d 0 W T = 0 := by
  simp [localResidualCoordinateBudget]

example :
    (∫ u, (weightedRadius u -
        (2 : ℝ) * harmonicPowerSum (2 - 1) 1 / 2) ^ 2
      ∂(weightedSimplexProbabilityMeasure (2 - 1) 2 :
        MeasureTheory.Measure (Fin (2 - 1) → ℝ))) ≤
      (2 : ℝ) ^ 2 * harmonicPowerSum (2 - 1) 2 / (2 * (2 + 1)) := by
  exact weightedSimplex_centeredRadius_sq_le_harmonic 2 (by omega) (by norm_num)

example :
    (localResidualCoordinateBudget 2 1 1 1 : ℝ) ≤
      (9 / 2 : ℝ) * Real.exp 2 := by
  have h := localResidualCoordinateBudget_le_weighted_integral_geometric
    2 1 1 1 1 3 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
    (by
      intro r hr
      have : r = 0 := by simpa using hr
      subst r
      norm_num [harmonicPowerSum_eq_range])
    (by
      intro r hr
      have : r = 0 := by simpa using hr
      subst r
      norm_num [harmonicPowerSum_eq_range])
  norm_num at h ⊢
  nlinarith [h]

end ReedSolomon.HiddenDerivative
