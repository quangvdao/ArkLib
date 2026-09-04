/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AdaptiveAmbientPadding
import Mathlib.Tactic.NormNum

/-!
# Canaries for adaptive ambient padding

These exact examples exercise both branches of the maximum, tightness at the top feasible rate,
nonintegral ceiling behavior, and the finite-size condition needed for the uniform ratio.
-/

namespace ReedSolomon
namespace AllRateListDecoding

noncomputable section

/-- At zero rate, the adaptive padding branch supplies the ambient dimension. -/
lemma adaptive_zero_rate_canary :
    adaptiveBaseRate (1 / 2 : ℝ) = 1 / 8 ∧
      adaptivePadding (1 / 2 : ℝ) 16 = 2 ∧
      adaptiveAmbientDimension (1 / 2 : ℝ) 16 0 = 2 ∧
      agreementThreshold (1 / 2 : ℝ) 16 0 = 8 ∧
      adaptiveAmbientRate (1 / 2 : ℝ) 16 0 = 1 / 8 ∧
      adaptiveAgreementFactor (1 / 2 : ℝ) = 2 ∧
      (agreementThreshold (1 / 2 : ℝ) 16 0 : ℝ) /
          adaptiveAmbientDimension (1 / 2 : ℝ) 16 0 = 4 := by
  norm_num [adaptiveBaseRate, adaptivePadding, adaptiveAmbientDimension, adaptiveAmbientRate,
    adaptiveAgreementFactor, agreementThreshold]

/-- At the top feasible rate, the message branch supplies `K` and the uniform ratio is tight. -/
lemma adaptive_top_rate_canary :
    adaptivePadding (1 / 2 : ℝ) 16 = 2 ∧
      adaptiveAmbientDimension (1 / 2 : ℝ) 16 8 = 8 ∧
      adaptiveAmbientDegree (1 / 2 : ℝ) 16 8 = 7 ∧
      agreementThreshold (1 / 2 : ℝ) 16 8 = 16 ∧
      (agreementThreshold (1 / 2 : ℝ) 16 8 : ℝ) /
          adaptiveAmbientDimension (1 / 2 : ℝ) 16 8 =
        adaptiveAgreementFactor (1 / 2 : ℝ) := by
  norm_num [adaptiveBaseRate, adaptivePadding, adaptiveAmbientDimension, adaptiveAmbientDegree,
    adaptiveAgreementFactor, agreementThreshold]

/-- A nonintegral example detects replacing the adaptive ceiling with a floor. -/
lemma adaptive_nonintegral_ceiling_canary :
    adaptiveBaseRate (1 / 2 : ℝ) * 10 = 5 / 4 ∧
      adaptivePadding (1 / 2 : ℝ) 10 = 2 := by
  have hCeil : Nat.ceil ((5 : ℝ) / 4) = 2 := by
    norm_num [Nat.ceil_eq_iff]
  norm_num [adaptiveBaseRate, adaptivePadding, hCeil]

/-- The bundled geometry theorem covers both branches of the adaptive maximum. -/
lemma adaptive_geometry_branches_canary :
    AdaptiveAmbientGeometry (1 / 2 : ℝ) 16 0 ∧
      AdaptiveAmbientGeometry (1 / 2 : ℝ) 16 8 := by
  constructor <;> apply adaptiveAmbientGeometry <;> norm_num [adaptiveBaseRate]

/-- The separate order threshold places a concrete derivative order below `D = K - 1`. -/
lemma adaptive_order_canary :
    1 < adaptiveAmbientDegree (1 / 2 : ℝ) 32 0 := by
  apply derivOrder_lt_adaptiveAmbientDegree
  norm_num [adaptiveBaseRate]

/-- Without `1 ≤ rho₀ * n`, rounding can destroy the uniform ratio: here `A / K = 1`, while the
claimed rate-independent factor would be `2`. -/
lemma adaptive_tiny_block_ratio_counterexample :
    adaptiveBaseRate (1 / 2 : ℝ) * 1 < 1 ∧
      adaptiveAmbientDimension (1 / 2 : ℝ) 1 0 = 1 ∧
      agreementThreshold (1 / 2 : ℝ) 1 0 = 1 ∧
      (agreementThreshold (1 / 2 : ℝ) 1 0 : ℝ) /
          adaptiveAmbientDimension (1 / 2 : ℝ) 1 0 = 1 ∧
      adaptiveAgreementFactor (1 / 2 : ℝ) = 2 := by
  have hGapCeil : Nat.ceil ((1 : ℝ) / 2) = 1 := by
    norm_num [Nat.ceil_eq_iff]
  have hBaseCeil : Nat.ceil ((1 : ℝ) / 8) = 1 := by
    norm_num [Nat.ceil_eq_iff]
  norm_num [adaptiveBaseRate, adaptivePadding, adaptiveAmbientDimension,
    adaptiveAgreementFactor, agreementThreshold, hGapCeil, hBaseCeil]

end
end AllRateListDecoding
end ReedSolomon
