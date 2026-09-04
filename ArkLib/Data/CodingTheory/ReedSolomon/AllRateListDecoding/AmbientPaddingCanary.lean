/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AmbientPadding
import Mathlib.Tactic.NormNum

/-!
# Canaries for midpoint ambient padding

These small exact examples exercise the zero-rate endpoint, the top feasible rate, nonintegral
floor/ceiling behavior, and the finite-size hypothesis needed for a positive padded rate.
-/

namespace ReedSolomon
namespace AllRateListDecoding

noncomputable section

/-- At zero message rate, gap `1/2` and length `16` give ambient rate `1/4` and agreement ratio
exactly `2`. -/
lemma zero_rate_midpoint_padding_canary :
    midpointPadding (1 / 2 : ℝ) 16 = 4 ∧
      midpointAmbientDimension (1 / 2 : ℝ) 16 0 = 4 ∧
      midpointAmbientDegree (1 / 2 : ℝ) 16 0 = 3 ∧
      agreementThreshold (1 / 2 : ℝ) 16 0 = 8 ∧
      midpointAmbientRate (1 / 2 : ℝ) 16 0 = 1 / 4 ∧
      midpointAgreementFactor (1 / 2 : ℝ) = 4 / 3 ∧
      (agreementThreshold (1 / 2 : ℝ) 16 0 : ℝ) /
          midpointAmbientDimension (1 / 2 : ℝ) 16 0 = 2 := by
  norm_num [midpointPadding, midpointAmbientDimension, midpointAmbientDegree,
    midpointAmbientRate, midpointAgreementFactor, agreementThreshold]

/-- At the top feasible rate `3/4`, gap `1/4` and length `32` still leave four padding
coefficients and an agreement-to-ambient ratio of `8/7`. -/
lemma top_rate_midpoint_padding_canary :
    midpointPadding (1 / 4 : ℝ) 32 = 4 ∧
      midpointAmbientDimension (1 / 4 : ℝ) 32 24 = 28 ∧
      agreementThreshold (1 / 4 : ℝ) 32 24 = 32 ∧
      midpointAmbientRate (1 / 4 : ℝ) 32 24 = 7 / 8 ∧
      midpointAgreementFactor (1 / 4 : ℝ) = 8 / 7 ∧
      (agreementThreshold (1 / 4 : ℝ) 32 24 : ℝ) /
          midpointAmbientDimension (1 / 4 : ℝ) 32 24 = 8 / 7 := by
  norm_num [midpointPadding, midpointAmbientDimension, midpointAmbientRate,
    midpointAgreementFactor, agreementThreshold]

/-- A nonintegral example catches accidental swaps between the floor used for padding and the
ceiling used for agreement. -/
lemma nonintegral_midpoint_rounding_canary :
    midpointPadding (3 / 10 : ℝ) 7 = 1 ∧
      midpointAmbientDimension (3 / 10 : ℝ) 7 4 = 5 ∧
      agreementThreshold (3 / 10 : ℝ) 7 4 = 7 := by
  have hCeil : Nat.ceil ((21 : ℝ) / 10) = 3 := by
    norm_num [Nat.ceil_eq_iff]
  norm_num [midpointPadding, midpointAmbientDimension, agreementThreshold, hCeil]

/-- The bundled theorem applies at both the low-rate and high-rate extremes. -/
lemma midpoint_geometry_endpoint_canary :
    MidpointAmbientGeometry (1 / 2 : ℝ) 16 0 1 ∧
      MidpointAmbientGeometry (1 / 4 : ℝ) 32 24 1 := by
  constructor <;> apply midpointAmbientGeometry <;> norm_num

/-- For a one-symbol block the midpoint floor can vanish, so a large-block rounding hypothesis
is genuinely necessary for any positive lower bound uniform in the message rate. -/
lemma tiny_block_padding_vanishes_canary :
    midpointPadding (1 / 2 : ℝ) 1 = 0 ∧
      midpointAmbientDimension (1 / 2 : ℝ) 1 0 = 0 := by
  norm_num [midpointPadding, midpointAmbientDimension]

end
end AllRateListDecoding
end ReedSolomon
