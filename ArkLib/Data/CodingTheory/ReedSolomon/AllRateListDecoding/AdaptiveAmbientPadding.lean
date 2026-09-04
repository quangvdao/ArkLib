/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AmbientPadding

/-!
# Adaptive ambient padding for all-rate Reed-Solomon list decoding

This file formalizes the paper's qualitative ambient padding.  For capacity gap `delta`, set

`rho₀ = delta * (1 - delta) / 2`

and take the ambient dimension

`K = max k (ceil (rho₀ * n))`.

Once `1 ≤ rho₀ * n` absorbs the one-unit ceiling loss, this choice gives the rate-independent
comparison

`1 / (1 - delta) ≤ A / K`,

where `A = k + ceil (delta * n)` is the requested agreement threshold.  The ambient rate is at
least `rho₀`, and `K` is strictly below both `n` and `A`.  A separate lemma records the exact
finite condition placing the derivative order below the manuscript's degree `D = K - 1`.
-/

namespace ReedSolomon
namespace AllRateListDecoding

noncomputable section

/-- The paper's rate floor for adaptive qualitative padding. -/
def adaptiveBaseRate (delta : ℝ) : ℝ :=
  delta * (1 - delta) / 2

/-- The integral adaptive padding floor, rounded up so it remains a lower rate bound. -/
def adaptivePadding (delta : ℝ) (blockLength : ℕ) : ℕ :=
  Nat.ceil (adaptiveBaseRate delta * blockLength)

/-- The paper's adaptive ambient dimension `K`. -/
def adaptiveAmbientDimension (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  max messageDim (adaptivePadding delta blockLength)

/-- The paper's adaptive ambient polynomial degree `D = K - 1`. -/
def adaptiveAmbientDegree (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  adaptiveAmbientDimension delta blockLength messageDim - 1

/-- The rate of the adaptive ambient polynomial space. -/
def adaptiveAmbientRate (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  adaptiveAmbientDimension delta blockLength messageDim / blockLength

/-- The uniform agreement-to-ambient factor supplied by adaptive padding. -/
def adaptiveAgreementFactor (delta : ℝ) : ℝ :=
  1 / (1 - delta)

lemma adaptiveBaseRate_pos {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    0 < adaptiveBaseRate delta := by
  rw [adaptiveBaseRate]
  positivity

lemma adaptivePadding_pos {delta : ℝ} {blockLength : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength) :
    0 < adaptivePadding delta blockLength := by
  rw [adaptivePadding]
  apply Nat.ceil_pos.mpr
  exact mul_pos (adaptiveBaseRate_pos hdelta hdeltaOne) (by exact_mod_cast hBlockLength)

lemma adaptiveAmbientDimension_pos {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength) :
    0 < adaptiveAmbientDimension delta blockLength messageDim := by
  rw [adaptiveAmbientDimension]
  exact (adaptivePadding_pos hdelta hdeltaOne hBlockLength).trans_le (Nat.le_max_right _ _)

/-- The explicit large-block condition absorbs the one-unit loss from rounding `rho₀ * n` up. -/
lemma adaptivePadding_le_gapProduct {delta : ℝ} {blockLength : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    (adaptivePadding delta blockLength : ℝ) ≤ delta * (1 - delta) * blockLength := by
  have hBaseNonneg : 0 ≤ adaptiveBaseRate delta * (blockLength : ℝ) :=
    mul_nonneg (adaptiveBaseRate_pos hdelta hdeltaOne).le (Nat.cast_nonneg _)
  have hCeil :
      (adaptivePadding delta blockLength : ℝ) <
        adaptiveBaseRate delta * blockLength + 1 := by
    simpa only [adaptivePadding] using Nat.ceil_lt_add_one hBaseNonneg
  rw [adaptiveBaseRate] at hRounding hCeil
  nlinarith

/-- Adaptive padding gives the promised positive lower bound on the ambient rate. -/
lemma adaptiveBaseRate_le_adaptiveAmbientRate {delta : ℝ} {blockLength messageDim : ℕ}
    (hBlockLength : 0 < blockLength) :
    adaptiveBaseRate delta ≤ adaptiveAmbientRate delta blockLength messageDim := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  rw [adaptiveAmbientRate]
  apply (le_div_iff₀ hLength).mpr
  calc
    adaptiveBaseRate delta * blockLength ≤
        (adaptivePadding delta blockLength : ℝ) := Nat.le_ceil _
    _ ≤ adaptiveAmbientDimension delta blockLength messageDim := by
      exact_mod_cast Nat.le_max_right messageDim (adaptivePadding delta blockLength)

/-- The adaptive dimension is at most `(1 - delta)` times the agreement threshold.  This is the
cross-multiplied form of the paper's uniform ratio bound. -/
lemma adaptiveAmbientDimension_le_one_sub_gap_mul_agreementThreshold {delta : ℝ}
    {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    (adaptiveAmbientDimension delta blockLength messageDim : ℝ) ≤
      (1 - delta) * agreementThreshold delta blockLength messageDim := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hOneSub : 0 < 1 - delta := sub_pos.mpr hdeltaOne
  have hMessage : (messageDim : ℝ) ≤ (1 - delta) * blockLength :=
    (div_le_iff₀ hLength).mp hRate
  have hCeil :
      delta * blockLength ≤ (Nat.ceil (delta * blockLength) : ℝ) := Nat.le_ceil _
  have hAgreementLower :
      (messageDim : ℝ) + delta * blockLength ≤
        agreementThreshold delta blockLength messageDim := by
    rw [agreementThreshold, Nat.cast_add]
    linarith
  have hScaledAgreement :
      (1 - delta) * ((messageDim : ℝ) + delta * blockLength) ≤
        (1 - delta) * agreementThreshold delta blockLength messageDim :=
    mul_le_mul_of_nonneg_left hAgreementLower hOneSub.le
  have hMessageScaled :
      (messageDim : ℝ) ≤ (1 - delta) * (messageDim + delta * blockLength) := by
    nlinarith
  have hPadding := adaptivePadding_le_gapProduct hdelta hdeltaOne hRounding
  have hMessageNonneg : (0 : ℝ) ≤ messageDim := Nat.cast_nonneg messageDim
  have hPaddingScaled :
      (adaptivePadding delta blockLength : ℝ) ≤
        (1 - delta) * (messageDim + delta * blockLength) := by
    nlinarith
  rw [adaptiveAmbientDimension, Nat.cast_max]
  exact (max_le hMessageScaled hPaddingScaled).trans hScaledAgreement

/-- Adaptive padding stays strictly below the block length at every feasible code rate. -/
lemma adaptiveAmbientDimension_lt_blockLength {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    adaptiveAmbientDimension delta blockLength messageDim < blockLength := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hMessage : (messageDim : ℝ) ≤ (1 - delta) * blockLength :=
    (div_le_iff₀ hLength).mp hRate
  have hMessageLt : (messageDim : ℝ) < blockLength := by
    nlinarith [mul_pos hdelta hLength]
  have hPadding := adaptivePadding_le_gapProduct hdelta hdeltaOne hRounding
  have hProductLtOne : delta * (1 - delta) < 1 := by
    nlinarith [sq_nonneg (delta - 1 / 2)]
  have hPaddingLt : (adaptivePadding delta blockLength : ℝ) < blockLength := by
    nlinarith
  have hAmbientLt :
      (adaptiveAmbientDimension delta blockLength messageDim : ℝ) < blockLength := by
    rw [adaptiveAmbientDimension, Nat.cast_max, max_lt_iff]
    exact ⟨hMessageLt, hPaddingLt⟩
  exact_mod_cast hAmbientLt

/-- The paper's uniform agreement factor is strictly larger than one. -/
lemma one_lt_adaptiveAgreementFactor {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    (1 : ℝ) < adaptiveAgreementFactor delta := by
  have hOneSub : (0 : ℝ) < 1 - delta := sub_pos.mpr hdeltaOne
  rw [adaptiveAgreementFactor]
  apply (lt_div_iff₀ hOneSub).mpr
  linarith

/-- Agreement divided by the adaptive dimension is uniformly at least `1 / (1 - delta)`. -/
lemma adaptiveAgreementFactor_le_agreementThreshold_div_adaptiveAmbientDimension {delta : ℝ}
    {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    adaptiveAgreementFactor delta ≤ agreementThreshold delta blockLength messageDim /
      adaptiveAmbientDimension delta blockLength messageDim := by
  have hOneSub : (0 : ℝ) < 1 - delta := sub_pos.mpr hdeltaOne
  have hAmbientPositive :=
    adaptiveAmbientDimension_pos (messageDim := messageDim) hdelta hdeltaOne hBlockLength
  have hAmbientPositiveReal :
      (0 : ℝ) < adaptiveAmbientDimension delta blockLength messageDim := by
    exact_mod_cast hAmbientPositive
  have hCross := adaptiveAmbientDimension_le_one_sub_gap_mul_agreementThreshold
    hdelta hdeltaOne hBlockLength hRate hRounding
  apply (le_div_iff₀ hAmbientPositiveReal).mpr
  calc
    adaptiveAgreementFactor delta * adaptiveAmbientDimension delta blockLength messageDim =
        adaptiveAmbientDimension delta blockLength messageDim / (1 - delta) := by
      rw [adaptiveAgreementFactor, one_div, div_eq_mul_inv]
      ring
    _ ≤ agreementThreshold delta blockLength messageDim := by
      apply (div_le_iff₀ hOneSub).mpr
      simpa only [mul_comm] using hCross

/-- The adaptive ambient dimension lies strictly below the agreement threshold. -/
lemma adaptiveAmbientDimension_lt_agreementThreshold {delta : ℝ}
    {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    adaptiveAmbientDimension delta blockLength messageDim <
      agreementThreshold delta blockLength messageDim := by
  have hAmbientPositive :=
    adaptiveAmbientDimension_pos (messageDim := messageDim) hdelta hdeltaOne hBlockLength
  have hRatio := adaptiveAgreementFactor_le_agreementThreshold_div_adaptiveAmbientDimension
    hdelta hdeltaOne hBlockLength hRate hRounding
  have hFactor := one_lt_adaptiveAgreementFactor hdelta hdeltaOne
  have hAmbientPositiveReal :
      (0 : ℝ) < adaptiveAmbientDimension delta blockLength messageDim := by
    exact_mod_cast hAmbientPositive
  have hAgreement :
      (adaptiveAmbientDimension delta blockLength messageDim : ℝ) <
        agreementThreshold delta blockLength messageDim := by
    have hRatioOne := hFactor.trans_le hRatio
    simpa using (lt_div_iff₀ hAmbientPositiveReal).mp hRatioOne
  exact_mod_cast hAgreement

/-- An explicit padding threshold places the derivative order below `D = K - 1`. -/
lemma derivOrder_lt_adaptiveAmbientDegree {delta : ℝ}
    {blockLength messageDim derivOrder : ℕ}
    (hOrder : ((derivOrder + 2 : ℕ) : ℝ) ≤ adaptiveBaseRate delta * blockLength) :
    derivOrder < adaptiveAmbientDegree delta blockLength messageDim := by
  have hCeilReal :
      ((derivOrder + 2 : ℕ) : ℝ) ≤ (adaptivePadding delta blockLength : ℝ) :=
    hOrder.trans (Nat.le_ceil _)
  have hCeil : derivOrder + 2 ≤ adaptivePadding delta blockLength := by
    exact_mod_cast hCeilReal
  rw [adaptiveAmbientDegree, adaptiveAmbientDimension]
  omega

/-- All rate-uniform geometric facts supplied by the paper's adaptive padding. -/
structure AdaptiveAmbientGeometry (delta : ℝ) (blockLength messageDim : ℕ) : Prop where
  ambientPositive : 0 < adaptiveAmbientDimension delta blockLength messageDim
  ambient_lt_blockLength : adaptiveAmbientDimension delta blockLength messageDim < blockLength
  ambient_lt_agreement : adaptiveAmbientDimension delta blockLength messageDim <
    agreementThreshold delta blockLength messageDim
  baseRate_le_ambientRate : adaptiveBaseRate delta ≤
    adaptiveAmbientRate delta blockLength messageDim
  one_lt_uniformAgreementFactor : (1 : ℝ) < adaptiveAgreementFactor delta
  uniformAgreementFactor_le_agreementRatio : adaptiveAgreementFactor delta ≤
    agreementThreshold delta blockLength messageDim /
      adaptiveAmbientDimension delta blockLength messageDim

/-- Adaptive padding works uniformly over every feasible code rate once the explicit ceiling
margin `1 ≤ rho₀ * n` holds. -/
theorem adaptiveAmbientGeometry {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 1 ≤ adaptiveBaseRate delta * blockLength) :
    AdaptiveAmbientGeometry delta blockLength messageDim where
  ambientPositive := adaptiveAmbientDimension_pos hdelta hdeltaOne hBlockLength
  ambient_lt_blockLength :=
    adaptiveAmbientDimension_lt_blockLength hdelta hdeltaOne hBlockLength hRate hRounding
  ambient_lt_agreement :=
    adaptiveAmbientDimension_lt_agreementThreshold hdelta hdeltaOne hBlockLength hRate hRounding
  baseRate_le_ambientRate := adaptiveBaseRate_le_adaptiveAmbientRate hBlockLength
  one_lt_uniformAgreementFactor := one_lt_adaptiveAgreementFactor hdelta hdeltaOne
  uniformAgreementFactor_le_agreementRatio :=
    adaptiveAgreementFactor_le_agreementThreshold_div_adaptiveAmbientDimension
      hdelta hdeltaOne hBlockLength hRate hRounding

end
end AllRateListDecoding
end ReedSolomon
