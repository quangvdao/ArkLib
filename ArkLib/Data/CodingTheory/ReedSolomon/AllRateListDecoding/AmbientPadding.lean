/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.Contracts
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Ambient padding for all-rate Reed-Solomon list decoding

This file isolates the elementary geometry of the direct ambient-padding reduction.  For a code
of block length `n`, message dimension `k`, and additive capacity gap `delta`, we use the midpoint
padding

`K = k + floor ((delta / 2) * n)`.

The manuscript's ambient degree is `D = K - 1`.  Once the two explicit rounding margins
`4 ≤ delta * n` and `2 * (d + 2) ≤ delta * n` hold, we have `d < D < K`; moreover, `K`
lies below both the block length and the requested agreement threshold.  Its rate is uniformly
bounded below by `delta / 4`.  More importantly for the downstream power-saving argument, the
requested agreement divided by `K` is uniformly at least `1 / (1 - delta / 2) > 1`.
-/

namespace ReedSolomon
namespace AllRateListDecoding

noncomputable section

/-- Half-gap padding, rounded down to an integral number of coefficients. -/
def midpointPadding (delta : ℝ) (blockLength : ℕ) : ℕ :=
  Nat.floor ((delta / 2) * blockLength)

/-- The ambient polynomial dimension obtained by adding midpoint padding to the message space. -/
def midpointAmbientDimension (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  messageDim + midpointPadding delta blockLength

/-- The rate of the midpoint-padded ambient polynomial space. -/
def midpointAmbientRate (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  midpointAmbientDimension delta blockLength messageDim / blockLength

/-- The manuscript's ambient polynomial degree, one below the ambient dimension. -/
def midpointAmbientDegree (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  midpointAmbientDimension delta blockLength messageDim - 1

/-- A rate-independent lower bound for agreement divided by the ambient dimension. -/
def midpointAgreementFactor (delta : ℝ) : ℝ :=
  1 / (1 - delta / 2)

lemma messageDim_le_midpointAmbientDimension (delta : ℝ) (blockLength messageDim : ℕ) :
    messageDim ≤ midpointAmbientDimension delta blockLength messageDim := by
  simp [midpointAmbientDimension]

/-- Midpoint padding is strictly smaller than the rounded full-gap contribution. -/
lemma midpointPadding_lt_ceil_gap {delta : ℝ} {blockLength : ℕ}
    (hdelta : 0 < delta) (hBlockLength : 0 < blockLength) :
    midpointPadding delta blockLength < Nat.ceil (delta * blockLength) := by
  rw [midpointPadding]
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  exact Nat.floor_lt_ceil_of_lt_of_pos
    (by nlinarith [mul_pos hdelta hLength]) (mul_pos hdelta hLength)

/-- The padded dimension lies strictly below the requested agreement threshold. -/
lemma midpointAmbientDimension_lt_agreementThreshold {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hBlockLength : 0 < blockLength) :
    midpointAmbientDimension delta blockLength messageDim <
      agreementThreshold delta blockLength messageDim := by
  simpa [midpointAmbientDimension, agreementThreshold] using
    Nat.add_lt_add_left (midpointPadding_lt_ceil_gap hdelta hBlockLength) messageDim

/-- A feasible code rate leaves enough room for midpoint padding below the block length. -/
lemma midpointAmbientDimension_lt_blockLength {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta) :
    midpointAmbientDimension delta blockLength messageDim < blockLength := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hMessage : (messageDim : ℝ) ≤ (1 - delta) * blockLength :=
    (div_le_iff₀ hLength).mp hRate
  have hPaddingNonneg : 0 ≤ (delta / 2) * (blockLength : ℝ) :=
    (mul_nonneg (div_nonneg hdelta.le (by norm_num)) hLength.le)
  have hPadding :
      (midpointPadding delta blockLength : ℝ) ≤ (delta / 2) * blockLength := by
    exact Nat.floor_le hPaddingNonneg
  have hAmbient :
      (midpointAmbientDimension delta blockLength messageDim : ℝ) < blockLength := by
    rw [midpointAmbientDimension, Nat.cast_add]
    nlinarith [mul_pos hdelta hLength]
  exact_mod_cast hAmbient

/-- A uniform lower bound for the padded ambient rate, including the one-unit floor loss. -/
lemma quarterGap_lt_midpointAmbientRate {delta : ℝ} {blockLength messageDim : ℕ}
    (hBlockLength : 0 < blockLength) (hRounding : 4 ≤ delta * blockLength) :
    delta / 4 < midpointAmbientRate delta blockLength messageDim := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hFloor :
      (delta / 2) * blockLength - 1 < (midpointPadding delta blockLength : ℝ) := by
    exact Nat.sub_one_lt_floor ((delta / 2) * blockLength)
  have hMessageNonneg : (0 : ℝ) ≤ messageDim := Nat.cast_nonneg messageDim
  rw [midpointAmbientRate]
  apply (lt_div_iff₀ hLength).mpr
  rw [midpointAmbientDimension, Nat.cast_add]
  nlinarith

/-- The derivative order fits below the padding under an explicit full-gap size condition. -/
lemma derivOrder_lt_midpointPadding {delta : ℝ} {blockLength derivOrder : ℕ}
    (hOrder : (2 : ℝ) * (derivOrder + 1) ≤ delta * blockLength) :
    derivOrder < midpointPadding delta blockLength := by
  have hLe : ((derivOrder + 1 : ℕ) : ℝ) ≤ (delta / 2) * blockLength := by
    push_cast at hOrder ⊢
    linarith
  have hFloor : derivOrder + 1 ≤ midpointPadding delta blockLength := by
    exact Nat.le_floor hLe
  omega

/-- Hence the derivative order also fits below every midpoint-padded ambient dimension. -/
lemma derivOrder_lt_midpointAmbientDimension {delta : ℝ}
    {blockLength messageDim derivOrder : ℕ}
    (hOrder : (2 : ℝ) * (derivOrder + 1) ≤ delta * blockLength) :
    derivOrder < midpointAmbientDimension delta blockLength messageDim := by
  have hPadding := derivOrder_lt_midpointPadding hOrder
  rw [midpointAmbientDimension]
  omega

/-- The stronger order threshold places the derivative order below the manuscript's ambient
degree `D = K - 1`, not merely below its dimension `K`. -/
lemma derivOrder_lt_midpointAmbientDegree {delta : ℝ}
    {blockLength messageDim derivOrder : ℕ}
    (hOrder : (2 : ℝ) * (derivOrder + 2) ≤ delta * blockLength) :
    derivOrder < midpointAmbientDegree delta blockLength messageDim := by
  have hLe : ((derivOrder + 2 : ℕ) : ℝ) ≤ (delta / 2) * blockLength := by
    push_cast at hOrder ⊢
    linarith
  have hFloor : derivOrder + 2 ≤ midpointPadding delta blockLength := by
    exact Nat.le_floor hLe
  rw [midpointAmbientDegree, midpointAmbientDimension]
  omega

/-- The uniform agreement factor is strictly larger than one for every gap in `(0, 1)`. -/
lemma one_lt_midpointAgreementFactor {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    (1 : ℝ) < midpointAgreementFactor delta := by
  have hDenom : (0 : ℝ) < 1 - delta / 2 := by linarith
  rw [midpointAgreementFactor]
  apply (lt_div_iff₀ hDenom).mpr
  linarith

/-- The requested agreement-to-ambient ratio is uniformly separated from one, independently of
the code rate. -/
lemma midpointAgreementFactor_le_agreementThreshold_div_midpointAmbientDimension {delta : ℝ}
    {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hAmbientPositive : 0 < midpointAmbientDimension delta blockLength messageDim) :
    midpointAgreementFactor delta ≤ agreementThreshold delta blockLength messageDim /
      midpointAmbientDimension delta blockLength messageDim := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hDenom : (0 : ℝ) < 1 - delta / 2 := by linarith
  have hMessage : (messageDim : ℝ) ≤ (1 - delta) * blockLength :=
    (div_le_iff₀ hLength).mp hRate
  have hPaddingNonneg : 0 ≤ (delta / 2) * (blockLength : ℝ) :=
    mul_nonneg (div_nonneg hdelta.le (by norm_num)) hLength.le
  have hPadding :
      (midpointPadding delta blockLength : ℝ) ≤ (delta / 2) * blockLength :=
    Nat.floor_le hPaddingNonneg
  have hAmbientUpper :
      (midpointAmbientDimension delta blockLength messageDim : ℝ) ≤
        messageDim + (delta / 2) * blockLength := by
    rw [midpointAmbientDimension, Nat.cast_add]
    linarith
  have hCeil :
      delta * blockLength ≤ (Nat.ceil (delta * blockLength) : ℝ) := Nat.le_ceil _
  have hAgreementLower :
      (messageDim : ℝ) + delta * blockLength ≤
        agreementThreshold delta blockLength messageDim := by
    rw [agreementThreshold, Nat.cast_add]
    linarith
  have hIdeal :
      (messageDim : ℝ) + (delta / 2) * blockLength ≤
        (1 - delta / 2) * (messageDim + delta * blockLength) := by
    nlinarith
  have hScaledAgreement :
      (1 - delta / 2) * ((messageDim : ℝ) + delta * blockLength) ≤
        (1 - delta / 2) * agreementThreshold delta blockLength messageDim :=
    mul_le_mul_of_nonneg_left hAgreementLower hDenom.le
  have hCross :
      (midpointAmbientDimension delta blockLength messageDim : ℝ) ≤
        (1 - delta / 2) * agreementThreshold delta blockLength messageDim :=
    hAmbientUpper.trans (hIdeal.trans hScaledAgreement)
  have hAmbientPositiveReal :
      (0 : ℝ) < midpointAmbientDimension delta blockLength messageDim := by
    exact_mod_cast hAmbientPositive
  apply (le_div_iff₀ hAmbientPositiveReal).mpr
  calc
    midpointAgreementFactor delta * midpointAmbientDimension delta blockLength messageDim =
        midpointAmbientDimension delta blockLength messageDim / (1 - delta / 2) := by
      rw [midpointAgreementFactor, one_div, div_eq_mul_inv]
      ring
    _ ≤ agreementThreshold delta blockLength messageDim := by
      apply (div_le_iff₀ hDenom).mpr
      simpa only [mul_comm] using hCross

/-- Strict containment below the agreement threshold gives a ratio strictly larger than one. -/
lemma one_lt_agreementThreshold_div_midpointAmbientDimension {delta : ℝ}
    {blockLength messageDim : ℕ}
    (hAmbientPositive : 0 < midpointAmbientDimension delta blockLength messageDim)
    (hAmbientAgreement : midpointAmbientDimension delta blockLength messageDim <
      agreementThreshold delta blockLength messageDim) :
    (1 : ℝ) < agreementThreshold delta blockLength messageDim /
      midpointAmbientDimension delta blockLength messageDim := by
  have hAmbientPositiveReal :
      (0 : ℝ) < midpointAmbientDimension delta blockLength messageDim := by
    exact_mod_cast hAmbientPositive
  apply (lt_div_iff₀ hAmbientPositiveReal).mpr
  simpa using (Nat.cast_lt.mpr hAmbientAgreement :
    (midpointAmbientDimension delta blockLength messageDim : ℝ) <
      agreementThreshold delta blockLength messageDim)

/-- All geometric side conditions supplied by midpoint ambient padding. -/
structure MidpointAmbientGeometry (delta : ℝ)
    (blockLength messageDim derivOrder : ℕ) : Prop where
  /-- The derivative order is below the manuscript's ambient degree `D = K - 1`. -/
  derivOrder_lt_degree : derivOrder < midpointAmbientDegree delta blockLength messageDim
  /-- The derivative order is below the ambient dimension. -/
  derivOrder_lt : derivOrder < midpointAmbientDimension delta blockLength messageDim
  /-- The ambient dimension is a genuine subspace of the block-length polynomial space. -/
  ambient_lt_blockLength : midpointAmbientDimension delta blockLength messageDim < blockLength
  /-- The requested agreement exceeds the ambient dimension. -/
  ambient_lt_agreement : midpointAmbientDimension delta blockLength messageDim <
    agreementThreshold delta blockLength messageDim
  /-- The padded ambient rate has a positive, rate-independent lower bound. -/
  quarterGap_lt_ambientRate : delta / 4 <
    midpointAmbientRate delta blockLength messageDim
  /-- Agreement is separated from the ambient dimension by a multiplicative factor above one. -/
  one_lt_agreementRatio : (1 : ℝ) < agreementThreshold delta blockLength messageDim /
    midpointAmbientDimension delta blockLength messageDim
  /-- The rate-independent factor itself is strictly larger than one. -/
  one_lt_uniformAgreementFactor : (1 : ℝ) < midpointAgreementFactor delta
  /-- The uniform factor lower-bounds agreement divided by the ambient dimension. -/
  uniformAgreementFactor_le_agreementRatio : midpointAgreementFactor delta ≤
    agreementThreshold delta blockLength messageDim /
      midpointAmbientDimension delta blockLength messageDim

/-- Midpoint padding works uniformly over every feasible code rate.

The hypotheses involving `4` and `2 * (derivOrder + 2)` are the explicit finite-size costs of
rounding down the padding and placing the derivative order below it. -/
theorem midpointAmbientGeometry {delta : ℝ} {blockLength messageDim derivOrder : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta)
    (hRounding : 4 ≤ delta * blockLength)
    (hOrder : (2 : ℝ) * (derivOrder + 2) ≤ delta * blockLength) :
    MidpointAmbientGeometry delta blockLength messageDim derivOrder := by
  have hDerivOrderDegree :=
    derivOrder_lt_midpointAmbientDegree (messageDim := messageDim) hOrder
  have hDerivOrder : derivOrder < midpointAmbientDimension delta blockLength messageDim := by
    rw [midpointAmbientDegree] at hDerivOrderDegree
    omega
  have hAmbientAgreement :=
    midpointAmbientDimension_lt_agreementThreshold (messageDim := messageDim) hdelta hBlockLength
  have hAmbientPositive := Nat.zero_lt_of_lt hDerivOrder
  have hUniformFactor :=
    midpointAgreementFactor_le_agreementThreshold_div_midpointAmbientDimension
      hdelta hdeltaOne hBlockLength hRate hAmbientPositive
  have hUniformFactorOne := one_lt_midpointAgreementFactor hdelta hdeltaOne
  exact
    { derivOrder_lt_degree := hDerivOrderDegree
      derivOrder_lt := hDerivOrder
      ambient_lt_blockLength :=
        midpointAmbientDimension_lt_blockLength hdelta hBlockLength hRate
      ambient_lt_agreement := hAmbientAgreement
      quarterGap_lt_ambientRate :=
        quarterGap_lt_midpointAmbientRate hBlockLength hRounding
      one_lt_agreementRatio := hUniformFactorOne.trans_le hUniformFactor
      one_lt_uniformAgreementFactor := hUniformFactorOne
      uniformAgreementFactor_le_agreementRatio := hUniformFactor }

end
end AllRateListDecoding
end ReedSolomon
