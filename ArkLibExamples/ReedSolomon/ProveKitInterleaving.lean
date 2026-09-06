/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLibExamples.ReedSolomon.ProveKitMCA
import ArkLibExamples.ReedSolomon.ProveKitQueryTuning

/-!
# Concrete width-eight Reed--Solomon bounds for ProveKit

This module applies the first-order ProveKit certificates to the actual width-eight row-wise
interleaved Reed--Solomon code. It treats the original 109-query agreement threshold `492831`
and the retuned 108-query threshold `491867`.

## Reading the statements

The base field `F` is arbitrary subject to the displayed characteristic hypothesis. The MCA
theorems additionally assume its cardinality is the pinned BN254 scalar modulus, because their
conclusion is the concrete `2^-128` probability bound. They quantify over all received
width-eight word pairs through `mcaError`; no received word or bad set is supplied as a premise.

The list theorems need no finiteness assumption on `F`. They bound `Code.Lambda`, hence every
received width-eight word, by the same scalar list bound. The proof packs each eight-tuple and
each stack of eight row polynomials into the rational-function field `F(Z)`. The scalar premise
over `F(Z)` is then derived from the proved first-order certificate theorems in `ProveKitMCA` and
`ProveKitQueryTuning`; no interleaved list bound is assumed.

## Scope

These results connect ProveKit's concrete agreement thresholds and interleaving width to ArkLib's
coding-theoretic `mcaError` and `Lambda` definitions. The query-count arithmetic remains in
`ProveKit` and `ProveKitQueryTuning`. This module does not model transcripts, Fiat--Shamir
sampling, commitment openings, or whole-protocol soundness.
-/

open Polynomial Code CoreDefinitions LinearCode
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

noncomputable section

/-- Capacity-gap parameter whose radius has exactly `492831` required agreements. -/
def original109Gap : ℝ := 230687 / 1048576

/-- Relative decoding radius of the original 109-query profile. -/
def original109Radius : NNReal :=
  555745 / 1048576

/-- Capacity-gap parameter whose radius has exactly `491867` required agreements. -/
def retuned108Gap : ℝ := 229723 / 1048576

/-- Relative decoding radius of the retuned 108-query profile. -/
def retuned108Radius : NNReal :=
  556709 / 1048576

@[simp] theorem original109Radius_coe :
    (original109Radius : ℝ) = 555745 / 1048576 := by
  norm_num [original109Radius]

@[simp] theorem retuned108Radius_coe :
    (retuned108Radius : ℝ) = 556709 / 1048576 := by
  norm_num [retuned108Radius]

/-- The original capacity-gap notation reproduces the agreement threshold and relative radius. -/
theorem original109_gap_spec :
    agreementThreshold original109Gap 1048576 262144 = 492831 ∧
      capacityRadius original109Gap 1048576 262144 = original109Radius := by
  constructor
  · norm_num [agreementThreshold, original109Gap]
  · rw [original109Radius_coe]
    norm_num [capacityRadius, original109Gap]

/-- The retuned capacity-gap notation reproduces the agreement threshold and relative radius. -/
theorem retuned108_gap_spec :
    agreementThreshold retuned108Gap 1048576 262144 = 491867 ∧
      capacityRadius retuned108Gap 1048576 262144 = retuned108Radius := by
  constructor
  · norm_num [agreementThreshold, retuned108Gap]
  · rw [retuned108Radius_coe]
    norm_num [capacityRadius, retuned108Gap]

/-- The original first-order constructor yields a scalar exact-line bound of `2^115`. -/
theorem original109_lineAgreement {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    LineExactAgreementBound domain 262144 492831 (2 ^ 115) := by
  have hraw := lineExactAgreementBound_firstOrder_of_heightSlotCount domain
    (by norm_num : 1 < 262143) (by norm_num : 0 < 384 * 492831)
    (by norm_num : 262144 ≤ 262143 + 1) bn254_interpolation_height
    (by norm_num : 1 < 262144) (by norm_num : 262144 ≤ 262144)
    (by norm_num : 0 < 262144) (by norm_num : 262144 ≤ 262197)
    (by norm_num : 262197 ≤ 492831) (by norm_num : 492831 ≤ 1048576)
    (hchar.imp_right (by omega))
  apply hraw.mono
  exact_mod_cast bn254_firstOrder_mca_envelope_le

open Classical in
/-- At the original 109-query radius, the actual width-eight code has affine-line MCA error at
most `2^-128`. The scalar exact-line premise is constructed above, and interleaving invariance
transports it without a width loss. -/
theorem original109_widthEight_mcaError_le
    {F : Type} [Field F] [Fintype F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) :
    mcaError (AffineLineGenerator F)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (original109Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := ReedSolomon.mcaError_interleaved_le_of_exactAgreement domain
    (t := 8) (A := 492831) (2 ^ 115) (original109_lineAgreement domain hchar)
      original109Radius (by norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [original109Radius_coe]; norm_num)
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

/-- Every received word for the original width-eight code has at most `2^50` nearby codewords.
The bound is unchanged from the scalar first-order list theorem. -/
theorem original109_widthEight_lambda_le
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (original109Radius : ℝ) ≤ (2 ^ 50 : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      original109Gap (by norm_num [original109Gap]) (by norm_num) domain (L := 2 ^ 50) (t := 8)
        (by
          intro received S hS
          have hcharRat : ringChar (RatFunc F) = 0 ∨
              max 1048576 688 < ringChar (RatFunc F) := by
            simpa [ReedSolomon.ringChar_ratFunc] using hchar
          have hS' : ∀ P ∈ S,
              IsAgreementSolution
                (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
                received 262144 492831 P := by
            intro P hP
            have hs := hS P hP
            rw [show agreementThreshold original109Gap 1048576 262144 = 492831 by
              exact original109_gap_spec.1] at hs
            simpa [IsAgreementSolution, polynomialAgreementSet] using hs
          have hb := bn254_finite_list_bound
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb.1)
  rw [original109_gap_spec.2] at hpacked
  exact hpacked

open Classical in
/-- At the retuned 108-query radius, the actual width-eight code still has affine-line MCA error
at most `2^-128`. Its scalar premise is `retuned_lineAgreement`, which is itself constructed from
the retuned finite interpolation support. -/
theorem retuned108_widthEight_mcaError_le
    {F : Type} [Field F] [Fintype F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 1048576 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) :
    mcaError (AffineLineGenerator F)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hline := retuned_lineAgreement domain (hchar.imp_right (by omega))
  have hmca := ReedSolomon.mcaError_interleaved_le_of_exactAgreement domain
    (t := 8) (A := 491867) (2 ^ 125) hline retuned108Radius (by norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [retuned108Radius_coe]; norm_num)
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

/-- Every received word for the retuned width-eight code has at most `7155729507207006` nearby
codewords. Rational-function packing again preserves the scalar list bound exactly. -/
theorem retuned108_widthEight_lambda_le
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 1048576 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (retuned108Radius : ℝ) ≤ (7155729507207006 : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      retuned108Gap (by norm_num [retuned108Gap]) (by norm_num) domain
        (L := 7155729507207006) (t := 8) (by
          intro received S hS
          have hcharRat : ringChar (RatFunc F) = 0 ∨
              1048576 < ringChar (RatFunc F) := by
            simpa [ReedSolomon.ringChar_ratFunc] using hchar
          have hS' : ∀ P ∈ S,
              IsAgreementSolution
                (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
                received 262144 491867 P := by
            intro P hP
            have hs := hS P hP
            rw [show agreementThreshold retuned108Gap 1048576 262144 = 491867 by
              exact retuned108_gap_spec.1] at hs
            simpa [IsAgreementSolution, polynomialAgreementSet] using hs
          have hb := retuned_finite_list_bound
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb)
  rw [retuned108_gap_spec.2] at hpacked
  exact hpacked

end

end ArkLibExamples.ReedSolomon.ProveKit
