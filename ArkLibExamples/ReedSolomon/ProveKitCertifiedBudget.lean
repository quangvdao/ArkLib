/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitAffine
import ArkLibExamples.ReedSolomon.ProveKitSharpLists
import ArkLibExamples.ReedSolomon.ProveKitSharpMCA

/-!
# Certified local ProveKit coding budgets

This module joins the semantic MCA and list-decoding theorems to the closed arithmetic for the
accepted ProveKit rows. It first transports the published sharp scalar list caps through the
rational-function packing of width-eight rows. It then packages, for the canonical challenge
fields, the affine MCA bound, the interleaved list bound, and the corresponding local slot,
query, and payload calculations.

The original BN254 package uses 109 queries and the published bounds
`E = 1126820196482631879700641773`, `L = 147000408479737`. The retuned BN254 package uses 108
queries and the independently derived bounds `E = 2^125`, `L = 7155729507207006`. The cubic
Goldilocks package uses its published 115-query row and bounds `E = 8210316778177167673`,
`L = 5089296970`.

No exceptional or list bound is an input to the package theorems. The MCA bounds quantify over
all received affine families through `mcaError`, and the `Code.Lambda` bounds quantify over all
received width-eight words. The numerical fields reproduce the local error and raw-payload model;
they do not compose a whole protocol or model transcript and commitment behavior.
-/

open Polynomial Code CoreDefinitions LinearCode
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields
open ArkLib.FiniteFieldBudget

noncomputable section

/-- The sharp BN254 MCA endpoint and the original 109-query list endpoint use the same radius. -/
theorem sharpBN254OriginalRadius_eq_original109Radius :
    sharpBN254OriginalRadius = original109Radius := by
  rfl

/-- Capacity gap whose threshold is the published cubic-Goldilocks agreement count. -/
def goldilocksCubicGap : ℝ := 250610 / 1048576

/-- The cubic-Goldilocks gap gives threshold `512754` and the radius used by the sharp MCA
endpoint. -/
theorem goldilocksCubic_gap_spec :
    agreementThreshold goldilocksCubicGap 1048576 262144 = 512754 ∧
      capacityRadius goldilocksCubicGap 1048576 262144 = sharpGoldilocksCubicRadius := by
  constructor
  · norm_num [agreementThreshold, goldilocksCubicGap]
  · rw [sharpGoldilocksCubicRadius_coe]
    norm_num [capacityRadius, goldilocksCubicGap]

open Classical in
/-- Rational-function packing preserves the published sharp BN254 list cap at width eight. -/
theorem bn254_original109_widthEight_lambda_le_sharp
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (original109Radius : ℝ) ≤ (bn254.listSize : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      original109Gap (by norm_num [original109Gap]) (by norm_num) domain
        (L := bn254.listSize) (t := 8) (by
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
          have hb := bn254_finite_list_bound_sharp
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb)
  rw [original109_gap_spec.2] at hpacked
  exact hpacked

open Classical in
/-- Rational-function packing preserves the published cubic-Goldilocks list cap at width eight. -/
theorem goldilocksCubic_widthEight_lambda_le_sharp
    {F : Type*} [Field F] (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 24 < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → F)))
        (sharpGoldilocksCubicRadius : ℝ) ≤ (goldilocksCubic.listSize : ℕ∞) := by
  have hpacked :=
    ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
      goldilocksCubicGap (by norm_num [goldilocksCubicGap]) (by norm_num) domain
        (L := goldilocksCubic.listSize) (t := 8) (by
          intro received S hS
          have hcharRat : ringChar (RatFunc F) = 0 ∨
              max 1048576 24 < ringChar (RatFunc F) := by
            simpa [ReedSolomon.ringChar_ratFunc] using hchar
          have hS' : ∀ P ∈ S,
              IsAgreementSolution
                (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
                received 262144 512754 P := by
            intro P hP
            have hs := hS P hP
            rw [show agreementThreshold goldilocksCubicGap 1048576 262144 = 512754 by
              exact goldilocksCubic_gap_spec.1] at hs
            simpa [IsAgreementSolution, polynomialAgreementSet] using hs
          have hb := goldilocksCubic_finite_list_bound_sharp
            (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
              received hcharRat S hS'
          exact_mod_cast hb)
  rw [goldilocksCubic_gap_spec.2] at hpacked
  exact hpacked

/-! ## Closed arithmetic packages -/

/-- The original row's affine MCA loss and list term fit together in one local slot. The MCA
denominator is `q - 1`, as required by the affine-space reduction. -/
theorem bn254_original_affineMCA_list_slot_le :
    (bn254.exceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * bn254.listSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 := by
  norm_num [bn254]

/-- The cubic row's affine MCA loss and list term fit together in one local slot. -/
theorem goldilocksCubic_affineMCA_list_slot_le :
    (goldilocksCubic.exceptionalCount : ℚ) / (goldilocksCubic.fieldSize - 1) +
        (2 * goldilocksCubic.listSize : ℚ) / goldilocksCubic.fieldSize ≤
      (1 : ℚ) / 2 ^ 128 := by
  norm_num [goldilocksCubic]

/-- The accepted retuned row also uses the affine denominator in its combined local slot. -/
theorem bn254_retuned108_affineMCA_list_slot_le :
    (2 ^ 125 : ℚ) / (bn254.fieldSize - 1) +
        (2 * 7155729507207006 : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 := by
  norm_num [bn254]

open Classical in
/-- The retuned canonical BN254 endpoint before weakening its count-level MCA term. -/
theorem bn254Scalar_retuned108_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((2 ^ 125 : ℝ) / (bn254.fieldSize - 1)) := by
  have hmca := ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 491867) (2 ^ 125 : ℝ)
      (retuned_lineAgreement domain (by
        right
        rw [bn254Scalar_ringChar]
        norm_num [BN254.scalarFieldSize]))
      retuned108Radius (by norm_num) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [retuned108Radius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [retuned108Radius])
      (by rw [retuned108Radius_coe]; norm_num)
  rw [bn254Scalar_card] at hmca
  simpa [BN254.scalarFieldSize, bn254] using hmca

open Classical in
/-- The original semantic MCA error plus its list term meets the shared local target. -/
theorem bn254Scalar_original109_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) +
        ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1)) +
          ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) :=
      add_le_add
        (bn254Scalar_original109_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1) +
          (2 * bn254.listSize : ℝ) / bn254.fieldSize) := by
      rw [ENNReal.ofReal_add (by norm_num [bn254]) (by norm_num [bn254])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal (by norm_num [bn254])

open Classical in
/-- The cubic-Goldilocks semantic MCA error plus its list term meets the shared local target. -/
theorem goldilocksCubic_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) +
        ENNReal.ofReal ((2 * goldilocksCubic.listSize : ℝ) /
          goldilocksCubic.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((goldilocksCubic.exceptionalCount : ℝ) /
          (goldilocksCubic.fieldSize - 1)) +
        ENNReal.ofReal ((2 * goldilocksCubic.listSize : ℝ) /
          goldilocksCubic.fieldSize) :=
      add_le_add
        (goldilocksCubic_concrete_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((goldilocksCubic.exceptionalCount : ℝ) /
          (goldilocksCubic.fieldSize - 1) +
        (2 * goldilocksCubic.listSize : ℝ) / goldilocksCubic.fieldSize) := by
      rw [ENNReal.ofReal_add (by norm_num [goldilocksCubic])
        (by norm_num [goldilocksCubic])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal (by norm_num [goldilocksCubic])

open Classical in
/-- The retuned semantic MCA error plus its list term meets the shared local target. -/
theorem bn254Scalar_retuned108_mcaError_add_list_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) +
        ENNReal.ofReal ((2 * 7155729507207006 : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  calc
    _ ≤ ENNReal.ofReal ((2 ^ 125 : ℝ) / (bn254.fieldSize - 1)) +
          ENNReal.ofReal ((2 * 7155729507207006 : ℝ) / bn254.fieldSize) :=
      add_le_add
        (bn254Scalar_retuned108_widthEight_affine_mcaError_le_count domain hs) le_rfl
    _ = ENNReal.ofReal ((2 ^ 125 : ℝ) / (bn254.fieldSize - 1) +
          (2 * 7155729507207006 : ℝ) / bn254.fieldSize) := by
      rw [ENNReal.ofReal_add (by norm_num [bn254]) (by norm_num [bn254])]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) :=
      ENNReal.ofReal_le_ofReal (by norm_num [bn254])

/-- All closed local arithmetic attached to the accepted original BN254 row. -/
structure BN254OriginalArithmetic : Prop where
  initialOodSlot :
    bn254.listSize * (bn254.listSize - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
      2 * bn254.fieldSize
  listSlot : 2 * bn254.listSize * 2 ^ 128 ≤ bn254.fieldSize
  affineMCAAndListSlot :
    (bn254.exceptionalCount : ℚ) / (bn254.fieldSize - 1) +
        (2 * bn254.listSize : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128
  openingSlot : 2 * (1 + bn254.queries) * 160 * 2 ^ 128 ≤ bn254.fieldSize
  querySelection :
    (bn254.powThreshold + 1) * bn254.agreementNumerator ^ bn254.queries * 2 ^ 128 ≤
        2 ^ 64 * bn254.n ^ bn254.queries ∧
      2 ^ 64 * bn254.n ^ (bn254.queries - 1) <
        (bn254.powThreshold + 1) *
          bn254.agreementNumerator ^ (bn254.queries - 1) * 2 ^ 128
  payloadLowerBounds :
    (bn254.nominalQueries - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 4032 ∧
      (bn254.zeroSlackQueryReference - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 2240

/-- All closed local arithmetic attached to the published cubic-Goldilocks row. -/
structure GoldilocksCubicArithmetic : Prop where
  initialOodSlot :
    goldilocksCubic.listSize * (goldilocksCubic.listSize - 1) *
          (goldilocksCubic.vectorSize - 1) ^ 2 * 2 ^ 128 ≤
      2 * goldilocksCubic.fieldSize ^ 2
  listSlot : 2 * goldilocksCubic.listSize * 2 ^ 128 ≤ goldilocksCubic.fieldSize
  affineMCAAndListSlot :
    (goldilocksCubic.exceptionalCount : ℚ) / (goldilocksCubic.fieldSize - 1) +
        (2 * goldilocksCubic.listSize : ℚ) / goldilocksCubic.fieldSize ≤
      (1 : ℚ) / 2 ^ 128
  openingSlot :
    2 * (1 + goldilocksCubic.queries) * 160 * 2 ^ 128 ≤ goldilocksCubic.fieldSize
  querySelection :
    (goldilocksCubic.powThreshold + 1) *
          goldilocksCubic.agreementNumerator ^ goldilocksCubic.queries * 2 ^ 128 ≤
        2 ^ 64 * goldilocksCubic.n ^ goldilocksCubic.queries ∧
      2 ^ 64 * goldilocksCubic.n ^ (goldilocksCubic.queries - 1) <
        (goldilocksCubic.powThreshold + 1) *
          goldilocksCubic.agreementNumerator ^ (goldilocksCubic.queries - 1) * 2 ^ 128
  payloadLowerBounds :
    (goldilocksCubic.nominalQueries - goldilocksCubic.queries) *
          (goldilocksCubic.interleavingWidth * goldilocksCubic.fieldBytes - 32) -
        (goldilocksCubic.initialOodSamples - 1) * goldilocksCubic.extensionBytes = 360 ∧
      (goldilocksCubic.zeroSlackQueryReference - goldilocksCubic.queries) *
          (goldilocksCubic.interleavingWidth * goldilocksCubic.fieldBytes - 32) -
        (goldilocksCubic.initialOodSamples - 1) * goldilocksCubic.extensionBytes = 104

/-- Closed local arithmetic for the accepted retuned 108-query BN254 option. -/
structure BN254Retuned108Arithmetic : Prop where
  initialOodSlot :
    (7155729507207006 : ℕ) * (7155729507207006 - 1) * (2097152 - 1) * 2 ^ 128 ≤
      2 * bn254.fieldSize
  affineMCAAndListSlot :
    (2 ^ 125 : ℚ) / (bn254.fieldSize - 1) +
        (2 * 7155729507207006 : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128
  openingSlot : (2 * (1 + 108) * 160 : ℕ) * 2 ^ 128 ≤ bn254.fieldSize
  querySelection :
    QueryMeetsTarget (2 ^ 64) 17350852076870155 491867 1048576 108 128
  grindingWork :
    (1082 : ℚ) / 1000 <
        (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) ∧
      (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) < (1083 : ℚ) / 1000
  extraPayloadLowerBound :
    (127 - 108 : ℕ) * (8 * 32 - 32) = (127 - 109) * (8 * 32 - 32) + 224

/-- The original BN254 closed arithmetic has no supplied count premise. -/
theorem bn254OriginalArithmetic : BN254OriginalArithmetic where
  initialOodSlot := bn254_changed_slots_meet_target.1
  listSlot := bn254_changed_slots_meet_target.2.2.1
  affineMCAAndListSlot := bn254_original_affineMCA_list_slot_le
  openingSlot := bn254_changed_slots_meet_target.2.2.2.2
  querySelection := bn254_query_selection
  payloadLowerBounds := bn254_payload_lower_bounds

/-- The cubic-Goldilocks closed arithmetic has no supplied count premise. -/
theorem goldilocksCubicArithmetic : GoldilocksCubicArithmetic where
  initialOodSlot := goldilocksCubic_changed_slots_meet_target.1
  listSlot := goldilocksCubic_changed_slots_meet_target.2.2.1
  affineMCAAndListSlot := goldilocksCubic_affineMCA_list_slot_le
  openingSlot := goldilocksCubic_changed_slots_meet_target.2.2.2.2
  querySelection := goldilocksCubic_query_selection
  payloadLowerBounds := goldilocksCubic_payload_lower_bounds

/-- The accepted retuned BN254 closed arithmetic has no supplied count premise. -/
theorem bn254Retuned108Arithmetic : BN254Retuned108Arithmetic where
  initialOodSlot := retuned_count_slots.2.1
  affineMCAAndListSlot := bn254_retuned108_affineMCA_list_slot_le
  openingSlot := retuned_count_slots.2.2
  querySelection := retuned_query108
  grindingWork := retuned_grinding_work
  extraPayloadLowerBound := retuned_extra_payload_lower_bound

/-! ## Canonical-field bundles -/

/-- Semantic coding bounds and local arithmetic for the accepted original BN254 row. -/
structure BN254OriginalCertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ BN254Scalar) : Prop where
  affineMCA :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1))
  affineMCAAndList :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) +
        ENNReal.ofReal ((2 * bn254.listSize : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → BN254Scalar)))
        (original109Radius : ℝ) ≤ (bn254.listSize : ℕ∞)
  arithmetic : BN254OriginalArithmetic

/-- Semantic coding bounds and local arithmetic for the published cubic-Goldilocks row. -/
structure GoldilocksCubicCertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ GoldilocksCubic) : Prop where
  affineMCA :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic.exceptionalCount : ℝ) /
        (goldilocksCubic.fieldSize - 1))
  affineMCAAndList :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) +
        ENNReal.ofReal ((2 * goldilocksCubic.listSize : ℝ) /
          goldilocksCubic.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → GoldilocksCubic)))
        (sharpGoldilocksCubicRadius : ℝ) ≤ (goldilocksCubic.listSize : ℕ∞)
  arithmetic : GoldilocksCubicArithmetic

/-- Semantic coding bounds and local arithmetic for the accepted retuned 108-query BN254 row. -/
structure BN254Retuned108CertifiedLocalBudget {s : ℕ}
    (domain : Fin 1048576 ↪ BN254Scalar) : Prop where
  affineMCA :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((2 ^ 125 : ℝ) / (bn254.fieldSize - 1))
  affineMCAAndList :
    mcaError (AffineSpaceGenerator BN254Scalar s)
          ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) +
        ENNReal.ofReal ((2 * 7155729507207006 : ℝ) / bn254.fieldSize) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128)
  interleavedList :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 8)
          (ReedSolomon.code domain 262144 : Set (Fin 1048576 → BN254Scalar)))
        (retuned108Radius : ℝ) ≤ (7155729507207006 : ℕ∞)
  arithmetic : BN254Retuned108Arithmetic

open Classical in
/-- Construct the complete local original-BN254 package from the evaluation domain alone. -/
theorem bn254Scalar_original109_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    BN254OriginalCertifiedLocalBudget (s := s) domain where
  affineMCA := bn254Scalar_original109_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := bn254Scalar_original109_mcaError_add_list_le domain hs
  interleavedList := bn254_original109_widthEight_lambda_le_sharp domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize])
  arithmetic := bn254OriginalArithmetic

open Classical in
/-- Construct the complete local cubic-Goldilocks package from the evaluation domain alone. -/
theorem goldilocksCubic_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    GoldilocksCubicCertifiedLocalBudget (s := s) domain where
  affineMCA := goldilocksCubic_concrete_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := goldilocksCubic_mcaError_add_list_le domain hs
  interleavedList := goldilocksCubic_widthEight_lambda_le_sharp domain (by
    right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize])
  arithmetic := goldilocksCubicArithmetic

open Classical in
/-- Construct the complete local retuned-BN254 package from the evaluation domain alone. -/
theorem bn254Scalar_retuned108_certifiedLocalBudget
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    BN254Retuned108CertifiedLocalBudget (s := s) domain where
  affineMCA := bn254Scalar_retuned108_widthEight_affine_mcaError_le_count domain hs
  affineMCAAndList := bn254Scalar_retuned108_mcaError_add_list_le domain hs
  interleavedList := retuned108_widthEight_lambda_le domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize])
  arithmetic := bn254Retuned108Arithmetic

end

end ArkLibExamples.ReedSolomon.ProveKit
