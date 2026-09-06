/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AffineAgreementBounds
import ArkLibExamples.ReedSolomon.ConcreteCurveMCA
import ArkLibExamples.ReedSolomon.Fields

/-!
# Sharp affine MCA endpoints for the ProveKit profiles

The concrete polynomial-curve construction gives an exceptional set for every pair of received
scalar words. At batching degree one, exact power agreement is exact line agreement. This module
uses that bridge, row-wise interleaving invariance, and the affine-space reduction to obtain MCA
bounds for the actual width-eight ProveKit codes.

The BN254 theorem covers the accepted original 109-query row, with agreement threshold `492831`
and radius `555745 / 1048576`. The cubic-Goldilocks theorem covers its published row, with
agreement threshold `512754` and radius `535822 / 1048576`. Their exceptional budgets are the
sharp counts recorded in `ProveKit.bn254.exceptionalCount` and
`ProveKit.goldilocksCubic.exceptionalCount`.

The canonical corollaries instantiate CompPoly's BN254 scalar field and Mathlib's degree-three
Goldilocks field. They quantify over every positive affine dimension and every family of received
width-eight words through `mcaError`; the only remaining input is the evaluation-domain embedding.

These are coding-theoretic MCA statements. Query sampling, proof-of-work grinding, transcript
generation, commitments, and composition with other protocol error terms are outside their scope.
-/

open Code CoreDefinitions LinearCode Polynomial
open ReedSolomon

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields

noncomputable section

/-- Relative decoding radius of the accepted original 109-query BN254 row. -/
def sharpBN254OriginalRadius : NNReal := 555745 / 1048576

/-- Relative decoding radius of the published cubic-Goldilocks row. -/
def sharpGoldilocksCubicRadius : NNReal := 535822 / 1048576

@[simp] theorem sharpBN254OriginalRadius_coe :
    (sharpBN254OriginalRadius : ℝ) = 555745 / 1048576 := by
  norm_num [sharpBN254OriginalRadius]

@[simp] theorem sharpGoldilocksCubicRadius_coe :
    (sharpGoldilocksCubicRadius : ℝ) = 535822 / 1048576 := by
  norm_num [sharpGoldilocksCubicRadius]

/-- The sharp BN254 curve certificate supplies the scalar exact-line interface. -/
theorem bn254_sharp_lineAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    LineExactAgreementBound domain 262144 492831
      bn254.exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
    (bn254.exceptionalCount : ℚ)
  intro values
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.bn254_exists_exceptional_exact_powerAgreement
      (E := AlgebraicClosure F) domain values
      (algebraMap F (AlgebraicClosure F)) hchar
  exact ⟨exceptional, by simpa only [bn254] using hcard, hgood⟩

/-- The sharp cubic-Goldilocks curve certificate supplies the scalar exact-line interface. -/
theorem goldilocksCubic_sharp_lineAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    LineExactAgreementBound domain 262144 512754
      goldilocksCubic.exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
    (goldilocksCubic.exceptionalCount : ℚ)
  intro values
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.goldilocksCubic_exists_exceptional_exact_powerAgreement
      (E := AlgebraicClosure F) domain values
      (algebraMap F (AlgebraicClosure F))
      hchar
  exact ⟨exceptional, by simpa only [goldilocksCubic] using hcard, hgood⟩

open Classical in
/-- The sharp original BN254 certificate gives the count-level affine MCA bound. -/
theorem bn254_original109_widthEight_affine_mcaError_le_count
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) /
        ((Fintype.card F : ℝ) - 1)) := by
  exact ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 492831) (bn254.exceptionalCount : ℝ)
      (bn254_sharp_lineAgreement domain hchar)
      sharpBN254OriginalRadius (by norm_num [bn254]) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpBN254OriginalRadius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpBN254OriginalRadius])
      (by rw [sharpBN254OriginalRadius_coe]; norm_num [bn254])

open Classical in
/-- The sharp original BN254 count-level bound is below the local 128-bit target. -/
theorem bn254_original109_widthEight_affine_mcaError_le_sharp
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := bn254_original109_widthEight_affine_mcaError_le_count domain hchar hs
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

open Classical in
/-- The sharp cubic-Goldilocks certificate gives the count-level affine MCA bound. -/
theorem goldilocksCubic_widthEight_affine_mcaError_le_count
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic.exceptionalCount : ℝ) /
        ((Fintype.card F : ℝ) - 1)) := by
  exact ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 512754) (goldilocksCubic.exceptionalCount : ℝ)
      (goldilocksCubic_sharp_lineAgreement domain hchar)
      sharpGoldilocksCubicRadius (by norm_num [goldilocksCubic]) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpGoldilocksCubicRadius])
      (by rw [← NNReal.coe_lt_coe]; norm_num [sharpGoldilocksCubicRadius])
      (by rw [sharpGoldilocksCubicRadius_coe]; norm_num [goldilocksCubic])

open Classical in
/-- The cubic-Goldilocks count-level bound is below the local 128-bit target. -/
theorem goldilocksCubic_widthEight_affine_mcaError_le_sharp
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F)
    (hcard : Fintype.card F = goldilocksCubic.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := goldilocksCubic_widthEight_affine_mcaError_le_count domain hchar hs
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [goldilocksCubic]))

open Classical in
/-- The canonical BN254 scalar field retains the exact count-level affine MCA bound. -/
theorem bn254Scalar_original109_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((bn254.exceptionalCount : ℝ) / (bn254.fieldSize - 1)) := by
  have hmca := bn254_original109_widthEight_affine_mcaError_le_count domain (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize]) hs
  rw [bn254Scalar_card] at hmca
  simpa [BN254.scalarFieldSize, bn254] using hmca

open Classical in
/-- The accepted original BN254 theorem on the canonical scalar field. -/
theorem bn254Scalar_original109_widthEight_affine_mcaError_le_sharp
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpBN254OriginalRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply bn254_original109_widthEight_affine_mcaError_le_sharp domain
  · right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize, bn254]
  · rw [bn254Scalar_card]
    norm_num [BN254.scalarFieldSize, bn254]
  · exact hs

open Classical in
/-- The canonical cubic Goldilocks field retains the exact count-level affine MCA bound. -/
theorem goldilocksCubic_concrete_widthEight_affine_mcaError_le_count
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) ≤
      ENNReal.ofReal ((goldilocksCubic.exceptionalCount : ℝ) /
        (goldilocksCubic.fieldSize - 1)) := by
  have hmca := goldilocksCubic_widthEight_affine_mcaError_le_count domain (by
    right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize]) hs
  rw [goldilocksCubic_card] at hmca
  simpa [Goldilocks.fieldSize, goldilocksCubic] using hmca

open Classical in
/-- The published cubic-Goldilocks theorem on the canonical degree-three field. -/
theorem goldilocksCubic_concrete_widthEight_affine_mcaError_le_sharp
    {s : ℕ} (domain : Fin 1048576 ↪ GoldilocksCubic) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator GoldilocksCubic s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8))
          (sharpGoldilocksCubicRadius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply goldilocksCubic_widthEight_affine_mcaError_le_sharp domain
  · right
    rw [goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize, goldilocksCubic]
  · rw [goldilocksCubic_card]
    norm_num [Goldilocks.fieldSize, goldilocksCubic]
  · exact hs

end

end ArkLibExamples.ReedSolomon.ProveKit
