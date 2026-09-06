/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AffineAgreementBounds
import ArkLibExamples.ReedSolomon.Fields
import ArkLibExamples.ReedSolomon.ProveKitInterleaving

/-!
# Affine-space MCA consequences for the ProveKit profiles

ProveKit combines more than two received words in its affine batching step. The scalar exact-line
certificates and affine-line interleaving theorem therefore need one final affine-space transfer.
This module applies that transfer to the actual width-eight Reed--Solomon rows.

## Reading the statements

The original profile uses agreement `492831`, radius `555745 / 1048576`, and exceptional budget
`2^115`. The retuned profile uses agreement `491867`, radius `556709 / 1048576`, and budget
`2^125`. For every positive affine dimension `s`, the generic theorems assume only that `F` has
the pinned BN254 cardinality and satisfies the characteristic condition. Both conclusions are
the full `mcaError` bound `2^-128`, hence quantify over all families of `s + 1` received
width-eight words.

The canonical corollaries use `ConcreteFields.BN254Scalar`. They discharge the field cardinality
and characteristic internally, leaving only the evaluation-domain embedding and `1 ≤ s` as
inputs.

## Mathematical scope

The affine-to-line reduction incurs the denominator `|F| - 1`; the closed BN254 arithmetic proves
that both exceptional budgets still meet the target. Query sampling, proof-of-work grinding,
commitment openings, and composition with other protocol errors remain outside these statements.
-/

open Code CoreDefinitions LinearCode
open ReedSolomon

namespace ArkLibExamples.ReedSolomon.ProveKit

noncomputable section

open ConcreteFields

open Classical in
/-- The original 109-query profile meets the target for every positive affine dimension. -/
theorem original109_widthEight_affine_mcaError_le
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (original109Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 492831) (2 ^ 115)
      (original109_lineAgreement domain hchar) original109Radius
      (by norm_num) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [original109Radius_coe]; norm_num)
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

open Classical in
/-- The retuned 108-query profile also meets the target for every positive affine dimension. -/
theorem retuned108_widthEight_affine_mcaError_le
    {F : Type} [Field F] [Fintype F] {s : ℕ}
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 1048576 < ringChar F)
    (hcard : Fintype.card F = bn254.fieldSize) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  have hmca := ReedSolomon.mcaError_affineSpace_interleaved_le_of_exactAgreement domain
    (t := 8) (s := s) (A := 491867) (2 ^ 125)
      (retuned_lineAgreement domain (hchar.imp_right (by omega))) retuned108Radius
      (by norm_num) hs
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [← NNReal.coe_lt_coe]; norm_num)
      (by rw [retuned108Radius_coe]; norm_num)
  rw [hcard] at hmca
  exact hmca.trans (ENNReal.ofReal_le_ofReal (by norm_num [bn254]))

open Classical in
/-- On the canonical BN254 scalar field, the original affine theorem needs only an evaluation
domain and a positive affine dimension. -/
theorem original109_bn254Scalar_widthEight_affine_mcaError_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (original109Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply original109_widthEight_affine_mcaError_le domain
  · right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize]
  · rw [bn254Scalar_card]
    norm_num [BN254.scalarFieldSize, bn254]
  · exact hs

open Classical in
/-- The retuned affine theorem has the same premise-free field specialization. -/
theorem retuned108_bn254Scalar_widthEight_affine_mcaError_le
    {s : ℕ} (domain : Fin 1048576 ↪ BN254Scalar) (hs : 1 ≤ s) :
    mcaError (AffineSpaceGenerator BN254Scalar s)
        ((ReedSolomon.code domain 262144) ^⋈ (Fin 8)) (retuned108Radius : ℝ) ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ 128) := by
  apply retuned108_widthEight_affine_mcaError_le domain
  · right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize]
  · rw [bn254Scalar_card]
    norm_num [BN254.scalarFieldSize, bn254]
  · exact hs

end

end ArkLibExamples.ReedSolomon.ProveKit
