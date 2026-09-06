/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting

/-!
# Chunked arithmetic for the retuned ProveKit shifted surplus

This module starts a dependency chain of bounded kernel reductions. Splitting the 1,442-grade
calculation keeps each ordinary Lean build within a predictable memory envelope.
-/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

/-- The degree-`t` shifted row contribution for the retuned BN254 support. -/
def queryTuningShiftedRowTerm (t : ℕ) : ℕ :=
  1048576 * firstOrderGradedRankBound 262143 491867 768 349 t *
    (17054177 + 1 - t)

/-- The degree-`t` shifted source contribution for the retuned BN254 support. -/
def queryTuningShiftedSourceTerm (t : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (min t 349 + 1),
    (768 * 491867 + b - 262143 * t) * (17054177 + 1 - t)

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 0 through 127. -/
theorem rowChunk0 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 0 128 = 100885993118152785920 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 128 through 255. -/
theorem rowChunk1 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 128 128 = 250893734478530740224 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 256 through 383. -/
theorem rowChunk2 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 256 128 = 321682154405029216256 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 384 through 511. -/
theorem rowChunk3 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 384 128 = 257976699574888169472 := by decide

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
