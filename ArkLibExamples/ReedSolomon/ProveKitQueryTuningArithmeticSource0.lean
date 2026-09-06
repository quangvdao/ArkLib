/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticRow2

/-! # Retuned ProveKit source-slot arithmetic, part 0 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 0 through 127. -/
theorem sourceChunk0 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 0 128 = 50062226974214430560 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 128 through 255. -/
theorem sourceChunk1 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 128 128 = 136860068682172714848 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 256 through 383. -/
theorem sourceChunk2 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 256 128 = 202062229877956938167 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 384 through 511. -/
theorem sourceChunk3 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 384 128 = 198981881101023540800 := by decide

/-- Exact source-slot subtotal for grades 0 through 511. -/
theorem sourceChunk0to3 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 0 512 = 587966406635367624375 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedSourceTerm 0 128 128 128 128
    _ _ _ _ sourceChunk0 sourceChunk1 sourceChunk2 sourceChunk3

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
