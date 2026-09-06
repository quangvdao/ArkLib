/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticSource0

/-! # Retuned ProveKit source-slot arithmetic, part 1 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 512 through 639. -/
theorem sourceChunk4 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 512 128 = 173344852641406465600 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 640 through 767. -/
theorem sourceChunk5 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 640 128 = 147708209009391105600 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 768 through 895. -/
theorem sourceChunk6 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 768 128 = 122071950204977460800 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 896 through 1023. -/
theorem sourceChunk7 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 896 128 = 96436076228165531200 := by decide

/-- Exact source-slot subtotal for grades 512 through 1023. -/
theorem sourceChunk4to7 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 512 512 = 539561088083940563200 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedSourceTerm 512 128 128 128 128
    _ _ _ _ sourceChunk4 sourceChunk5 sourceChunk6 sourceChunk7

/-- Exact source-slot subtotal for grades 0 through 1023. -/
theorem sourceChunk0to7 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 0 1024 = 1127527494719308187575 := by
  exact Finset.sumRangeFrom_two_eq queryTuningShiftedSourceTerm 0 512 512 _ _
    sourceChunk0to3 sourceChunk4to7

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
