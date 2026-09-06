/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticRow2B

/-! # Retuned ProveKit row-slot arithmetic, part 2 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 1152 through 1279. -/
theorem rowChunk9 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1152 128 = 0 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 1280 through 1407. -/
theorem rowChunk10 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1280 128 = 0 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 1408 through 1441. -/
theorem rowChunk11 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1408 34 = 0 := by decide

/-- Exact row-slot subtotal for grades 0 through 1407. -/
theorem rowChunk0to10 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 0 1408 = 1263885967595824742400 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedRowTerm 0 1024 128 128 128
    _ _ _ _ rowChunk0to7 rowChunk8 rowChunk9 rowChunk10

/-- Exact row-slot total over all 1,442 active grades. -/
theorem queryTuningShiftedRowTotal :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 0 1442 = 1263885967595824742400 := by
  exact Finset.sumRangeFrom_two_eq queryTuningShiftedRowTerm 0 1408 34 _ _
    rowChunk0to10 rowChunk11

/-- The complete shifted row-slot count for the retuned support. -/
theorem queryTuningShiftedRowSlots :
    firstOrderCurveShiftedRowSlotBound 262143 491867 768 349 1441 1048576 1 17054177 =
      1263885967595824742400 := by
  have hterm :
      (fun t ↦ 1048576 * firstOrderGradedRankBound 262143 491867 768 349 t *
        (17054177 + 1 - 1 * t)) = queryTuningShiftedRowTerm := by
    funext t
    simp [queryTuningShiftedRowTerm]
  exact (firstOrderCurveShiftedRowSlotBound_eq_sumRangeFrom
    262143 491867 768 349 1441 1048576 1 17054177).trans
      ((congrArg (fun f ↦ Finset.sumRangeFrom f 0 1442) hterm).trans
        queryTuningShiftedRowTotal)

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
