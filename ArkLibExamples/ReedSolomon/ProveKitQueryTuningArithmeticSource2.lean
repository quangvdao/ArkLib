/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticSource1

/-! # Retuned ProveKit source-slot arithmetic, part 2 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 1024 through 1151. -/
theorem sourceChunk8 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 1024 128 = 70800587078955316800 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 1152 through 1279. -/
theorem sourceChunk9 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 1152 128 = 45165482757346817600 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 1280 through 1407. -/
theorem sourceChunk10 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 1280 128 = 19530763263340033600 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact source-slot subtotal for grades 1408 through 1441. -/
theorem sourceChunk11 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 1408 34 = 878946814992883175 := by decide

/-- Exact source-slot subtotal for grades 1024 through 1441. -/
theorem sourceChunk8to11 :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 1024 418 = 136375779914635051175 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedSourceTerm 1024 128 128 128 34
    _ _ _ _ sourceChunk8 sourceChunk9 sourceChunk10 sourceChunk11

/-- Exact source-slot total over all 1,442 active grades. -/
theorem queryTuningShiftedSourceTotal :
    Finset.sumRangeFrom queryTuningShiftedSourceTerm 0 1442 = 1263903274633943238750 := by
  exact Finset.sumRangeFrom_two_eq queryTuningShiftedSourceTerm 0 1024 418 _ _
    sourceChunk0to7 sourceChunk8to11

/-- The complete shifted source-slot count for the retuned support. -/
theorem queryTuningShiftedSourceSlots :
    firstOrderCurveShiftedHeightSlotCount 262143 491867 768 349 1441 1 17054177 =
      1263903274633943238750 := by
  have hterm :
      (fun t ↦ ∑ b ∈ Finset.range (min t 349 + 1),
        (768 * 491867 + b - 262143 * t) * (17054177 + 1 - 1 * t)) =
          queryTuningShiftedSourceTerm := by
    funext t
    simp [queryTuningShiftedSourceTerm]
  exact (firstOrderCurveShiftedHeightSlotCount_eq_sumRangeFrom
    262143 491867 768 349 1441 1 17054177).trans
      ((congrArg (fun f ↦ Finset.sumRangeFrom f 0 1442) hterm).trans
        queryTuningShiftedSourceTotal)

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
