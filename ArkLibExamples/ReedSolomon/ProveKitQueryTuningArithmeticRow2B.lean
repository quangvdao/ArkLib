/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticRow2A

/-! # Retuned ProveKit boundary row-slot arithmetic, part 2 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8e :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1088 16 = 37694107010727936 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8f :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1104 16 = 4506123096817664 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8g :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1120 16 = 0 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8h :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1136 16 = 0 := by decide

/-- Exact row-slot subtotal for grades 1088 through 1151. -/
theorem rowChunk8eToH :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1088 64 = 42200230107545600 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedRowTerm 1088 16 16 16 16
    _ _ _ _ rowChunk8e rowChunk8f rowChunk8g rowChunk8h

/-- Exact row-slot subtotal for grades 1024 through 1151. -/
theorem rowChunk8 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1024 128 = 1257284292547969024 := by
  exact Finset.sumRangeFrom_two_eq queryTuningShiftedRowTerm 1024 64 64 _ _
    rowChunk8aToD rowChunk8eToH

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
