/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticRowAggregate

/-! # Retuned ProveKit boundary row-slot arithmetic, part 1 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- These short boundary chunks keep kernel reduction below the ordinary build memory envelope.
theorem rowChunk8a :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1024 16 = 536660197993611264 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8b :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1040 16 = 356986345790373888 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8c :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1056 16 = 213934115278290944 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
theorem rowChunk8d :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1072 16 = 107503403378147328 := by decide

/-- Exact row-slot subtotal for grades 1024 through 1087. -/
theorem rowChunk8aToD :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 1024 64 = 1215084062440423424 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedRowTerm 1024 16 16 16 16
    _ _ _ _ rowChunk8a rowChunk8b rowChunk8c rowChunk8d

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
