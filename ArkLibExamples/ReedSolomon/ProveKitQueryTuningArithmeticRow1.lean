/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmetic

/-! # Retuned ProveKit row-slot arithmetic, part 1 -/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 512 through 639. -/
theorem rowChunk4 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 512 128 = 169190075876631379968 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 640 through 767. -/
theorem rowChunk5 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 640 128 = 99094175947486658560 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 768 through 895. -/
theorem rowChunk6 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 768 128 = 47749681020212871168 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit finite slot subtotal exceeds the default reduction budget.
/-- Exact row-slot subtotal for grades 896 through 1023. -/
theorem rowChunk7 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 896 128 = 15156168882344951808 := by decide

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
