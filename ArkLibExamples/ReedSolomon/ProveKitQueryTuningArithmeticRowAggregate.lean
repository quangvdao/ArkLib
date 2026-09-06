/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticRow1

/-!
# Retuned ProveKit row-slot aggregation

This module combines already checked subtotals after their kernel reductions have been serialized.
Keeping aggregation separate bounds peak memory in an ordinary build.
-/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

/-- Exact row-slot subtotal for grades 0 through 511. -/
theorem rowChunk0to3 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 0 512 = 931438581576600911872 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedRowTerm 0 128 128 128 128
    _ _ _ _ rowChunk0 rowChunk1 rowChunk2 rowChunk3

/-- Exact row-slot subtotal for grades 512 through 1023. -/
theorem rowChunk4to7 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 512 512 = 331190101726675861504 := by
  exact Finset.sumRangeFrom_four_eq queryTuningShiftedRowTerm 512 128 128 128 128
    _ _ _ _ rowChunk4 rowChunk5 rowChunk6 rowChunk7

/-- Exact row-slot subtotal for grades 0 through 1023. -/
theorem rowChunk0to7 :
    Finset.sumRangeFrom queryTuningShiftedRowTerm 0 1024 = 1262628683303276773376 := by
  exact Finset.sumRangeFrom_two_eq queryTuningShiftedRowTerm 0 512 512 _ _
    rowChunk0to3 rowChunk4to7

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
