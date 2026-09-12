/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting

/-!
# Acceptance clients for first-order column-height counting

The concrete parameters below have four support columns and seven coefficient slots at height
one, strictly more than the two scalar equations allowed by a one-row budget.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

example : firstOrderHeightSlotCount 2 3 1 0 1 1 = 7 := by
  decide

example : firstOrderColumnSlotCount 2 3 1 0 1 1 = 7 := by
  rw [firstOrderColumnSlotCount_eq_heightSlotCount (by omega : 0 < 2)]
  decide

example : 1 * (1 + 1) < firstOrderHeightSlotCount 2 3 1 0 1 1 := by
  decide

open SymbolicReceivedInterpolation

example : Function.Injective
    (SymbolicWeightedSupportInterpolation.firstOrderColumns
      (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1)) :=
  SymbolicWeightedSupportInterpolation.firstOrderColumns_injective

example (j : Fin (Fintype.card ↑(firstOrderExponents 2 3 1 0 1))) :
    (SymbolicWeightedSupportInterpolation.firstOrderColumns
      (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) j).exponent ∈
        firstOrderExponents 2 3 1 0 1 :=
  SymbolicWeightedSupportInterpolation.firstOrderColumns_eligible j

end ReedSolomon.HiddenDerivative
