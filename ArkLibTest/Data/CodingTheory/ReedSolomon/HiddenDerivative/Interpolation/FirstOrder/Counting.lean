/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Counting

/-!
# Acceptance clients for the first-order dimension count

The final example checks a small nonvacuous certificate through the generic interpolation
theorem: four support columns satisfy one actual local constraint rank budget.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

example : firstOrderDimensionCount 2 3 1 0 1 = 4 := by
  decide

example {F : Type*} [Field F] (centers received : Fin 1 → F) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧
      Q ∈ firstOrderSpace F 2 3 1 0 1 ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount
    (by omega : 1 < 2) centers received
  decide

end ReedSolomon.HiddenDerivative
