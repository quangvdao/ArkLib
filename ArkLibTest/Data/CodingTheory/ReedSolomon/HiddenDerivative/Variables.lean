/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Variables
import Mathlib.Tactic.FinCases

/-! # Boundary regression tests -/

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

/-! ### Boundary canaries -/

/-- At order zero the auxiliary variable has contact weight zero.  This is intentional: the
order-zero interpolation argument must not infer finite dimensionality from this weight alone. -/
theorem localContactWeight_order_zero_canary :
    localContactWeight 0 (localE 0) = 0 := rfl

/-- At derivative order two, the zero-based local indices give weights zero and one to `Y₁`
and `Y₂`, respectively. -/
theorem localHigherJetWeight_order_two_canary :
    localHigherJetWeight 2 (localY (0 : Fin 2)) = 0 ∧
      localHigherJetWeight 2 (localY (1 : Fin 2)) = 1 := by
  decide

/-- At derivative order two, `T * E²` has contact order `1 + 2*2 = 5`. -/
theorem localContactOrder_order_two_canary :
    let e : LocalVariable 2 →₀ ℕ :=
      Finsupp.single (localT 2) 1 + Finsupp.single (localE 2) 2
    localContactOrder 2 e = 5 := by
  simp [localContactOrder, Finsupp.weight_single]

end ReedSolomon.HiddenDerivative
