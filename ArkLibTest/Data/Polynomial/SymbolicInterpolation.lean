/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolation
import Mathlib.Algebra.Field.ZMod

/-! Characteristic-two acceptance for symbolic interpolation and its Hasse constraints. -/

open Polynomial Polynomial.SymbolicInterpolation

-- The second Hasse derivative can be nonzero in characteristic two.
example : hasseConstraint (C (1 : ZMod 2)) (C 1) 2 0 5
    (monomial 1 (monomial 3 (monomial 5 1))) = 1 := by
  change (((Bivariate.shift (monomial 1 (monomial 3 (monomial 5 1)))
    (C (1 : ZMod 2)) (C 1)).coeff 0).coeff 2).coeff 5 = 1
  rw [shift_monomial_coeff]
  norm_num
  decide

-- Exact surplus constructs a polynomial in characteristic two, with the intended axes
-- and every Hasse constraint, including Z coefficients beyond the finite scalar system.
example : ∃ Q : Polynomial (Polynomial (Polynomial (ZMod 2))), Q ≠ 0 ∧
    (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
      j < 4 ∧ i + 2 * j < 9 ∧ j + h < 6) ∧
    ∀ _a : Fin 1, ∀ r s, r + s < 3 →
      ((Bivariate.shift Q (C (0 : ZMod 2)) Polynomial.X).coeff s).coeff r = 0 := by
  exact exists_polynomial_of_card_surplus 2 9 4 6 1 3
    (fun _ => 0) (fun _ => Polynomial.X) (by intro a; simp) (by decide)
