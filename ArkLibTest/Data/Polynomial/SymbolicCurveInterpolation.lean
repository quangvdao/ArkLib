/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicCurveInterpolation
import Mathlib.Algebra.Field.ZMod

/-! Curve-degree scaling and inseparable characteristic-two substitution checks. -/

open Polynomial Polynomial.SymbolicInterpolation

example : (curveMonomialSupport 2 2 9 4 (2 * 6)).card = 236 := by
  rw [card_curveMonomialSupport]
  norm_num [card_monomialSupport, Finset.sum_range_succ]

example : (curveConstraintSupport 2 3 (2 * 6)).card = 64 := by decide

example : ⟨3, (2, 5)⟩ ∈ curveMonomialSupport 2 2 9 4 12 := by decide

example : ⟨3, (2, 6)⟩ ∉ curveMonomialSupport 2 2 9 4 12 := by decide

-- The curve Y = Z² is inseparable in characteristic two. The budget 11 is not divisible
-- by its degree, so this also checks the independently rounded budget interface.
example : ∃ Q : Polynomial (Polynomial (Polynomial (ZMod 2))), Q ≠ 0 ∧
    (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
      j < 4 ∧ i + 2 * j < 9 ∧ 2 * j + h < 11) ∧
    ∀ _a : Fin 1, ∀ r s, r + s < 3 →
      ((Bivariate.shift Q (C (0 : ZMod 2)) (Polynomial.X ^ 2)).coeff s).coeff r = 0 := by
  exact exists_curve_polynomial_of_card_surplus 2 2 9 4 11 1 3
    (fun _ => 0) (fun _ => Polynomial.X ^ 2) (by intro a; simp)
    (by norm_num [card_curveConstraintSupport_sum, card_curveMonomialSupport_sum,
      Finset.sum_range_succ])
