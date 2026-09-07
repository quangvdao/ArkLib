/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.SymbolicCurveInterpolation
import Mathlib.Algebra.Field.ZMod

/-! The actual curve endpoint works for the inseparable curve `Y = Z²` over `F₂`. -/

open Polynomial

-- M*D_Z = 49/6, hence the integer Z budget is 9, not M*ceil(D_Z) = 10.
example : ∃ Q : Polynomial (Polynomial (Polynomial (ZMod 2))), Q ≠ 0 ∧
    (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
      (j : ℝ) < 7 / 2 ∧ ((i + j : ℕ) : ℝ) < 7 / 2 ∧
        ((2 * j + h : ℕ) : ℝ) < 49 / 6) ∧
    ∀ _a : Fin 1, (some 3 : Option ℕ) ≤ Bivariate.rootMultiplicity Q
      (C (0 : ZMod 2)) (Polynomial.X ^ 2) := by
  have h := ProximityGap.exists_curve_interpolant 2 1 1 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ => (0 : ZMod 2)) (fun _ => Polynomial.X ^ 2) (by intro a; simp)
  norm_num at h ⊢
  exact h
