/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicCurveSurplus

/-! The curve budget rounds the product: `ceil (2 * 49/12) = 9`, while
`2 * ceil (49/12) = 10`. This client exercises the smaller budget. -/

open Polynomial.SymbolicInterpolation

example : (curveConstraintSupport 2 3 9).card <
    (curveMonomialSupport 2 1 4 4 9).card := by
  have h := card_curve_constraints_lt_monomials 2 1 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hy : ⌈(7 / 2 : ℝ)⌉₊ = 4 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  have hz : ⌈(49 / 6 : ℝ)⌉₊ = 9 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num at h
  rwa [hy, hz] at h
