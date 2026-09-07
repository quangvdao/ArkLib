/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.SymbolicInterpolation
import Mathlib.Algebra.Field.ZMod

/-! The paper-facing endpoint constructs an affine interpolant in characteristic two. -/

open Polynomial

example : ∃ Q : Polynomial (Polynomial (Polynomial (ZMod 2))), Q ≠ 0 ∧
    (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
      (j : ℝ) < 7 / 2 ∧ ((i + j : ℕ) : ℝ) < 7 / 2 ∧
        ((j + h : ℕ) : ℝ) < 49 / 12) ∧
    ∀ _a : Fin 1, (some 3 : Option ℕ) ≤ Bivariate.rootMultiplicity Q
      (C (0 : ZMod 2)) (C 1 + Polynomial.X * C 1) := by
  have h := ProximityGap.exists_affine_interpolant 1 1 3
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => (0 : ZMod 2)) (fun _ => 1) (fun _ => 1)
  norm_num at h ⊢
  exact h
