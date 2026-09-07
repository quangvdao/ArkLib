/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BivariateMultiplicity
import Mathlib.Algebra.Field.ZMod

/-! Multiplicity clients distinguish total Hasse order from the ordinary derivative in
characteristic two, and check both polynomial axes. -/

open Polynomial Polynomial.Bivariate

example : (some 2 : Option ℕ) ≤ rootMultiplicity
    (monomial 2 (C 1) : Polynomial (Polynomial (ZMod 2))) 0 0 := by
  apply (le_rootMultiplicity_iff_of_ne_zero _ (by simp) _ _ _).mpr
  intro r s hrs
  have hs : 2 ≠ s := by omega
  simp [shift, coeff_monomial, hs]

example : ¬ (some 2 : Option ℕ) ≤ rootMultiplicity
    (C X + monomial 2 (C 1) : Polynomial (Polynomial (ZMod 2))) 0 0 := by
  have hQ : (C X + monomial 2 (C 1) : Polynomial (Polynomial (ZMod 2))) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial (Polynomial (ZMod 2)) => p.coeff 2) h
    simp at hc
  rw [le_rootMultiplicity_iff_of_ne_zero _ hQ]
  intro h
  have hx := h 1 0 (by decide)
  simp [shift] at hx
