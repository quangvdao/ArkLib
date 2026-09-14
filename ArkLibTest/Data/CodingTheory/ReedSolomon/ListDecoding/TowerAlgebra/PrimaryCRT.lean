/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimaryCRT
import Mathlib.Algebra.Field.ZMod

/-! # Public scalar CRT interface and zero-dimensional factor checks -/

namespace ArkLibTest.PrimaryCRT

open CompPoly Polynomial ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

private abbrev F := ZMod 2

-- The nilpotent residual retains the complete double root, with a zero-ring complement.
example : unitFactor (CPolynomial.X ^ 2 : CPolynomial F) CPolynomial.X = 1 := by
  decide +kernel

-- The public representative formula elaborates without exposing the CRT implementation.
example (h e : CPolynomial F) (hh : h.monic) (p : F[X]) :
    primarySplitEquiv h e hh (AdjoinRoot.mk h.toPoly p) =
      (AdjoinRoot.mk (nilFactor h e).toPoly p, AdjoinRoot.mk (unitFactor h e).toPoly p) := by
  simp [primarySplitEquiv_mk]

-- A unit parent is allowed: its entire quotient, and both factor quotients, have dimension zero.
example : Nonempty
    (AdjoinRoot (1 : CPolynomial F).toPoly ≃+*
      AdjoinRoot (nilFactor 1 (0 : CPolynomial F)).toPoly ×
      AdjoinRoot (unitFactor 1 (0 : CPolynomial F)).toPoly) :=
  ⟨primarySplitEquiv 1 0 (by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]
    exact Polynomial.monic_one)⟩

end ArkLibTest.PrimaryCRT
