/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit
import Mathlib.Algebra.Field.ZMod

/-! Executed primary-factor retention, including fibers above the characteristic. -/

namespace ArkLibTest.PrimarySplit

open CompPoly
open ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

private abbrev F := ZMod 2

private def v : CPolynomial F := CPolynomial.X

private def doubleRoot : CPolynomial F := v ^ 2

private def mixed : CPolynomial F := v ^ 2 * (v - 1) ^ 3

-- A nonzero nilpotent retains the entire double root.
example : (nilFactor doubleRoot v == doubleRoot) = true := by decide +kernel

example : (unitFactor doubleRoot v == 1) = true := by decide +kernel

-- The fiber degree is five in characteristic two: each multiplicity is preserved.
example : (mixed.natDegree == 5) = true := by decide +kernel

example : (nilFactor mixed v == v ^ 2) = true := by decide +kernel

example : (unitFactor mixed v == (v - 1) ^ 3) = true := by decide +kernel

-- The complementary residual selects the other complete primary component.
example : (nilFactor mixed (v - 1) == (v - 1) ^ 3) = true := by decide +kernel

example : (unitFactor mixed (v - 1) == v ^ 2) = true := by decide +kernel

end ArkLibTest.PrimarySplit
