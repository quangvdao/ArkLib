/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.PreparedCoverage
import Mathlib.Algebra.Field.ZMod

namespace ArkLibTest.FirstOrderPreparedCoverage

open CompPoly CPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

private def chart : ChartData E 1 2 :=
  { center := 1
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2 * (CMvPolynomial.X 1 + 1)
    separant := CMvPolynomial.X 1 + 1
    denominator := CMvPolynomial.X 1 + 1
    numerators := ![1, 1 + CMvPolynomial.X 1] }

private def h : CPolynomial (CPolynomial E) := CPolynomial.X ^ 2
private def gs : List (CPolynomial (CPolynomial E)) := [CPolynomial.C CPolynomial.X]
private def trace : FilterCore.Trace E := ⟨[CPolynomial.X ^ 2], CPolynomial.X ^ 2,
  some CPolynomial.X⟩

private instance : DecidableEq (FilterCore.Trace E) := fun a b =>
  decidable_of_iff (a.coefficients = b.coefficients ∧
    a.thresholdPolynomial = b.thresholdPolynomial ∧ a.base = b.base) (by
      cases a; cases b; simp)

private theorem htrace : FilterCore.run 2 id 2 2 h gs = some trace := by
  decide +kernel

private theorem hmonic : h.monic := by
  rw [h, CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  exact Polynomial.monic_X.pow 2

private def family := PreparedCoverage.fromFilter 2 id (by intro a; exact ZMod.pow_card a)
  chart 2 h gs trace htrace CPolynomial.X rfl (by decide +kernel) hmonic (by decide +kernel)

-- The retained fiber differs from the original cubic chart and keeps its multiplicity two.
example : family.map (fun c => c.val.dimension) = [2] := by decide +kernel

-- Inverting the true denominator and translating center 1 retains the nilpotent constant slot.
example : (family.map fun c => c.val.coefficients) == [[1, CPolynomial.X]] := by decide +kernel

example : h ∣ (chartPolynomials chart).equation := by
  refine ⟨CPolynomial.X + 1, ?_⟩
  decide +kernel

#print axioms PreparedCoverage.representedBy_of_constructor_threshold
#print axioms PreparedCoverage.fromFilter_dimension_le

end ArkLibTest.FirstOrderPreparedCoverage
