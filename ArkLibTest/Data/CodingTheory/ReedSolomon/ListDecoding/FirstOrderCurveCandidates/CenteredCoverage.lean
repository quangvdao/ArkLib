/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.CenteredCoverage
import Mathlib.Algebra.Field.ZMod

namespace ArkLibTest.FirstOrderCenteredCoverage

open CompPoly CPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

-- These coefficients encode P(2+Z)=4+3Z+Z² over F₅, so P=X²+4X+2.
example : CoefficientList.centeredToDescending (2 : ZMod 5) [4, 3, 1] = [1, 4, 2] :=
  by decide +kernel

example : CoefficientList.centeredToDescending (0 : ZMod 5) [4, 3, 1] = [1, 3, 4] :=
  by decide +kernel

example : CoefficientList.centeredToDescending (2 : ZMod 5) [] = [] := by decide +kernel

private abbrev E := ZMod 2

-- At the geometric point v=0 this is the Taylor expansion of X at center 1.
private def chart : ChartData E 1 2 :=
  { center := 1
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1 + CMvPolynomial.X 1
    numerators := ![1, 1 + CMvPolynomial.X 1] }

private def tower : TowerRepresentation (F := E) :=
  TowerCore.parameterTower CPolynomial.X (CPolynomial.X ^ 2)

private theorem weak : tower.NonreducedWellFormed 0 := by
  have hG : (CPolynomial.X : CPolynomial E).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  apply TowerCore.parameterTower_wellFormed _ _ hG
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := E)).squarefree
  · decide +kernel
  · rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow 2
  · decide +kernel

private theorem weak_list : ∀ r ∈ [tower], r.NonreducedWellFormed 0 := by
  intro r hr
  simpa using (show r = tower from by simpa using hr) ▸ weak

-- The nilpotent constant coefficient survives the exact change of basis.
example : ((CenteredCoverage.components chart [tower] weak_list).map
    fun c => c.val.coefficients) == [[1, CPolynomial.X]] := by decide +kernel

private def domain : Fin 2 ↪ E := ⟨fun i => i, fun _ _ h => h⟩

-- Both reversal and the nonzero center translation are necessary for this full recovery.
example : CenteredCoverage.recover chart [tower] weak_list domain (fun i => domain i) 2 ==
    [[1, 0]] := by decide +kernel

example : (CenteredCoverage.components { chart with denominator := CMvPolynomial.X 1 }
    [tower] weak_list).isEmpty = true := by decide +kernel

#print axioms CoefficientList.centeredToDescending_taylor
#print axioms CenteredMaterialize.run_specialize_of_taylor
#print axioms CenteredCoverage.constructor_taylor_coefficients
#print axioms CenteredCoverage.recover_exact_of_taylor_coverage

end ArkLibTest.FirstOrderCenteredCoverage
