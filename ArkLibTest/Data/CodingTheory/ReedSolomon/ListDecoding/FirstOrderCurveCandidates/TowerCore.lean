/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.TowerCore
import Mathlib.Algebra.Field.ZMod

/-! Parameter construction and localization preserve nonreduced fibers in characteristic two. -/

namespace ArkLibTest.FirstOrderCurveTowerCore

open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates.TowerCore

private abbrev F := ZMod 2

private def tower (m : ℕ) : TowerRepresentation (F := F) :=
  parameterTower CPolynomial.X (CPolynomial.X ^ m)

private theorem tower_wellFormed (m : ℕ) (hm : 0 < m) :
    (tower m).NonreducedWellFormed 0 := by
  have hG : (CPolynomial.X : CPolynomial F).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  have hGpos : 0 < (CPolynomial.X : CPolynomial F).natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly, Polynomial.natDegree_X]
    exact Nat.zero_lt_one
  have hh : (CPolynomial.X ^ m : CPolynomial (CPolynomial F)).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow m
  apply parameterTower_wellFormed _ _ hG
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := F)).squarefree
  · exact hGpos
  · exact hh
  · apply reducedFiber_positive _ _ hG hGpos hh
    simpa only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow,
      CPolynomial.X_toPoly, Polynomial.natDegree_X_pow] using hm

private def checkTower (m : ℕ) (hm : 0 < m) : Bool :=
  let r := tower m
  let kept := localizeFiber r (CPolynomial.X + 1) (tower_wellFormed m hm)
  let removed := localizeFiber r CPolynomial.X (tower_wellFormed m hm)
  r.coefficients.isEmpty &&
    (r.fiber == (CPolynomial.X ^ m : CPolynomial (CPolynomial F))) &&
    (kept.map TowerRepresentation.dimension == [m]) &&
    kept.all (fun child => child.coefficients.isEmpty) && removed.isEmpty

-- Full nilpotent multiplicity, empty payload, unit retention, and nilpotent removal.
example : checkTower 2 (by decide) = true := by decide +kernel
example : checkTower 3 (by decide) = true := by decide +kernel

end ArkLibTest.FirstOrderCurveTowerCore
