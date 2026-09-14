/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.LocalizeFiber
import Mathlib.Algebra.Field.ZMod

/-! Executed localization preserves entire nilpotent fibers, including above the characteristic. -/

namespace ArkLibTest.LocalizeFiber

open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev F := ZMod 2

private def source (m : ℕ) : TowerRepresentation (F := F) :=
  ⟨CPolynomial.X, CPolynomial.X ^ m, []⟩

private def tower (m : ℕ) : TowerRepresentation (F := F) :=
  restrictTower (source m) CPolynomial.X (CPolynomial.X ^ m)

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
  apply restrictTower_nonreducedWellFormed (source m) CPolynomial.X (CPolynomial.X ^ m) hG
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := F)).squarefree
  · simp only [TowerRepresentation.dimension, restrictTower]
    rw [natDegree_reduceBase CPolynomial.X hG hGpos (CPolynomial.X ^ m) hh]
    simpa only [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly,
      CPolynomial.toPoly_pow, Polynomial.natDegree_X_pow, Polynomial.natDegree_X, one_mul]
      using hm.ne'
  · exact TowerRepresentation.monic_reduceBase hG hGpos hh
  · rfl

private def checks1 : Bool := Id.run do
  for m in [2, 3] do
    -- The branch uses a checked proof of positivity only; there is no characteristic bound.
    if hm : 0 < m then
      let kept := localizeFiber (tower m) (CPolynomial.X + 1) (tower_wellFormed m hm)
      unless (kept.map TowerRepresentation.dimension == [m]) do
        return false
      unless (kept.map TowerRepresentation.fiber == [(tower m).fiber]) do
        return false
      let removed := localizeFiber (tower m) CPolynomial.X (tower_wellFormed m hm)
      unless removed.isEmpty do
        return false
    else
      return false
  return true

example : checks1 = true := by decide +kernel

end ArkLibTest.LocalizeFiber
