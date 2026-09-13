/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimaryTower
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Normalization
import Mathlib.Algebra.Field.ZMod

/-! Actual weak-invariant splitting retains the nilpotent fiber in characteristic two. -/

namespace ArkLibTest.PrimaryTower

open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev F := ZMod 2

private def source : TowerRepresentation (F := F) :=
  ⟨CPolynomial.X, CPolynomial.X ^ 2, []⟩

private def tower : TowerRepresentation (F := F) :=
  restrictTower source CPolynomial.X (CPolynomial.X ^ 2)

private theorem tower_wellFormed : tower.NonreducedWellFormed 0 := by
  have hG : (CPolynomial.X : CPolynomial F).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  have hGpos : 0 < (CPolynomial.X : CPolynomial F).natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly, Polynomial.natDegree_X]
    exact Nat.zero_lt_one
  have hh : (CPolynomial.X ^ 2 : CPolynomial (CPolynomial F)).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow 2
  apply restrictTower_nonreducedWellFormed source CPolynomial.X (CPolynomial.X ^ 2) hG
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := F)).squarefree
  · simp only [TowerRepresentation.dimension, restrictTower]
    rw [natDegree_reduceBase CPolynomial.X hG hGpos (CPolynomial.X ^ 2) hh]
    simp only [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly,
      CPolynomial.toPoly_pow, Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    decide
  · exact TowerRepresentation.monic_reduceBase hG hGpos hh
  · rfl

private def children := splitZeroUnitPrimary tower CPolynomial.X tower_wellFormed

private def checks1 : Bool := Id.run do
  unless (children.length == 1) do
    return false
  unless (children.map (fun c : TaggedTower (F := F) =>
      (c.tag.isZero, c.tower.dimension)) == [(true, 2)]) do
    return false
  unless (children.map (fun c : TaggedTower (F := F) => c.tower.fiber) == [tower.fiber]) do
    return false
  unless ((splitStatePrimary tower CPolynomial.X tower_wellFormed).divisor.toCPolynomial == 0) do
    return false
  return true

example (child : TaggedTower (F := F)) (hc : child ∈ children) :
    child.tower.NonreducedWellFormed 0 :=
  splitZeroUnitPrimary_nonreducedWellFormed tower CPolynomial.X tower_wellFormed child hc

example : checks1 = true := by decide +kernel

end ArkLibTest.PrimaryTower
