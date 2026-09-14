/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimaryTower
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Normalization
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.BatchedTowerCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Actual weak-invariant splitting retains the nilpotent fiber in characteristic two. -/

namespace ArkLibTest.NonreducedRecovery

open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private abbrev F := ZMod 2

private def source : TowerRepresentation (F := F) :=
  ⟨CPolynomial.X, CPolynomial.X ^ 2, [CPolynomial.X]⟩

private def tower : TowerRepresentation (F := F) :=
  restrictTower source CPolynomial.X (CPolynomial.X ^ 2)

private theorem tower_wellFormed : tower.NonreducedWellFormed 1 := by
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

private def packet : AgreementRecovery.Tower.Component F 1 := ⟨tower, tower_wellFormed⟩

private def domain : Fin 2 ↪ F :=
  ⟨fun i => (i.val : F), by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

-- Every geometric point represents the base-field constant zero, although its stored coefficient
-- is the nonzero nilpotent V. Thus the residual at either received zero is also V.
private def checks1 : Bool := Id.run do
  let recovered := AgreementRecovery.BatchedTower.recoverAgreementDefault
    (RingHom.id F) domain (fun _ => 0) 1 2 [packet]
  unless (recovered == [[0]]) do
    return false
  let duplicated := AgreementRecovery.BatchedTower.recoverAgreementDefault
    (RingHom.id F) domain (fun _ => 0) 1 2 [packet, packet]
  unless (duplicated == [[0]]) do
    return false
  let rejected := AgreementRecovery.BatchedTower.recoverAgreementDefault
    (RingHom.id F) domain (fun i => (i.val : F)) 1 2 [packet]
  unless rejected.isEmpty do
    return false
  let stopped := AgreementRecovery.BatchedTower.blocks .naive .remainderOnly
    (RingHom.id F) domain (fun _ => 0) 1 [packet]
  unless (stopped.map (fun b => b.component.val.dimension) == [2]) do
    return false
  return true

example : checks1 = true := by decide +kernel

end ArkLibTest.NonreducedRecovery
