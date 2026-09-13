/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulayCorrectness
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotient
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Degree bounds for the checked dense Macaulay quotient

This file proves parameter-degree bounds that follow from the executable
matrix construction and from the product certificate returned by
`macaulayQuotient?`.  These statements concern the computed determinant and
checked quotient only; they do not identify that quotient with a resultant.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial
open DenseMacaulay

section CommRing

variable {F : Type*} [CommRing F] [BEq F] [LawfulBEq F]

/-- The extraneous principal determinant has total parameter degree at most
the size of its minor. -/
theorem extraneousFactor_totalDegree_le_minorSize {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (extraneousFactor system).totalDegree ≤ (extraneousIndices system).length := by
  rw [CPoly.totalDegree_equiv (S := F)]
  unfold extraneousFactor
  change ((CPoly.polyRingEquiv (n := n + 2) (R := F))
    ((extraneousMatrix system).det)).totalDegree ≤ _
  rw [RingEquiv.map_det (CPoly.polyRingEquiv (n := n + 2) (R := F))
    (extraneousMatrix system)]
  simpa using DenseMacaulay.totalDegree_det_le_card
    ((CPoly.polyRingEquiv (n := n + 2) (R := F)).mapMatrix
      (extraneousMatrix system)) 1
    (fun i j => by
      change (fromCMvPolynomial
        (matrix system (extraneousIndex i) (extraneousIndex j))).totalDegree ≤ 1
      exact DenseMacaulay.matrix_entry_totalDegree_le_one system _ _)

/-- Each individual parameter degree of the extraneous determinant is bounded
by the size of its principal minor. -/
theorem extraneousFactor_parameterDegree_le_minorSize {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (i : Fin (n + 2)) :
    (fromCMvPolynomial (extraneousFactor system)).degreeOf i ≤
      (extraneousIndices system).length :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans <| by
    simpa [CPoly.totalDegree_equiv (S := F)] using
      extraneousFactor_totalDegree_le_minorSize system

end CommRing

section Field

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- A successful checked quotient has total parameter degree at most the full
Macaulay matrix size. -/
theorem macaulayQuotient_totalDegree_le_matrixSize {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {quotient : Parameters n F}
    (hquotient : macaulayQuotient? system = some quotient) :
    quotient.totalDegree ≤ (basis system).length := by
  by_cases hzero : quotient = 0
  · subst quotient
    simp [CPoly.totalDegree_equiv (S := F)]
  have hfactor : extraneousFactor system ≠ 0 :=
    macaulayQuotient?_extraneousFactor_ne_zero hquotient
  have hproduct := macaulayQuotient?_sound hquotient
  have hquotientMap : fromCMvPolynomial quotient ≠ 0 := by
    intro hmap
    apply hzero
    apply fromCMvPolynomial_injective
    simpa using hmap
  have hfactorMap : fromCMvPolynomial (extraneousFactor system) ≠ 0 := by
    intro hmap
    apply hfactor
    apply fromCMvPolynomial_injective
    simpa using hmap
  have hcharacteristicMap : fromCMvPolynomial (characteristic system) ≠ 0 := by
    rw [← hproduct, CPoly.map_mul]
    exact mul_ne_zero hquotientMap hfactorMap
  have hdivides : fromCMvPolynomial quotient ∣
      fromCMvPolynomial (characteristic system) := by
    refine ⟨fromCMvPolynomial (extraneousFactor system), ?_⟩
    rw [← CPoly.map_mul, hproduct]
  calc
    quotient.totalDegree = (fromCMvPolynomial quotient).totalDegree :=
      CPoly.totalDegree_equiv (S := F)
    _ ≤ (fromCMvPolynomial (characteristic system)).totalDegree :=
      MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdivides hcharacteristicMap
    _ = (characteristic system).totalDegree :=
      (CPoly.totalDegree_equiv (S := F)).symm
    _ ≤ (basis system).length :=
      DenseMacaulay.characteristic_totalDegree_le_matrixSize system

/-- Each individual parameter degree of a successful checked quotient is
bounded by the full Macaulay matrix size. -/
theorem macaulayQuotient_parameterDegree_le_matrixSize {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {quotient : Parameters n F}
    (hquotient : macaulayQuotient? system = some quotient)
    (i : Fin (n + 2)) :
    (fromCMvPolynomial quotient).degreeOf i ≤ (basis system).length :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans <| by
    simpa [CPoly.totalDegree_equiv (S := F)] using
      macaulayQuotient_totalDegree_le_matrixSize hquotient

end Field

end ArkLib.Rojas.Producer.MacaulayQuotient
