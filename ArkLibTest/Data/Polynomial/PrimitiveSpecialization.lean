/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.PrimitiveSpecialization
import Mathlib.Algebra.Field.ZMod

/-! Acceptance tests for primitive, full-degree, and separable specialization. -/

open Polynomial

noncomputable section

example {A : Type*} [CommSemiring A] {R H Q : A[X]} (hprim : R.IsPrimitive)
    (hfac : R = H * Q) (hQdeg : Q.natDegree = 0) : IsUnit (Q.coeff 0) :=
  hprim.isUnit_constantCoeff_of_eq_mul_of_natDegree_eq_zero hfac hQdeg

example {F : Type*} [Field F] (P : Polynomial (Polynomial (Polynomial F))) (j k : ℕ)
    (hdegree : 0 < (Bivariate.swap (P.coeff j)).natDegree +
      (Bivariate.swap (P.coeff k)).natDegree)
    (hresultant : resultant (Bivariate.swap (P.coeff j))
      (Bivariate.swap (P.coeff k)) ≠ 0) :
    PrimitiveSpecializationObstruction F P :=
  primitiveSpecializationObstructionOfCoefficientPair P j k hdegree hresultant

example {F : Type*} [Field F] (P : Polynomial (Polynomial (Polynomial F))) (j k DZ DX : ℕ)
    (hjZ : (Bivariate.swap (P.coeff j)).natDegree ≤ DZ)
    (hkZ : (Bivariate.swap (P.coeff k)).natDegree ≤ DZ)
    (hjX : Bivariate.degreeX (Bivariate.swap (P.coeff j)) ≤ DX)
    (hkX : Bivariate.degreeX (Bivariate.swap (P.coeff k)) ≤ DX)
    (hdegree : 0 < (Bivariate.swap (P.coeff j)).natDegree +
      (Bivariate.swap (P.coeff k)).natDegree)
    (hresultant : resultant (Bivariate.swap (P.coeff j))
      (Bivariate.swap (P.coeff k)) ≠ 0) :
    (primitiveSpecializationObstructionOfCoefficientPair P j k hdegree
      hresultant).polynomial.natDegree ≤ 2 * DZ * DX :=
  coefficient_pair_primitive_obstruction_natDegree_le P j k DZ DX
    hjZ hkZ hjX hkX hdegree hresultant

private noncomputable def primitiveCandidate :
    Polynomial (Polynomial (Polynomial (ZMod 2))) :=
  C (C X) * X + C X

private noncomputable def pairCandidateObstruction :
    PrimitiveSpecializationObstruction (ZMod 2) primitiveCandidate :=
  primitiveSpecializationObstructionOfCoefficientPair primitiveCandidate 0 1
    (by simp [primitiveCandidate, Bivariate.swap])
    (by simp [primitiveCandidate, Bivariate.swap])

-- The concrete coefficient pair recovers the required `X`-exception polynomial.
example : pairCandidateObstruction.polynomial = X := by
  simp [pairCandidateObstruction, primitiveSpecializationObstructionOfCoefficientPair,
    primitiveCandidate, Bivariate.swap]

private noncomputable def candidateObstruction :
    PrimitiveSpecializationObstruction (ZMod 2) primitiveCandidate where
  polynomial := X
  ne_zero := X_ne_zero
  isPrimitive_of_eval_ne_zero := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [isPrimitive_iff_isUnit_of_C_dvd]
    intro a ha
    have hcoeff := (C_dvd_iff_dvd_coeff a _).mp ha 0
    have hdiv : a ∣ C x := by simpa [primitiveCandidate] using hcoeff
    apply isUnit_iff_dvd_one.mpr
    exact hdiv.trans (isUnit_iff_dvd_one.mp (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx0)))

-- The primitive obstruction has degree one, so the two-element field still contains a common
-- center; at the excluded center zero, the specialization is the nonprimitive polynomial `Z·Y`.
example : ∃ x : ZMod 2,
    (primitiveCandidate.map (evalRingHom (C x))).IsPrimitive ∧
    primitiveCandidate.map (evalRingHom (C x)) ≠ 0 ∧
    (primitiveCandidate.map (evalRingHom (C x))).natDegree = primitiveCandidate.natDegree ∧
    (primitiveCandidate.map ((algebraMap (Polynomial (ZMod 2))
      (FractionRing (Polynomial (ZMod 2)))).comp (evalRingHom (C x)))).Separable := by
  have hdegree : ∀ i : Unit, i ∈ Finset.univ → 0 < primitiveCandidate.natDegree := by
    simp [primitiveCandidate]
  have hsep : ∀ i : Unit, i ∈ Finset.univ →
      (primitiveCandidate.map (algebraMap _
        (FractionRing (Polynomial (Polynomial (ZMod 2)))))).Separable := by
    intro i hi
    let K := FractionRing (Polynomial (Polynomial (ZMod 2)))
    let f : Polynomial (Polynomial (ZMod 2)) →+* K := algebraMap _ _
    have hb0 : f (C X) ≠ 0 :=
      (map_ne_zero_iff f
        (IsFractionRing.injective (Polynomial (Polynomial (ZMod 2))) K)).mpr (by simp)
    have hb : IsUnit (f (C X)) := isUnit_iff_ne_zero.mpr hb0
    have hlinear := separable_C_mul_X_pow_add_C_mul_X_add_C
      (0 : K) (f (C X)) (f X) (n := 0) (by simp) hb
    simpa [primitiveCandidate, K, f] using hlinear
  have hcard : ∑ i : Unit,
      (candidateObstruction.polynomial.natDegree + primitiveCandidate.leadingCoeff.natDegree +
        (resultant primitiveCandidate primitiveCandidate.derivative).natDegree) <
        Fintype.card (ZMod 2) := by
    simp [primitiveCandidate, candidateObstruction]
  simpa only [Finset.mem_univ, true_implies, forall_const] using
    exists_primitive_full_degree_separable_specialization_of_degree_sum_lt_card
      Finset.univ (fun _ : Unit ↦ primitiveCandidate) (fun _ ↦ candidateObstruction)
      hdegree hsep hcard

private noncomputable def degreeDropCandidate :
    Polynomial (Polynomial (Polynomial (ZMod 2))) :=
  C X * X + 1

-- Nonzeroness alone does not preserve the outer degree: the leading-coefficient obstruction is
-- independently necessary, while the constant term keeps this specialization nonzero.
example : degreeDropCandidate.map (evalRingHom (C (0 : ZMod 2))) ≠ 0 ∧
    (degreeDropCandidate.map (evalRingHom (C (0 : ZMod 2)))).natDegree <
      degreeDropCandidate.natDegree := by
  constructor
  · simp [degreeDropCandidate]
  · have hle : degreeDropCandidate.natDegree ≤ 1 := by
      exact (natDegree_add_le _ _).trans (by simp)
    have hcoeff : degreeDropCandidate.coeff 1 ≠ 0 := by
      rw [degreeDropCandidate, coeff_add, coeff_C_mul_X, coeff_one]
      simp
    have hdegree : degreeDropCandidate.natDegree = 1 :=
      natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff
    rw [hdegree]
    simp [degreeDropCandidate]

#print axioms Polynomial.IsPrimitive.isUnit_constantCoeff_of_eq_mul_of_natDegree_eq_zero
#print axioms Polynomial.isUnit_cofactor_of_isPrimitive_of_full_natDegree
#print axioms Polynomial.exists_unit_cofactor_of_isPrimitive_dvd_full_natDegree
#print axioms Polynomial.primitiveSpecializationObstructionOfCoefficientPair
#print axioms Polynomial.coefficient_pair_primitive_obstruction_natDegree_le
#print axioms Polynomial.full_degree_separable_obstruction_ne_zero
#print axioms Polynomial.exists_primitive_full_degree_separable_specialization_of_degree_sum_lt_card
