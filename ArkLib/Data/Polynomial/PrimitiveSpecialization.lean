/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SeparableSpecialization

/-!
# Primitive and full-degree polynomial specialization

A primitive polynomial admits no nonunit constant cofactor. This module packages that content
argument and combines a supplied primitive-specialization obstruction with the leading-coefficient
and derivative-resultant obstructions. Avoiding the product gives one specialization that is
primitive, preserves the outer degree, and is separable over the remaining fraction field.

Constructing a primitive-specialization obstruction, and bounding its degree in a concrete
application, are separate obligations. Fraction-field separability is not promoted to
coefficient-ring separability here.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.

The unit-cofactor argument and obstruction interface are adapted from Remco Bloemen's
`BCHKSPrimitiveSpecialization.lean`, proximity-prize PR #45, commit
`e4c8dfbf73ba1cc152e72d67c63435aae1021397`. The simultaneous product follows Jieyi Long's
`BCHKSUniversalPrimitiveX0Avoidance6399.lean`, PR #72, commit
`19bc7d3e21b2261257e1961acd720b2c395d87e1`, with all concrete parameters removed.
-/

namespace Polynomial

/-- A primitive ambient polynomial forces every constant polynomial cofactor to have a unit
coefficient. This is the exact content premise used by the quantitative Hensel setup. -/
theorem IsPrimitive.isUnit_constantCoeff_of_eq_mul_of_natDegree_eq_zero
    {A : Type*} [CommSemiring A] {R H Q : A[X]} (hprim : R.IsPrimitive)
    (hfac : R = H * Q) (hQdeg : Q.natDegree = 0) : IsUnit (Q.coeff 0) := by
  let a := Q.coeff 0
  have hQ : Q = C a := eq_C_of_natDegree_le_zero hQdeg.le
  have ha : IsUnit a := (isPrimitive_iff_isUnit_of_C_dvd.mp hprim) a ⟨H, by
    calc
      R = H * Q := hfac
      _ = H * C a := by rw [hQ]
      _ = C a * H := mul_comm _ _
  ⟩
  simpa [a] using ha

/-- A full-outer-degree divisor of a primitive polynomial has only a unit cofactor. -/
theorem isUnit_cofactor_of_isPrimitive_of_full_natDegree
    {A : Type*} [CommSemiring A] [NoZeroDivisors A] [Nontrivial A]
    {R H Q : A[X]} (hprim : R.IsPrimitive) (hH : H ≠ 0)
    (hfac : R = H * Q) (hdeg : H.natDegree = R.natDegree) : IsUnit Q := by
  have hR : R ≠ 0 := hprim.ne_zero
  have hQ : Q ≠ 0 := by
    intro hQ
    apply hR
    rw [hfac, hQ, mul_zero]
  have hQdeg : Q.natDegree = 0 := by
    have hmul := natDegree_mul hH hQ
    rw [← hfac] at hmul
    omega
  have hQeq : Q = C (Q.coeff 0) := eq_C_of_natDegree_le_zero hQdeg.le
  rw [hQeq, isUnit_C]
  exact hprim.isUnit_constantCoeff_of_eq_mul_of_natDegree_eq_zero hfac hQdeg

/-- Divisibility form of `isUnit_cofactor_of_isPrimitive_of_full_natDegree`. -/
theorem exists_unit_cofactor_of_isPrimitive_dvd_full_natDegree
    {A : Type*} [CommSemiring A] [NoZeroDivisors A] [Nontrivial A]
    {R H : A[X]} (hprim : R.IsPrimitive) (hH : H ≠ 0) (hdvd : H ∣ R)
    (hdeg : H.natDegree = R.natDegree) :
    ∃ Q : A[X], R = H * Q ∧ IsUnit Q := by
  obtain ⟨Q, rfl⟩ := hdvd
  refine ⟨Q, rfl, ?_⟩
  exact isUnit_cofactor_of_isPrimitive_of_full_natDegree hprim hH rfl hdeg

/-- A supplied nonzero polynomial in the specialization parameter certifying that the
specialization is primitive. This structure does not construct such an obstruction. -/
structure PrimitiveSpecializationObstruction
    (F : Type*) [Field F] (P : Polynomial (Polynomial (Polynomial F))) where
  polynomial : Polynomial F
  ne_zero : polynomial ≠ 0
  isPrimitive_of_eval_ne_zero : ∀ x : F, eval x polynomial ≠ 0 →
    (P.map (evalRingHom (C x))).IsPrimitive

/-- Product of the supplied primitive obstruction, the leading coefficient, and the
derivative resultant. Its nonvanishing certifies all three specialization properties. -/
noncomputable def fullDegreeSeparableObstruction
    {F : Type*} [Field F] (P : Polynomial (Polynomial (Polynomial F)))
    (o : PrimitiveSpecializationObstruction F P) : Polynomial (Polynomial F) :=
  o.polynomial.map C * P.leadingCoeff * resultant P P.derivative

/-- The combined obstruction is nonzero when the polynomial has positive outer degree and is
separable over the fraction field before specialization. -/
theorem full_degree_separable_obstruction_ne_zero
    {F : Type*} [Field F] (P : Polynomial (Polynomial (Polynomial F)))
    (o : PrimitiveSpecializationObstruction F P) (hdegree : 0 < P.natDegree)
    (hsep : (P.map (algebraMap _ (FractionRing (Polynomial (Polynomial F))))).Separable) :
    fullDegreeSeparableObstruction P o ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact (Polynomial.map_ne_zero_iff (p := o.polynomial) C_injective).mpr o.ne_zero
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hdegree)
  · exact resultant_derivative_ne_zero_of_fractionField_separable P hsep

/-- One point simultaneously makes every member primitive, preserves its outer degree, and
makes it separable over the remaining fraction field. The hypothesis exposes the actual degree
of the combined obstruction; constructing and estimating the primitive part remains separate. -/
theorem exists_primitive_full_degree_separable_specialization_of_degree_sum_lt_card
    {F : Type*} [Field F] [Fintype F] {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (Polynomial (Polynomial F)))
    (o : ∀ i, PrimitiveSpecializationObstruction F (P i))
    (hdegree : ∀ i ∈ s, 0 < (P i).natDegree)
    (hsep : ∀ i ∈ s,
      ((P i).map (algebraMap _ (FractionRing (Polynomial (Polynomial F))))).Separable)
    (hcard : ∑ i ∈ s, ((o i).polynomial.natDegree + (P i).leadingCoeff.natDegree +
      (resultant (P i) (P i).derivative).natDegree) < Fintype.card F) :
    ∃ x : F, ∀ i ∈ s,
      ((P i).map (evalRingHom (C x))).IsPrimitive ∧
      (P i).map (evalRingHom (C x)) ≠ 0 ∧
      ((P i).map (evalRingHom (C x))).natDegree = (P i).natDegree ∧
      ((P i).map ((algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
        (evalRingHom (C x)))).Separable := by
  have hcombinedDegree :
      ∑ i ∈ s, (fullDegreeSeparableObstruction (P i) (o i)).natDegree ≤
        ∑ i ∈ s, ((o i).polynomial.natDegree + (P i).leadingCoeff.natDegree +
          (resultant (P i) (P i).derivative).natDegree) := by
    apply Finset.sum_le_sum
    intro i hi
    calc
      (fullDegreeSeparableObstruction (P i) (o i)).natDegree ≤
          ((o i).polynomial.map C * (P i).leadingCoeff).natDegree +
            (resultant (P i) (P i).derivative).natDegree := natDegree_mul_le
      _ ≤ ((o i).polynomial.map C).natDegree + (P i).leadingCoeff.natDegree +
            (resultant (P i) (P i).derivative).natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
      _ = (o i).polynomial.natDegree + (P i).leadingCoeff.natDegree +
            (resultant (P i) (P i).derivative).natDegree := by
        rw [natDegree_map_eq_of_injective C_injective]
  obtain ⟨x, hx⟩ := exists_forall_eval_C_ne_zero_of_sum_natDegree_lt_card s
    (fun i ↦ fullDegreeSeparableObstruction (P i) (o i))
    (fun i hi ↦ full_degree_separable_obstruction_ne_zero (P i) (o i)
      (hdegree i hi) (hsep i hi)) (hcombinedDegree.trans_lt hcard)
  refine ⟨x, fun i hi ↦ ?_⟩
  have hproduct :
      ((((o i).polynomial.map C).eval (C x)) * (P i).leadingCoeff.eval (C x)) *
          (resultant (P i) (P i).derivative).eval (C x) ≠ 0 := by
    simpa [fullDegreeSeparableObstruction] using hx i hi
  have hleft :
      (((o i).polynomial.map C).eval (C x)) * (P i).leadingCoeff.eval (C x) ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hobstructionMap : ((o i).polynomial.map C).eval (C x) ≠ 0 :=
    left_ne_zero_of_mul hleft
  have hleading : (P i).leadingCoeff.eval (C x) ≠ 0 :=
    right_ne_zero_of_mul hleft
  have hresultant : (resultant (P i) (P i).derivative).eval (C x) ≠ 0 :=
    right_ne_zero_of_mul hproduct
  have hobstruction : eval x (o i).polynomial ≠ 0 := by
    intro hzero
    apply hobstructionMap
    simp [hzero]
  have hprimitive := (o i).isPrimitive_of_eval_ne_zero x hobstruction
  have hnatDegree := natDegree_map_of_leadingCoeff_ne_zero
    (evalRingHom (C x)) hleading
  have hnonzero : (P i).map (evalRingHom (C x)) ≠ 0 := by
    exact ne_zero_of_natDegree_gt (hnatDegree.symm ▸ hdegree i hi)
  refine ⟨hprimitive, hnonzero, hnatDegree, ?_⟩
  apply separable_map_of_resultant_derivative_ne_zero _ (P i) (hdegree i hi)
  change algebraMap (Polynomial F) (FractionRing (Polynomial F))
    ((resultant (P i) (P i).derivative).eval (C x)) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hresultant

end Polynomial
