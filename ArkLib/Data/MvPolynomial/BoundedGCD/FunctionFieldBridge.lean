/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.ContentPrimitiveGCD
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import CompPoly.Univariate.Deriv
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Radical

/-!
# Function-field bridges for certified stored gcds

This module connects the executable last-variable representation and certified gcd output to
ordinary polynomial algebra over the fraction field of the coefficient ring.  It contains no
runtime choice: fraction fields and normalized gcd structures occur only in proof statements.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge

open CompPoly
open CPoly.TaylorReconstruction
open CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD

variable {E : Type*} [CommRing E] [DecidableEq E] [BEq E] [LawfulBEq E]
  [Nontrivial E] {r : ℕ}

omit [DecidableEq E] [Nontrivial E] in
private theorem partialDerivative_add (i : Fin (r + 1))
    (p q : CMvPolynomial (r + 1) E) :
    CMvPolynomial.partialDerivative i (p + q) =
      CMvPolynomial.partialDerivative i p + CMvPolynomial.partialDerivative i q := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_add,
    (MvPolynomial.pderiv i).map_add, CPoly.map_add,
    CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]

omit [DecidableEq E] [Nontrivial E] in
private theorem partialDerivative_mul (i : Fin (r + 1))
    (p q : CMvPolynomial (r + 1) E) :
    CMvPolynomial.partialDerivative i (p * q) =
      CMvPolynomial.partialDerivative i p * q + p * CMvPolynomial.partialDerivative i q := by
  apply CPoly.fromCMvPolynomial_injective
  simp only [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_mul,
    MvPolynomial.pderiv_mul, CPoly.map_add]

private theorem partialDerivative_flattenLast_C (p : CMvPolynomial r E) :
    CMvPolynomial.partialDerivative (Fin.last r) (flattenLast (CPolynomial.C p)) = 0 := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative, flattenLast_semantics]
  simp only [CPolynomial.C_toPoly, Polynomial.eval₂_C]
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars, CPoly.map_zero]
  intro hlast
  have hsubset := MvPolynomial.vars_rename Fin.castSucc (fromCMvPolynomial p) hlast
  simp only [Finset.mem_image] at hsubset
  obtain ⟨i, _, hi⟩ := hsubset
  exact Fin.castSucc_ne_last i hi

private theorem partialDerivative_flattenLast_X :
    CMvPolynomial.partialDerivative (Fin.last r)
      (flattenLast (CPolynomial.X : CPolynomial (CMvPolynomial r E))) = 1 := by
  apply CPoly.fromCMvPolynomial_injective
  rw [flattenLast_X, CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_X, MvPolynomial.pderiv_X_self, CPoly.map_one]

private theorem derivative_X :
    CPolynomial.derivative (CPolynomial.X : CPolynomial (CMvPolynomial r E)) = 1 := by
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.derivative_toPoly, CPolynomial.X_toPoly,
    Polynomial.derivative_X, CPolynomial.toPoly_one]

/-- Differentiating after flattening the last-variable view agrees with stored univariate
differentiation. -/
theorem partialDerivative_flattenLast (p : CPolynomial (CMvPolynomial r E)) :
    CMvPolynomial.partialDerivative (Fin.last r) (flattenLast p) =
      flattenLast (CPolynomial.derivative p) := by
  induction p using CPolynomial.induction_on with
  | h0 =>
      apply CPoly.fromCMvPolynomial_injective
      rw [_root_.map_zero (flattenLast (r := r) (E := E)),
        CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_zero,
        _root_.map_zero (MvPolynomial.pderiv (Fin.last r)), CPolynomial.derivative_zero,
        _root_.map_zero (flattenLast (r := r) (E := E))]
      simp
  | hC p =>
      rw [partialDerivative_flattenLast_C, CPolynomial.derivative_C]
      simp
  | hadd p q hp hq =>
      rw [_root_.map_add (flattenLast (r := r) (E := E)), partialDerivative_add, hp, hq,
        CPolynomial.derivative_add,
        _root_.map_add (flattenLast (r := r) (E := E))]
  | hX p hp =>
      rw [_root_.map_mul (flattenLast (r := r) (E := E)), partialDerivative_mul,
        partialDerivative_flattenLast_X, hp, CPolynomial.derivative_mul,
        derivative_X]
      simp

/-- Splitting off the last stored variable sends its partial derivative to the ordinary
univariate derivative. -/
theorem splitLast_partialDerivative_last (p : CMvPolynomial (r + 1) E) :
    splitLast (CMvPolynomial.partialDerivative (Fin.last r) p) =
      CPolynomial.derivative (splitLast p) := by
  apply (show Function.Injective (flattenLast (r := r) (E := E)) from fun a b h => by
    rw [← splitLast_flattenLast a, ← splitLast_flattenLast b, h])
  calc
    flattenLast (splitLast (CMvPolynomial.partialDerivative (Fin.last r) p)) =
        CMvPolynomial.partialDerivative (Fin.last r) p := flattenLast_splitLast _
    _ = CMvPolynomial.partialDerivative (Fin.last r) (flattenLast (splitLast p)) := by
      rw [flattenLast_splitLast]
    _ = flattenLast (CPolynomial.derivative (splitLast p)) :=
      partialDerivative_flattenLast _

section StoredFactorizationInstances

variable {F : Type*} [CommRing F] [IsDomain F] [UniqueFactorizationMonoid F]
  [BEq F] [LawfulBEq F] {n : ℕ}

/-- The stored polynomial representation inherits unique factorization from semantic
multivariate polynomials. -/
noncomputable instance storedUniqueFactorizationMonoid :
    UniqueFactorizationMonoid (CMvPolynomial n F) :=
  (CPoly.polyRingEquiv (n := n) (R := F)).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

/-- Proof-only normalized gcd structure on stored multivariate polynomials. Executable gcds are
still supplied explicitly and certified by `ContentPrimitiveGCD.Certificate`. -/
noncomputable instance storedNormalizedGCDMonoid : NormalizedGCDMonoid (CMvPolynomial n F) :=
  letI : NormalizationMonoid (CMvPolynomial n F) := Nonempty.some inferInstance
  Nonempty.some (nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mpr inferInstance)

end StoredFactorizationInstances

section FractionField

variable {R K : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [IsDomain R] [NormalizedGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
  [DecidableEq K]

omit [DecidableEq R] [NormalizedGCDMonoid R] in
private theorem toPoly_dvd {p q : CPolynomial R} (h : p ∣ q) : p.toPoly ∣ q.toPoly := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a.toPoly, CPolynomial.toPoly_mul _ _⟩

omit [DecidableEq R] [NormalizedGCDMonoid R] in
private theorem of_toPoly_dvd {p q : CPolynomial R} (h : p.toPoly ∣ q.toPoly) : p ∣ q := by
  obtain ⟨a, ha⟩ := h
  refine ⟨CPolynomial.ringEquiv.symm a, ?_⟩
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_mul]
  have hinverse : (CPolynomial.ringEquiv.symm a).toPoly = a := by
    rw [← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
  rw [hinverse]
  exact ha

omit [DecidableEq R] in
/-- A certified gcd of primitive stored polynomials remains associated to the Euclidean gcd after
mapping the coefficient ring into its fraction field. -/
theorem certificate_fraction_gcd_associated
    {left right result : CPolynomial R}
    (hleftPrimitive : left.toPoly.IsPrimitive)
    (certificate : Certificate left right result) :
    Associated
      (result.toPoly.map (algebraMap R K))
      (EuclideanDomain.gcd
        (left.toPoly.map (algebraMap R K))
        (right.toPoly.map (algebraMap R K))) := by
  let fieldGcd := EuclideanDomain.gcd
    (left.toPoly.map (algebraMap R K))
    (right.toPoly.map (algebraMap R K))
  have hresultDvd : result.toPoly.map (algebraMap R K) ∣ fieldGcd := by
    apply EuclideanDomain.dvd_gcd
    · exact map_dvd (Polynomial.mapRingHom (algebraMap R K))
        (toPoly_dvd certificate.dvd_left)
    · exact map_dvd (Polynomial.mapRingHom (algebraMap R K))
        (toPoly_dvd certificate.dvd_right)
  have hleftMap : left.toPoly.map (algebraMap R K) ≠ 0 := by
    intro hzero
    apply hleftPrimitive.ne_zero
    apply Polynomial.map_injective (algebraMap R K)
      (FaithfulSMul.algebraMap_injective R K)
    simpa using hzero
  have hfieldGcd : fieldGcd ≠ 0 := by
    intro hzero
    have := EuclideanDomain.gcd_dvd_left
      (left.toPoly.map (algebraMap R K)) (right.toPoly.map (algebraMap R K))
    change fieldGcd ∣ left.toPoly.map (algebraMap R K) at this
    rw [hzero, zero_dvd_iff] at this
    exact hleftMap this
  let integerGcd := IsLocalization.integerNormalization (nonZeroDivisors R) fieldGcd
  let primitiveGcd := integerGcd.primPart
  have hintegerGcd : integerGcd ≠ 0 := by
    exact (IsFractionRing.integerNormalization_eq_zero_iff.not).mpr hfieldGcd
  have hprimitiveGcd : primitiveGcd.IsPrimitive := Polynomial.isPrimitive_primPart _
  obtain ⟨scale, hscaleMem, hscaleEq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors R) fieldGcd
  have hscaleNe : scale ≠ 0 := nonZeroDivisors.ne_zero hscaleMem
  have hcontent : integerGcd.content ≠ 0 := by
    exact Polynomial.content_eq_zero_iff.not.mpr hintegerGcd
  have hmapScale : algebraMap R K scale ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective R K).ne hscaleNe
  have hmapContent : algebraMap R K integerGcd.content ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective R K).ne hcontent
  have hintegerAssociatedField :
      Associated (integerGcd.map (algebraMap R K)) fieldGcd := by
    have hunitScale : IsUnit (algebraMap R (Polynomial K) scale) := by
      change IsUnit (Polynomial.C ((algebraMap R K) scale))
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hmapScale)
    rw [hscaleEq, Algebra.smul_def]
    exact associated_unit_mul_left fieldGcd _ hunitScale
  have hintegerAssociatedPrimitive :
      Associated (integerGcd.map (algebraMap R K))
        (primitiveGcd.map (algebraMap R K)) := by
    rw [integerGcd.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C]
    exact associated_unit_mul_left _ _ (Polynomial.isUnit_C.mpr <|
      isUnit_iff_ne_zero.mpr hmapContent)
  have hprimitiveAssociatedField :
      Associated (primitiveGcd.map (algebraMap R K)) fieldGcd :=
    hintegerAssociatedPrimitive.symm.trans hintegerAssociatedField
  have hprimitiveDvdLeftMap : primitiveGcd.map (algebraMap R K) ∣
      left.toPoly.map (algebraMap R K) :=
    hprimitiveAssociatedField.dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hprimitiveDvdRightMap : primitiveGcd.map (algebraMap R K) ∣
      right.toPoly.map (algebraMap R K) :=
    hprimitiveAssociatedField.dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hprimitiveDvdResult : primitiveGcd ∣ result.toPoly := by
    have hprimitiveInverse :
        (CPolynomial.ringEquiv.symm primitiveGcd).toPoly = primitiveGcd := by
      rw [← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
    have hstored : CPolynomial.ringEquiv.symm primitiveGcd ∣ result :=
      certificate.greatest (CPolynomial.ringEquiv.symm primitiveGcd)
        (of_toPoly_dvd <| by
          rw [hprimitiveInverse]
          exact hprimitiveGcd.dvd_of_fraction_map_dvd_fraction_map hprimitiveDvdLeftMap)
        (of_toPoly_dvd <| by
          rw [hprimitiveInverse]
          exact hprimitiveGcd.dvd_of_fraction_map_dvd_fraction_map hprimitiveDvdRightMap)
    have hsemantic := toPoly_dvd hstored
    rw [hprimitiveInverse] at hsemantic
    exact hsemantic
  have hfieldDvdResult : fieldGcd ∣ result.toPoly.map (algebraMap R K) :=
    hprimitiveAssociatedField.dvd'.trans <|
      map_dvd (Polynomial.mapRingHom (algebraMap R K)) hprimitiveDvdResult
  exact associated_of_dvd_dvd hresultDvd hfieldDvdResult

/-- Dividing a nonzero polynomial over a field by a divisor associated to its derivative gcd
leaves a squarefree quotient. -/
theorem squarefree_quotient_gcd_derivative
    {input divisor quotient : Polynomial K} (hinput : input ≠ 0)
    (hdivisor : Associated divisor (EuclideanDomain.gcd input input.derivative))
    (hfactor : quotient * divisor = input) : Squarefree quotient := by
  let radical := UniqueFactorizationMonoid.radical input
  let repeated := EuclideanDomain.divRadical input
  have hrepeatedDvdGcd : repeated ∣ EuclideanDomain.gcd input input.derivative := by
    apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.divRadical_dvd_self input
    · exact divRadical_dvd_derivative input
  have hrepeatedDvdDivisor : repeated ∣ divisor :=
    hdivisor.dvd_iff_dvd_right.mpr hrepeatedDvdGcd
  obtain ⟨multiplier, hmultiplier⟩ := hrepeatedDvdDivisor
  have hcancel : repeated * (multiplier * quotient) = repeated * radical := by
    calc
      _ = (repeated * multiplier) * quotient := (mul_assoc _ _ _).symm
      _ = divisor * quotient := by rw [hmultiplier]
      _ = input := by rw [mul_comm, hfactor]
      _ = radical * repeated := EuclideanDomain.radical_mul_divRadical.symm
      _ = repeated * radical := mul_comm _ _
  have hquotientDvd : quotient ∣ radical := by
    refine ⟨multiplier, ?_⟩
    have h := mul_left_cancel₀ (EuclideanDomain.divRadical_ne_zero hinput) hcancel
    simpa [mul_comm] using h.symm
  exact UniqueFactorizationMonoid.squarefree_radical.squarefree_of_dvd hquotientDvd

/-- Removing a gcd from a squarefree polynomial leaves a squarefree factor coprime to the second
gcd input. -/
theorem squarefree_coprime_complement
    {support separant divisor regular : Polynomial K}
    (hsupport : Squarefree support)
    (hdivisor : Associated divisor (EuclideanDomain.gcd support separant))
    (hfactor : regular * divisor = support) :
    Squarefree regular ∧ IsCoprime regular separant := by
  have hregularDvd : regular ∣ support := ⟨divisor, hfactor.symm⟩
  have hregularSquarefree : Squarefree regular :=
    hsupport.squarefree_of_dvd hregularDvd
  have hproductSquarefree : Squarefree (regular * divisor) := hfactor.symm ▸ hsupport
  have hrel : IsRelPrime regular divisor := IsRelPrime.of_squarefree_mul hproductSquarefree
  refine ⟨hregularSquarefree, IsRelPrime.isCoprime ?_⟩
  intro common hcommonRegular hcommonSeparant
  have hcommonSupport : common ∣ support := hcommonRegular.trans hregularDvd
  have hcommonGcd : common ∣ EuclideanDomain.gcd support separant :=
    EuclideanDomain.dvd_gcd hcommonSupport hcommonSeparant
  have hcommonDivisor : common ∣ divisor :=
    hdivisor.dvd_iff_dvd_right.mpr hcommonGcd
  exact hrel hcommonRegular hcommonDivisor

end FractionField

end CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge
