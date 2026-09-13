/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Constructor
public import ArkLib.Data.MvPolynomial.BoundedGCD.FunctionFieldBridge
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# General-order regular components from two certified gcds

The last jet variable is treated as the univariate variable. The equation is first normalized to
a primitive polynomial, then divided by its gcd with the actual separant. A second gcd with that
same separant removes every remaining generically singular component. All arithmetic operations
are executable parameters with explicit algebraic laws; callers do not supply success witnesses.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.General

open CompPoly CPoly CPoly.TaylorReconstruction
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD
open CPoly.CMvPolynomial.BoundedGCD.GaussPreservation

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] {r : ℕ}

/-- Inspectable output of the two-gcd last-variable pipeline. -/
structure Data (r : ℕ) (E : Type*) [Field E] [DecidableEq E] [BEq E] [LawfulBEq E] where
  normalization : CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization.Data
    (CMvPolynomial r E)
  repeatedDivisor : CPolynomial (CMvPolynomial r E)
  support : CPolynomial (CMvPolynomial r E)
  singularDivisor : CPolynomial (CMvPolynomial r E)
  regular : CPolynomial (CMvPolynomial r E)

/-- Run primitive normalization, repeated-factor removal, and actual-separant component removal. -/
def run? (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (equation separant : CMvPolynomial (r + 1) E) : Option (Data r E) :=
  match CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization.normalize?
      coefficientGcd coefficientDivide (splitLast equation) with
  | none => none
  | some normalization =>
      match CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?
          coefficientGcd coefficientDivide
          normalization.primitive (splitLast separant) with
      | none => none
      | some repeatedDivisor =>
          match flatDivide (flattenLast normalization.primitive)
              (flattenLast repeatedDivisor) with
          | none => none
          | some supportFlat =>
              let support := splitLast supportFlat
              match CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?
                  coefficientGcd coefficientDivide
                  support (splitLast separant) with
              | none => none
              | some singularDivisor =>
                  match flatDivide (flattenLast support) (flattenLast singularDivisor) with
                  | none => none
                  | some regularFlat => some
                      { normalization
                        repeatedDivisor
                        support
                        singularDivisor
                        regular := splitLast regularFlat }

/-- Algebraic certificate for a completed two-gcd computation. -/
structure Certificate
    (equation separant : CMvPolynomial (r + 1) E) (data : Data r E) : Prop where
  equation_normalization :
    CPolynomial.C data.normalization.content * data.normalization.primitive = splitLast equation
  core_primitive : data.normalization.primitive.toPoly.IsPrimitive
  repeated_gcd : CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.Certificate
    data.normalization.primitive
    (splitLast separant) data.repeatedDivisor
  support_factor : data.support * data.repeatedDivisor = data.normalization.primitive
  singular_gcd : CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.Certificate data.support
    (splitLast separant) data.singularDivisor
  regular_factor : data.regular * data.singularDivisor = data.support

private theorem splitLast_ne_zero {p : CMvPolynomial (r + 1) E} (hp : p ≠ 0) :
    splitLast p ≠ 0 := by
  intro hzero
  apply hp
  rw [← flattenLast_splitLast p, hzero]
  exact map_zero (flattenLast (r := r) (E := E))

private theorem flattenLast_ne_zero
    {p : CPolynomial (CMvPolynomial r E)} (hp : p ≠ 0) : flattenLast p ≠ 0 := by
  intro hzero
  apply hp
  rw [← splitLast_flattenLast p, hzero]
  exact map_zero (splitLast (r := r) (E := E))

private theorem nonzero_of_dvd_nonzero {R : Type*} [MonoidWithZero R]
    {divisor value : R} (hvalue : value ≠ 0) (hdivides : divisor ∣ value) : divisor ≠ 0 := by
  intro hzero
  subst divisor
  exact hvalue (zero_dvd_iff.mp hdivides)

private theorem factor_from_flat_division
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (flatDivideLaws : DivideLaws flatDivide)
    (dividend divisor quotient : CPolynomial (CMvPolynomial r E))
    (hdivide : flatDivide (flattenLast dividend) (flattenLast divisor) =
      some (flattenLast quotient)) : quotient * divisor = dividend := by
  have hflat := flatDivideLaws.sound hdivide
  have hnested := congrArg (splitLast (r := r) (E := E)) hflat
  simpa using hnested

/-- Every successful run carries the normalization, gcd, and exact quotient identities used by
the producer. -/
theorem run?_certificate
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (coefficientGcdLaws : GcdLaws coefficientGcd)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    (flatDivideLaws : DivideLaws flatDivide)
    (equation separant : CMvPolynomial (r + 1) E) (data : Data r E)
    (hequation : equation ≠ 0)
    (hrun : run? coefficientGcd coefficientDivide flatDivide equation separant = some data) :
    Certificate equation separant data := by
  unfold run? at hrun
  split at hrun
  · simp at hrun
  · rename_i normalization hnormalization
    split at hrun
    · simp at hrun
    · rename_i repeatedDivisor hrepeated
      split at hrun
      · simp at hrun
      · rename_i supportFlat hsupport
        dsimp only at hrun
        split at hrun
        · simp at hrun
        · rename_i singularDivisor hsingular
          split at hrun
          · simp at hrun
          · rename_i regularFlat hregular
            simp only [Option.some.injEq] at hrun
            subst data
            have hcoreNe :=
              CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization.normalize?_primitive_ne_zero
              coefficientGcd coefficientDivide (splitLast equation) normalization
              hnormalization (splitLast_ne_zero hequation)
            refine
              { equation_normalization :=
                  CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization.normalize?_identity
                  coefficientGcd coefficientDivide _ normalization hnormalization
                core_primitive :=
                  CPoly.CMvPolynomial.BoundedGCD.GaussPreservation.normalize?_toPoly_isPrimitive
                  coefficientGcd coefficientDivide coefficientGcdLaws coefficientDivideLaws
                  _ normalization hnormalization (splitLast_ne_zero hequation)
                repeated_gcd :=
                  CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?_certificate
                  coefficientGcd
                  coefficientDivide coefficientGcdLaws coefficientDivideLaws _ _ _ hrepeated
                support_factor := ?_
                singular_gcd :=
                  CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?_certificate
                  coefficientGcd
                  coefficientDivide coefficientGcdLaws coefficientDivideLaws _ _ _ hsingular
                regular_factor := ?_ }
            · have hflat := flatDivideLaws.sound hsupport
              have hnested := congrArg (splitLast (r := r) (E := E)) hflat
              simpa using hnested
            · have hflat := flatDivideLaws.sound hregular
              have hnested := congrArg (splitLast (r := r) (E := E)) hflat
              simpa using hnested

/-- Exact coefficient and flat division operations make the full two-gcd pipeline total for every
nonzero equation. -/
theorem run?_exists_certificate
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (coefficientGcdLaws : GcdLaws coefficientGcd)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    (flatDivideLaws : DivideLaws flatDivide)
    (equation separant : CMvPolynomial (r + 1) E) (hequation : equation ≠ 0) :
    ∃ data, run? coefficientGcd coefficientDivide flatDivide equation separant = some data ∧
      Certificate equation separant data := by
  have hequationNested : splitLast equation ≠ 0 := splitLast_ne_zero hequation
  obtain ⟨normalization, hnormalization⟩ :=
    CPoly.CMvPolynomial.BoundedGCD.GaussPreservation.normalize?_exists
    coefficientGcd coefficientDivide coefficientGcdLaws coefficientDivideLaws
    (splitLast equation) hequationNested
  have hcoreNe :=
    CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization.normalize?_primitive_ne_zero
    coefficientGcd coefficientDivide (splitLast equation) normalization
    hnormalization hequationNested
  obtain ⟨repeatedDivisor, hrepeated, repeatedCertificate⟩ :=
    CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?_exists_certificate
      coefficientGcd coefficientDivide
      coefficientGcdLaws coefficientDivideLaws normalization.primitive (splitLast separant)
  have hrepeatedNe : repeatedDivisor ≠ 0 :=
    nonzero_of_dvd_nonzero hcoreNe repeatedCertificate.dvd_left
  have hrepeatedFlatNe : flattenLast repeatedDivisor ≠ 0 := flattenLast_ne_zero hrepeatedNe
  have hrepeatedFlatDvd : flattenLast repeatedDivisor ∣ flattenLast normalization.primitive :=
    map_dvd (flattenLast (r := r) (E := E)) repeatedCertificate.dvd_left
  obtain ⟨supportFlat, hsupport⟩ :=
    flatDivideLaws.complete hrepeatedFlatNe hrepeatedFlatDvd
  let support := splitLast supportFlat
  have hsupportFactor : support * repeatedDivisor = normalization.primitive := by
    have hflat := flatDivideLaws.sound hsupport
    have hnested := congrArg (splitLast (r := r) (E := E)) hflat
    simpa [support] using hnested
  have hsupportNe : support ≠ 0 := by
    intro hzero
    apply hcoreNe
    rw [← hsupportFactor, hzero, zero_mul]
  obtain ⟨singularDivisor, hsingular, singularCertificate⟩ :=
    CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD.compute?_exists_certificate
      coefficientGcd coefficientDivide
      coefficientGcdLaws coefficientDivideLaws support (splitLast separant)
  have hsingularNe : singularDivisor ≠ 0 :=
    nonzero_of_dvd_nonzero hsupportNe singularCertificate.dvd_left
  have hsingularFlatNe : flattenLast singularDivisor ≠ 0 := flattenLast_ne_zero hsingularNe
  have hsingularFlatDvd : flattenLast singularDivisor ∣ flattenLast support :=
    map_dvd (flattenLast (r := r) (E := E)) singularCertificate.dvd_left
  obtain ⟨regularFlat, hregular⟩ :=
    flatDivideLaws.complete hsingularFlatNe hsingularFlatDvd
  let data : Data r E :=
    { normalization
      repeatedDivisor
      support
      singularDivisor
      regular := splitLast regularFlat }
  have hregular' : flatDivide supportFlat (flattenLast singularDivisor) = some regularFlat := by
    simpa [support] using hregular
  have hrun : run? coefficientGcd coefficientDivide flatDivide equation separant = some data := by
    simp [run?, hnormalization, hrepeated, hsupport, support, hsingular, hregular', data]
  exact ⟨data, hrun,
    run?_certificate coefficientGcd coefficientDivide flatDivide coefficientGcdLaws
      coefficientDivideLaws flatDivideLaws equation separant data hequation hrun⟩

/-- The actual specialized separant is the stored partial derivative in the last jet variable. -/
theorem initialSeparant_eq_partialDerivative_last (center : E) (T : CMvPolynomial (r + 2) E) :
    FastTaylor.initialSeparant center T =
      CMvPolynomial.partialDerivative (Fin.last r) (FastTaylor.initialEquation center T) := by
  apply fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative,
    FastTaylor.initialEquation_semantics, FastTaylor.initialSeparant_semantics]
  exact (ReedSolomon.HiddenDerivative.pderiv_initialJetEquation center
    (ReedSolomon.HiddenDerivative.semanticEquation T) (Fin.last r)).symm

/-- Flatten the retained last-variable polynomial for consumption by the chart constructor. -/
def component (data : Data r E) : CMvPolynomial (r + 1) E :=
  flattenLast data.regular

/-- Map a last-variable polynomial to the rational function field in the earlier jet variables. -/
noncomputable def genericPolynomial (p : CPolynomial (CMvPolynomial r E)) :
    Polynomial (FractionRing (CMvPolynomial r E)) :=
  p.toPoly.map (algebraMap (CMvPolynomial r E) (FractionRing (CMvPolynomial r E)))

/-- The normalized equation factors into the retained regular polynomial and all discarded
factors. -/
theorem Certificate.nested_factorization
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    data.regular *
        (CPolynomial.C data.normalization.content *
          data.singularDivisor * data.repeatedDivisor) =
      splitLast equation := by
  rw [← certificate.equation_normalization, ← certificate.support_factor,
    ← certificate.regular_factor]
  ring

/-- The returned flat component divides the original specialized equation by a literal stored
product identity. -/
theorem Certificate.component_factorization
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    component data * flattenLast
        (CPolynomial.C data.normalization.content *
          data.singularDivisor * data.repeatedDivisor) = equation := by
  rw [component, ← map_mul (flattenLast (r := r) (E := E)),
    certificate.nested_factorization, flattenLast_splitLast]

/-- The retained component divides the original specialized equation. -/
theorem Certificate.component_dvd_equation
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) : component data ∣ equation := by
  refine ⟨flattenLast
    (CPolynomial.C data.normalization.content *
      data.singularDivisor * data.repeatedDivisor), ?_⟩
  exact certificate.component_factorization.symm

/-- The actual derivative identity makes the primitive core's scalar content a factor of the
separant. -/
theorem Certificate.separant_factorization
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    CPolynomial.C data.normalization.content *
        CPolynomial.derivative data.normalization.primitive = splitLast separant := by
  rw [hseparant,
    CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge.splitLast_partialDerivative_last,
    ← certificate.equation_normalization, CPolynomial.derivative_mul,
    CPolynomial.derivative_C]
  simp

/-- A nonzero equation yields a nonzero retained regular polynomial. -/
theorem Certificate.regular_ne_zero
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0) :
    data.regular ≠ 0 := by
  intro hzero
  apply hequation
  rw [← flattenLast_splitLast equation, ← certificate.nested_factorization, hzero, zero_mul]
  exact map_zero (flattenLast (r := r) (E := E))

/-- The returned constructor component is nonzero whenever the input equation is nonzero. -/
theorem Certificate.component_ne_zero
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0) :
    component data ≠ 0 := flattenLast_ne_zero (certificate.regular_ne_zero hequation)

/-- The constructor component has total degree at most that of the original equation. -/
theorem Certificate.component_totalDegree_le
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0) :
    (fromCMvPolynomial (component data)).totalDegree ≤
      (fromCMvPolynomial equation).totalDegree := by
  let discarded := flattenLast
    (CPolynomial.C data.normalization.content *
      data.singularDivisor * data.repeatedDivisor)
  have hcomponent : fromCMvPolynomial (component data) ≠ 0 :=
    CPoly.polyRingEquiv.map_ne_zero_iff.mpr (certificate.component_ne_zero hequation)
  have hdiscarded : fromCMvPolynomial discarded ≠ 0 := by
    intro hzero
    apply hequation
    have hproduct := certificate.component_factorization
    apply fromCMvPolynomial_injective
    rw [← hproduct, CPoly.map_mul, hzero, mul_zero]
    exact CPoly.map_zero.symm
  have hdegree := MvPolynomial.totalDegree_mul_of_isDomain hcomponent hdiscarded
  rw [← CPoly.map_mul, certificate.component_factorization] at hdegree
  omega

/-- The first quotient is squarefree, while the final quotient is both squarefree and generically
coprime to the actual separant. -/
theorem Certificate.generic_regular_certificates
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    Squarefree (genericPolynomial data.support) ∧
      Squarefree (genericPolynomial data.regular) ∧
      IsCoprime (genericPolynomial data.regular) (genericPolynomial (splitLast separant)) := by
  classical
  let K := FractionRing (CMvPolynomial r E)
  let fractionMap := algebraMap (CMvPolynomial r E) K
  have hcoreNe : data.normalization.primitive ≠ 0 := by
    intro hzero
    apply hequation
    rw [← flattenLast_splitLast equation, ← certificate.equation_normalization,
      hzero, mul_zero]
    exact map_zero (flattenLast (r := r) (E := E))
  have hcoreMapNe : genericPolynomial data.normalization.primitive ≠ 0 := by
    intro hzero
    apply hcoreNe
    apply CPolynomial.toPoly_injective
    apply Polynomial.map_injective fractionMap
      (FaithfulSMul.algebraMap_injective (CMvPolynomial r E) K)
    rw [CPolynomial.toPoly_zero]
    simpa [genericPolynomial, K, fractionMap] using hzero
  have hcontentNe : data.normalization.content ≠ 0 := by
    intro hzero
    apply hequation
    rw [← flattenLast_splitLast equation, ← certificate.equation_normalization,
      hzero]
    simp
  have hcontentMapNe : fractionMap data.normalization.content ≠ 0 := by
    intro hzero
    apply hcontentNe
    apply FaithfulSMul.algebraMap_injective (CMvPolynomial r E) K
    exact hzero.trans (map_zero fractionMap).symm
  have hseparantFactor := certificate.separant_factorization hseparant
  have hseparantGeneric :
      genericPolynomial (splitLast separant) =
        Polynomial.C (fractionMap data.normalization.content) *
          (genericPolynomial data.normalization.primitive).derivative := by
    have hmapped := congrArg
      (Polynomial.mapRingHom fractionMap)
      (congrArg CPolynomial.toPoly hseparantFactor)
    change Polynomial.map fractionMap (splitLast separant).toPoly =
      Polynomial.C (fractionMap data.normalization.content) *
        Polynomial.derivative (Polynomial.map fractionMap data.normalization.primitive.toPoly)
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
      CPolynomial.derivative_toPoly,
      _root_.map_mul (Polynomial.mapRingHom fractionMap)] at hmapped
    change Polynomial.map fractionMap (Polynomial.C data.normalization.content) *
      Polynomial.map fractionMap (Polynomial.derivative data.normalization.primitive.toPoly) =
        Polynomial.map fractionMap (splitLast separant).toPoly at hmapped
    rw [Polynomial.map_C] at hmapped
    rw [← Polynomial.derivative_map] at hmapped
    exact hmapped.symm
  have hseparantAssociated :
      Associated (genericPolynomial (splitLast separant))
        (genericPolynomial data.normalization.primitive).derivative := by
    exact (Associated.of_eq hseparantGeneric).trans <|
      associated_unit_mul_left _ _
        (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontentMapNe))
  have hrepeatedGcd :
      Associated (genericPolynomial data.repeatedDivisor)
        (EuclideanDomain.gcd (genericPolynomial data.normalization.primitive)
          (genericPolynomial (splitLast separant))) := by
    simpa [genericPolynomial, K] using
      (CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge.certificate_fraction_gcd_associated
        (K := K) certificate.core_primitive certificate.repeated_gcd)
  have hgcdTransfer :
      Associated
        (EuclideanDomain.gcd (genericPolynomial data.normalization.primitive)
          (genericPolynomial (splitLast separant)))
        (EuclideanDomain.gcd (genericPolynomial data.normalization.primitive)
          (genericPolynomial data.normalization.primitive).derivative) := by
    apply associated_of_dvd_dvd
    · apply EuclideanDomain.dvd_gcd
      · exact EuclideanDomain.gcd_dvd_left _ _
      · exact hseparantAssociated.dvd_iff_dvd_right.mp
          (EuclideanDomain.gcd_dvd_right _ _)
    · apply EuclideanDomain.dvd_gcd
      · exact EuclideanDomain.gcd_dvd_left _ _
      · exact hseparantAssociated.dvd_iff_dvd_right.mpr
          (EuclideanDomain.gcd_dvd_right _ _)
  have hderivativeGcd :
      Associated (genericPolynomial data.repeatedDivisor)
        (EuclideanDomain.gcd (genericPolynomial data.normalization.primitive)
          (genericPolynomial data.normalization.primitive).derivative) := by
    exact hrepeatedGcd.trans hgcdTransfer
  have hsupportFactorGeneric :
      genericPolynomial data.support * genericPolynomial data.repeatedDivisor =
        genericPolynomial data.normalization.primitive := by
    have hmapped := congrArg
      (Polynomial.mapRingHom fractionMap)
      (congrArg CPolynomial.toPoly certificate.support_factor)
    change Polynomial.map fractionMap data.support.toPoly *
      Polynomial.map fractionMap data.repeatedDivisor.toPoly =
        Polynomial.map fractionMap data.normalization.primitive.toPoly
    rw [CPolynomial.toPoly_mul,
      _root_.map_mul (Polynomial.mapRingHom fractionMap)] at hmapped
    exact hmapped
  have hsupportSquarefree : Squarefree (genericPolynomial data.support) :=
    CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge.squarefree_quotient_gcd_derivative
      hcoreMapNe hderivativeGcd hsupportFactorGeneric
  have hsupportPrimitive : data.support.toPoly.IsPrimitive := by
    apply Polynomial.isPrimitive_of_dvd certificate.core_primitive
    refine ⟨data.repeatedDivisor.toPoly, ?_⟩
    have hsemantic := congrArg CPolynomial.toPoly certificate.support_factor
    rw [CPolynomial.toPoly_mul] at hsemantic
    exact hsemantic.symm
  have hsingularGcd :
      Associated (genericPolynomial data.singularDivisor)
        (EuclideanDomain.gcd (genericPolynomial data.support)
          (genericPolynomial (splitLast separant))) := by
    simpa [genericPolynomial, K] using
      (CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge.certificate_fraction_gcd_associated
        (K := K) hsupportPrimitive certificate.singular_gcd)
  have hregularFactorGeneric :
      genericPolynomial data.regular * genericPolynomial data.singularDivisor =
        genericPolynomial data.support := by
    have hmapped := congrArg
      (Polynomial.mapRingHom fractionMap)
      (congrArg CPolynomial.toPoly certificate.regular_factor)
    change Polynomial.map fractionMap data.regular.toPoly *
      Polynomial.map fractionMap data.singularDivisor.toPoly =
        Polynomial.map fractionMap data.support.toPoly
    rw [CPolynomial.toPoly_mul,
      _root_.map_mul (Polynomial.mapRingHom fractionMap)] at hmapped
    exact hmapped
  have hregular :=
    CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge.squarefree_coprime_complement
      hsupportSquarefree hsingularGcd hregularFactorGeneric
  exact ⟨hsupportSquarefree, hregular⟩

/-- The first quotient is squarefree over the rational function field in the earlier jet
variables. -/
theorem Certificate.support_squarefree
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    Squarefree (genericPolynomial data.support) :=
  (certificate.generic_regular_certificates hequation hseparant).1

/-- The retained quotient is squarefree over the rational function field in the earlier jet
variables. -/
theorem Certificate.regular_squarefree
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    Squarefree (genericPolynomial data.regular) :=
  (certificate.generic_regular_certificates hequation hseparant).2.1

/-- The retained quotient is coprime to the actual separant over the rational function field in
the earlier jet variables. -/
theorem Certificate.regular_isCoprime_separant
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    IsCoprime (genericPolynomial data.regular) (genericPolynomial (splitLast separant)) :=
  (certificate.generic_regular_certificates hequation hseparant).2.2

/-- At every extension-field point where the actual separant is nonzero, the retained component
has exactly the same roots as the original equation. This includes component meetings and points
over ramified projection fibers. -/
theorem Certificate.eval₂_component_iff_equation
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hseparantIdentity : separant =
      CMvPolynomial.partialDerivative (Fin.last r) equation)
    {K : Type*} [Field K] (embedding : E →+* K) (point : Fin (r + 1) → K)
    (hseparant : CMvPolynomial.eval₂ embedding point separant ≠ 0) :
    CMvPolynomial.eval₂ embedding point (component data) = 0 ↔
      CMvPolynomial.eval₂ embedding point equation = 0 := by
  let evaluate := CMvPolynomial.eval₂Hom embedding point
  have factorEvalNe (factor : CPolynomial (CMvPolynomial r E))
      (hfactor : factor ∣ splitLast separant) : evaluate (flattenLast factor) ≠ 0 := by
    intro hzero
    apply hseparant
    obtain ⟨quotient, hquotient⟩ := hfactor
    rw [← flattenLast_splitLast separant, hquotient,
      map_mul (flattenLast (r := r) (E := E))]
    change evaluate (flattenLast factor * flattenLast quotient) = 0
    rw [(evaluate).map_mul, hzero, zero_mul]
  have hcontentDvd : CPolynomial.C data.normalization.content ∣ splitLast separant := by
    refine ⟨CPolynomial.derivative data.normalization.primitive, ?_⟩
    exact (certificate.separant_factorization hseparantIdentity).symm
  have hcontentEval : evaluate (flattenLast (CPolynomial.C data.normalization.content)) ≠ 0 :=
    factorEvalNe _ hcontentDvd
  have hsingularEval : evaluate (flattenLast data.singularDivisor) ≠ 0 :=
    factorEvalNe _ certificate.singular_gcd.dvd_right
  have hrepeatedEval : evaluate (flattenLast data.repeatedDivisor) ≠ 0 :=
    factorEvalNe _ certificate.repeated_gcd.dvd_right
  have hdiscardedEval : evaluate (flattenLast
      (CPolynomial.C data.normalization.content *
        data.singularDivisor * data.repeatedDivisor)) ≠ 0 := by
    rw [map_mul (flattenLast (r := r) (E := E)),
      map_mul (flattenLast (r := r) (E := E)),
      (evaluate).map_mul, (evaluate).map_mul]
    exact mul_ne_zero (mul_ne_zero hcontentEval hsingularEval) hrepeatedEval
  have hfactorization := congrArg evaluate certificate.component_factorization
  simp only [evaluate, CMvPolynomial.eval₂Hom_apply, (evaluate).map_mul] at hfactorization
  constructor
  · intro hcomponent
    rw [← hfactorization, hcomponent, zero_mul]
  · intro hequation
    rw [← hfactorization] at hequation
    exact (mul_eq_zero.mp hequation).resolve_right hdiscardedEval

/-- Return no component for a last-variable constant and otherwise the unique retained positive
degree component. -/
def components (data : Data r E) : List (CMvPolynomial (r + 1) E) :=
  if data.regular.natDegree = 0 then [] else [component data]

/-- The output is empty exactly in the degree-zero branch. -/
theorem components_eq_nil_iff (data : Data r E) :
    components data = [] ↔ data.regular.natDegree = 0 := by
  simp [components]

/-- Every nonempty output is the singleton retained component and has positive last-variable
degree. -/
theorem components_eq_singleton_of_ne_zero (data : Data r E)
    (hdegree : data.regular.natDegree ≠ 0) :
    components data = [component data] ∧ 0 < data.regular.natDegree := by
  exact ⟨by simp [components, hdegree], Nat.pos_of_ne_zero hdegree⟩

/-- Primitivity is preserved by both exact divisor removals. -/
theorem Certificate.regular_primitive
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) : data.regular.toPoly.IsPrimitive := by
  have hsupportPrimitive : data.support.toPoly.IsPrimitive := by
    apply Polynomial.isPrimitive_of_dvd certificate.core_primitive
    refine ⟨data.repeatedDivisor.toPoly, ?_⟩
    have hsemantic := congrArg CPolynomial.toPoly certificate.support_factor
    rw [CPolynomial.toPoly_mul] at hsemantic
    exact hsemantic.symm
  apply Polynomial.isPrimitive_of_dvd hsupportPrimitive
  refine ⟨data.singularDivisor.toPoly, ?_⟩
  have hsemantic := congrArg CPolynomial.toPoly certificate.regular_factor
  rw [CPolynomial.toPoly_mul] at hsemantic
  exact hsemantic.symm

/-- A primitive retained polynomial of last-variable degree zero is a unit. -/
theorem Certificate.regular_isUnit_of_natDegree_eq_zero
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hdegree : data.regular.natDegree = 0) : IsUnit data.regular := by
  have hpolyDegree : data.regular.toPoly.natDegree = 0 := by
    simpa [CPolynomial.natDegree_toPoly] using hdegree
  have heq := Polynomial.eq_C_of_natDegree_eq_zero hpolyDegree
  have hcontent := certificate.regular_primitive.content_eq_one
  rw [heq, Polynomial.content_C] at hcontent
  have hcoefficient : IsUnit (data.regular.toPoly.coeff 0) := normalize_eq_one.mp hcontent
  have hpolyUnit : IsUnit data.regular.toPoly := by
    rw [heq, Polynomial.isUnit_C]
    exact hcoefficient
  have hstoredUnit := hpolyUnit.map CPolynomial.ringEquiv.symm.toRingHom
  have hinverse : CPolynomial.ringEquiv.symm data.regular.toPoly = data.regular := by
    rw [← CPolynomial.ringEquiv_apply, RingEquiv.symm_apply_apply]
  change IsUnit (CPolynomial.ringEquiv.symm data.regular.toPoly) at hstoredUnit
  rw [hinverse] at hstoredUnit
  exact hstoredUnit

/-- The component list is empty exactly when the retained last-variable polynomial is a unit. -/
theorem Certificate.components_eq_nil_iff_isUnit
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    components data = [] ↔ IsUnit data.regular := by
  rw [components_eq_nil_iff]
  constructor
  · exact certificate.regular_isUnit_of_natDegree_eq_zero
  · intro hunit
    have hmapped := hunit.map CPolynomial.ringEquiv.toRingHom
    have hpolyUnit : IsUnit data.regular.toPoly := by
      change IsUnit (CPolynomial.ringEquiv data.regular) at hmapped
      rw [CPolynomial.ringEquiv_apply] at hmapped
      exact hmapped
    have hdegree : data.regular.toPoly.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hpolyUnit
    simpa [CPolynomial.natDegree_toPoly] using hdegree

/-- The component list is empty exactly when the retained polynomial has no root over an
algebraic closure of the rational function field in the earlier jet variables. -/
theorem Certificate.components_eq_nil_iff_no_generic_root
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    components data = [] ↔
      ∀ x : AlgebraicClosure (FractionRing (CMvPolynomial r E)),
        ¬ ((genericPolynomial data.regular).map
          (algebraMap (FractionRing (CMvPolynomial r E))
            (AlgebraicClosure (FractionRing (CMvPolynomial r E))))).IsRoot x := by
  let K₀ := FractionRing (CMvPolynomial r E)
  let L := AlgebraicClosure K₀
  let toK₀ := algebraMap (CMvPolynomial r E) K₀
  let toL := algebraMap K₀ L
  let mapped := (genericPolynomial data.regular).map toL
  constructor
  · intro hempty x hroot
    have hunit := (certificate.components_eq_nil_iff_isUnit).mp hempty
    have hpolyUnit : IsUnit data.regular.toPoly := by
      have hmapped := hunit.map CPolynomial.ringEquiv.toRingHom
      change IsUnit (CPolynomial.ringEquiv data.regular) at hmapped
      rw [CPolynomial.ringEquiv_apply] at hmapped
      exact hmapped
    have hgenericUnit : IsUnit (genericPolynomial data.regular) :=
      hpolyUnit.map (Polynomial.mapRingHom toK₀)
    have hmappedUnit : IsUnit mapped := hgenericUnit.map (Polynomial.mapRingHom toL)
    have hevalUnit : IsUnit (mapped.eval x) := hmappedUnit.map (Polynomial.evalRingHom x)
    exact hevalUnit.ne_zero hroot
  · intro hnoRoot
    by_contra hnonempty
    have hdegree : data.regular.natDegree ≠ 0 := by
      intro hzero
      exact hnonempty ((components_eq_nil_iff data).mpr hzero)
    have hpolyNe : data.regular.toPoly ≠ 0 := by
      intro hzero
      apply hdegree
      have hstoredZero : data.regular = 0 := by
        apply CPolynomial.toPoly_injective
        rw [hzero, CPolynomial.toPoly_zero]
      rw [hstoredZero]
      have hpolyZero : (0 : CPolynomial (CMvPolynomial r E)).toPoly.natDegree = 0 := by
        rw [CPolynomial.toPoly_zero, Polynomial.natDegree_zero]
      simpa [CPolynomial.natDegree_toPoly] using hpolyZero
    have hsourceDegree : data.regular.toPoly.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hpolyNe]
      intro hpolyDegree
      apply hdegree
      simpa [CPolynomial.natDegree_toPoly] using hpolyDegree
    have hgenericDegree : (genericPolynomial data.regular).degree ≠ 0 := by
      rw [genericPolynomial, Polynomial.degree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective (CMvPolynomial r E) K₀)]
      exact hsourceDegree
    have hmappedDegree : mapped.degree ≠ 0 := by
      change ((genericPolynomial data.regular).map toL).degree ≠ 0
      rw [Polynomial.degree_map_eq_of_injective toL.injective]
      exact hgenericDegree
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root mapped hmappedDegree
    exact hnoRoot x hx

/-- A positive-degree branch emits the unique retained component and that polynomial has a root
over an algebraic closure of the earlier-variable rational function field. -/
theorem Certificate.components_eq_singleton_and_exists_generic_root
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hdegree : data.regular.natDegree ≠ 0) :
    components data = [component data] ∧ 0 < data.regular.natDegree ∧
      ∃ x : AlgebraicClosure (FractionRing (CMvPolynomial r E)),
        ((genericPolynomial data.regular).map
          (algebraMap (FractionRing (CMvPolynomial r E))
            (AlgebraicClosure (FractionRing (CMvPolynomial r E))))).IsRoot x := by
  have hsingleton := components_eq_singleton_of_ne_zero data hdegree
  refine ⟨hsingleton.1, hsingleton.2, ?_⟩
  by_contra hnoRoot
  have hnone : ∀ x : AlgebraicClosure (FractionRing (CMvPolynomial r E)),
      ¬ ((genericPolynomial data.regular).map
        (algebraMap (FractionRing (CMvPolynomial r E))
          (AlgebraicClosure (FractionRing (CMvPolynomial r E))))).IsRoot x := by
    simpa only [not_exists] using hnoRoot
  have hempty := certificate.components_eq_nil_iff_no_generic_root.mpr hnone
  exact hdegree ((components_eq_nil_iff data).mp hempty)

/-- The empty degree branch contains no regular equation root over any extension field. -/
theorem Certificate.components_empty_no_regular_root
    {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hseparantIdentity : separant =
      CMvPolynomial.partialDerivative (Fin.last r) equation)
    (hempty : components data = [])
    {K : Type*} [Field K] (embedding : E →+* K) (point : Fin (r + 1) → K) :
    ¬(CMvPolynomial.eval₂ embedding point equation = 0 ∧
      CMvPolynomial.eval₂ embedding point separant ≠ 0) := by
  have hdegree := (components_eq_nil_iff data).mp hempty
  have hregularUnit := certificate.regular_isUnit_of_natDegree_eq_zero hdegree
  have hcomponentUnit : IsUnit (component data) :=
    hregularUnit.map (flattenLast (r := r) (E := E))
  have hevalUnit : IsUnit (CMvPolynomial.eval₂ embedding point (component data)) :=
    hcomponentUnit.map (CMvPolynomial.eval₂Hom embedding point)
  rintro ⟨hequation, hseparant⟩
  have hcomponent := (certificate.eval₂_component_iff_equation
    hseparantIdentity embedding point hseparant).mpr hequation
  exact hevalUnit.ne_zero hcomponent

/-- Run the two-gcd producer on the actual initial equation and its actual highest-jet partial. -/
def runInitial?
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (center : E) (T : CMvPolynomial (r + 2) E) : Option (Data r E) :=
  run? coefficientGcd coefficientDivide flatDivide
    (FastTaylor.initialEquation center T) (FastTaylor.initialSeparant center T)

/-- Exact supplied arithmetic operations make the actual initial-stage producer total whenever
its specialized equation is nonzero. -/
theorem runInitial?_exists_certificate
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (coefficientGcdLaws : GcdLaws coefficientGcd)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    (flatDivideLaws : DivideLaws flatDivide)
    (center : E) (T : CMvPolynomial (r + 2) E)
    (hequation : FastTaylor.initialEquation center T ≠ 0) :
    ∃ data, runInitial? coefficientGcd coefficientDivide flatDivide center T = some data ∧
      Certificate (FastTaylor.initialEquation center T)
        (FastTaylor.initialSeparant center T) data := by
  exact run?_exists_certificate coefficientGcd coefficientDivide flatDivide coefficientGcdLaws
    coefficientDivideLaws flatDivideLaws _ _ hequation

/-- Every successful actual-stage run satisfies the extension-field regular-root equivalence. -/
theorem runInitial?_eval₂_component_iff
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E → Option (CMvPolynomial r E))
    (flatDivide : CMvPolynomial (r + 1) E → CMvPolynomial (r + 1) E →
      Option (CMvPolynomial (r + 1) E))
    (coefficientGcdLaws : GcdLaws coefficientGcd)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    (flatDivideLaws : DivideLaws flatDivide)
    (center : E) (T : CMvPolynomial (r + 2) E) (data : Data r E)
    (hequation : FastTaylor.initialEquation center T ≠ 0)
    (hrun : runInitial? coefficientGcd coefficientDivide flatDivide center T = some data)
    {K : Type*} [Field K] (embedding : E →+* K) (point : Fin (r + 1) → K)
    (hseparant : CMvPolynomial.eval₂ embedding point
      (FastTaylor.initialSeparant center T) ≠ 0) :
    CMvPolynomial.eval₂ embedding point (component data) = 0 ↔
      CMvPolynomial.eval₂ embedding point (FastTaylor.initialEquation center T) = 0 := by
  have certificate := run?_certificate coefficientGcd coefficientDivide flatDivide
    coefficientGcdLaws coefficientDivideLaws flatDivideLaws _ _ data hequation hrun
  exact certificate.eval₂_component_iff_equation
    (initialSeparant_eq_partialDerivative_last center T) embedding point hseparant

end ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.General
