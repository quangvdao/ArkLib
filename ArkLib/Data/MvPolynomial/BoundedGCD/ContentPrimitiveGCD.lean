/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.GaussPreservation

/-!
# Content and primitive-part gcd assembly

This module combines executable coefficient content with the certified primitive
pseudo-remainder sequence. Zero inputs are handled directly. For two nonzero inputs, both are
normalized, their coefficient contents are passed to the supplied lower-dimensional gcd, and
their primitive parts are passed to the normalized pseudo-gcd.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD

open CompPoly
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD.GaussPreservation

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]

/-- Assemble a full gcd candidate from executable coefficient operations. -/
def compute? (gcd : R → R → R) (divide : R → R → Option R)
    (left right : CPolynomial R) : Option (CPolynomial R) :=
  if left = 0 then some right
  else if right = 0 then some left
  else
    match normalize? gcd divide left, normalize? gcd divide right with
    | some leftData, some rightData =>
        (NormalizedPseudoRemainder.candidate? gcd divide
          leftData.primitive rightData.primitive).map fun primitive =>
            CPolynomial.C (gcd leftData.content rightData.content) * primitive
    | _, _ => none

/-- Algebraic certificate for a greatest common divisor returned by `compute?`. -/
structure Certificate (left right result : CPolynomial R) : Prop where
  dvd_left : result ∣ left
  dvd_right : result ∣ right
  greatest : ∀ common, common ∣ left → common ∣ right → common ∣ result

omit [DecidableEq R] in
private theorem toPoly_dvd_iff (left right : CPolynomial R) :
    left.toPoly ∣ right.toPoly ↔ left ∣ right := by
  constructor
  · rintro ⟨quotient, hquotient⟩
    refine ⟨CPolynomial.ringEquiv.symm quotient, ?_⟩
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul]
    have hinverse : (CPolynomial.ringEquiv.symm quotient).toPoly = quotient := by
      rw [← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
    rw [hinverse]
    exact hquotient
  · rintro ⟨quotient, hquotient⟩
    refine ⟨quotient.toPoly, ?_⟩
    rw [← CPolynomial.toPoly_mul, hquotient]

omit [DecidableEq R] in
private theorem C_dvd_C {left right : R} (h : left ∣ right) :
    CPolynomial.C left ∣ CPolynomial.C right := by
  obtain ⟨quotient, rfl⟩ := h
  refine ⟨CPolynomial.C quotient, ?_⟩
  apply CPolynomial.toPoly_injective
  simp [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]

private theorem normalization_content_ne_zero (gcd : R → R → R)
    (divide : R → R → Option R) (p : CPolynomial R) (data : Data R)
    (h : normalize? gcd divide p = some data) (hp : p ≠ 0) : data.content ≠ 0 := by
  intro hzero
  apply hp
  rw [← normalize?_identity gcd divide p data h, hzero]
  simp

section Gauss

variable [NormalizedGCDMonoid R]

/-- The semantic content of an input is associated to the executable coefficient content returned
by normalization. -/
private theorem content_associated_normalization (gcd : R → R → R)
    (divide : R → R → Option R) (p : CPolynomial R) (data : Data R)
    (h : normalize? gcd divide p = some data)
    (hprimitive : data.primitive.toPoly.IsPrimitive) :
    Associated p.toPoly.content data.content := by
  have hidentity := congrArg CPolynomial.toPoly <| normalize?_identity gcd divide p data h
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] at hidentity
  rw [← hidentity]
  have hassociated := Polynomial.associated_content_C_mul
    data.content data.primitive.toPoly
  rw [hprimitive.content_eq_one, mul_one] at hassociated
  exact hassociated

/-- Successful assembly on two nonzero normalized inputs has the greatest-common-divisor
property. -/
private theorem certificate_of_nonzero (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (left right : CPolynomial R)
    (hleft : left ≠ 0) (hright : right ≠ 0) (leftData rightData : Data R)
    (hleftData : normalize? gcd divide left = some leftData)
    (hrightData : normalize? gcd divide right = some rightData)
    (primitive : CPolynomial R)
    (hprimitive : NormalizedPseudoRemainder.candidate? gcd divide
      leftData.primitive rightData.primitive = some primitive) :
    Certificate left right
      (CPolynomial.C (gcd leftData.content rightData.content) * primitive) := by
  have hleftPrimitive := normalize?_toPoly_isPrimitive gcd divide gcdLaws divideLaws
    left leftData hleftData hleft
  have hrightPrimitive := normalize?_toPoly_isPrimitive gcd divide gcdLaws divideLaws
    right rightData hrightData hright
  have primitiveCertificate := candidate?_certificate gcd divide gcdLaws divideLaws
    leftData.primitive rightData.primitive primitive hleftPrimitive
    (Or.inr hrightPrimitive) hprimitive
  have hleftDivides :
      CPolynomial.C (gcd leftData.content rightData.content) * primitive ∣ left := by
    have hcontentDvd : CPolynomial.C (gcd leftData.content rightData.content) ∣
        CPolynomial.C leftData.content := C_dvd_C <| gcdLaws.dvd_left ..
    have hproduct := mul_dvd_mul hcontentDvd primitiveCertificate.dvd_left
    exact hproduct.trans <| by
      rw [normalize?_identity gcd divide left leftData hleftData]
  have hrightDivides :
      CPolynomial.C (gcd leftData.content rightData.content) * primitive ∣ right := by
    have hcontentDvd : CPolynomial.C (gcd leftData.content rightData.content) ∣
        CPolynomial.C rightData.content := C_dvd_C <| gcdLaws.dvd_right ..
    have hproduct := mul_dvd_mul hcontentDvd primitiveCertificate.dvd_right
    exact hproduct.trans <| by
      rw [normalize?_identity gcd divide right rightData hrightData]
  refine ⟨hleftDivides, hrightDivides, ?_⟩
  intro common hcommonLeft hcommonRight
  let commonPrimitive : CPolynomial R :=
    CPolynomial.ringEquiv.symm common.toPoly.primPart
  have hcommonPrimitiveToPoly : commonPrimitive.toPoly = common.toPoly.primPart := by
    rw [← CPolynomial.ringEquiv_apply, RingEquiv.apply_symm_apply]
  have hcommonPrimitive : commonPrimitive.toPoly.IsPrimitive := by
    rw [hcommonPrimitiveToPoly]
    exact common.toPoly.isPrimitive_primPart
  have hcommonLeftSemantic := (toPoly_dvd_iff common left).mpr hcommonLeft
  have hcommonRightSemantic := (toPoly_dvd_iff common right).mpr hcommonRight
  have hcontentLeftSemantic : common.toPoly.content ∣ left.toPoly.content :=
    ((Polynomial.dvd_iff_content_dvd_content_and_primPart_dvd_primPart
      ((CPolynomial.toPoly_eq_zero_iff left).not.mpr hleft)).mp hcommonLeftSemantic).1
  have hcontentRightSemantic : common.toPoly.content ∣ right.toPoly.content :=
    ((Polynomial.dvd_iff_content_dvd_content_and_primPart_dvd_primPart
      ((CPolynomial.toPoly_eq_zero_iff right).not.mpr hright)).mp hcommonRightSemantic).1
  have hcontentLeft : common.toPoly.content ∣ leftData.content :=
    ((content_associated_normalization gcd divide left leftData hleftData
      hleftPrimitive).dvd_iff_dvd_right).mp hcontentLeftSemantic
  have hcontentRight : common.toPoly.content ∣ rightData.content :=
    ((content_associated_normalization gcd divide right rightData hrightData
      hrightPrimitive).dvd_iff_dvd_right).mp hcontentRightSemantic
  have hcontent : common.toPoly.content ∣ gcd leftData.content rightData.content :=
    gcdLaws.greatest hcontentLeft hcontentRight
  have hcommonPrimitiveDvdCommon : commonPrimitive ∣ common := by
    apply (toPoly_dvd_iff commonPrimitive common).mp
    rw [hcommonPrimitiveToPoly]
    exact common.toPoly.primPart_dvd
  have hcommonPrimitiveLeft : commonPrimitive ∣ leftData.primitive := by
    have hproduct := (toPoly_dvd_iff commonPrimitive left).mpr <|
      hcommonPrimitiveDvdCommon.trans hcommonLeft
    have hidentity := congrArg CPolynomial.toPoly <|
      normalize?_identity gcd divide left leftData hleftData
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] at hidentity
    have hproductSemantic : commonPrimitive.toPoly ∣
        Polynomial.C leftData.content * leftData.primitive.toPoly := by
      rw [hidentity]
      exact hproduct
    exact (toPoly_dvd_iff commonPrimitive leftData.primitive).mp <|
      cancel_content leftData.content hcommonPrimitive hleftPrimitive
        (normalization_content_ne_zero gcd divide left leftData hleftData hleft)
        hproductSemantic
  have hcommonPrimitiveRight : commonPrimitive ∣ rightData.primitive := by
    have hproduct := (toPoly_dvd_iff commonPrimitive right).mpr <|
      hcommonPrimitiveDvdCommon.trans hcommonRight
    have hidentity := congrArg CPolynomial.toPoly <|
      normalize?_identity gcd divide right rightData hrightData
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] at hidentity
    have hproductSemantic : commonPrimitive.toPoly ∣
        Polynomial.C rightData.content * rightData.primitive.toPoly := by
      rw [hidentity]
      exact hproduct
    exact (toPoly_dvd_iff commonPrimitive rightData.primitive).mp <|
      cancel_content rightData.content hcommonPrimitive hrightPrimitive
        (normalization_content_ne_zero gcd divide right rightData hrightData hright)
        hproductSemantic
  have hprimitiveDvd : commonPrimitive ∣ primitive :=
    primitiveCertificate.greatest commonPrimitive hcommonPrimitiveLeft hcommonPrimitiveRight
  have hassembled : CPolynomial.C common.toPoly.content * commonPrimitive ∣
      CPolynomial.C (gcd leftData.content rightData.content) * primitive :=
    mul_dvd_mul (C_dvd_C hcontent) hprimitiveDvd
  have hcommonDecomposition : CPolynomial.C common.toPoly.content * commonPrimitive = common := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C, hcommonPrimitiveToPoly]
    exact common.toPoly.eq_C_content_mul_primPart.symm
  rw [hcommonDecomposition] at hassembled
  exact hassembled

/-- Exact lower-dimensional operations make full gcd assembly total for arbitrary inputs and
certify its universal gcd property. -/
theorem compute?_exists_certificate (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (left right : CPolynomial R) :
    ∃ result, compute? gcd divide left right = some result ∧ Certificate left right result := by
  by_cases hleft : left = 0
  · subst left
    exact ⟨right, by simp [compute?],
      ⟨dvd_zero right, dvd_rfl, fun common _ hcommon => hcommon⟩⟩
  · by_cases hright : right = 0
    · subst right
      exact ⟨left, by simp [compute?, hleft],
        ⟨dvd_rfl, dvd_zero left, fun common hcommon _ => hcommon⟩⟩
    · obtain ⟨leftData, hleftData⟩ := normalize?_exists gcd divide gcdLaws divideLaws left hleft
      obtain ⟨rightData, hrightData⟩ := normalize?_exists gcd divide gcdLaws divideLaws right hright
      have hleftPrimitive := normalize?_toPoly_isPrimitive gcd divide gcdLaws divideLaws
        left leftData hleftData hleft
      have hrightPrimitive := normalize?_toPoly_isPrimitive gcd divide gcdLaws divideLaws
        right rightData hrightData hright
      obtain ⟨primitive, hprimitive, _⟩ := candidate?_exists_certificate gcd divide gcdLaws
        divideLaws leftData.primitive rightData.primitive hleftPrimitive (Or.inr hrightPrimitive)
      refine ⟨CPolynomial.C (gcd leftData.content rightData.content) * primitive, ?_, ?_⟩
      · simp [compute?, hleft, hright, hleftData, hrightData, hprimitive]
      · exact certificate_of_nonzero gcd divide gcdLaws divideLaws left right hleft hright
          leftData rightData hleftData hrightData primitive hprimitive

/-- Every successful full gcd computation carries its divisibility and maximality certificate. -/
theorem compute?_certificate (gcd : R → R → R) (divide : R → R → Option R)
    (gcdLaws : GcdLaws gcd) (divideLaws : DivideLaws divide)
    (left right result : CPolynomial R) (hresult : compute? gcd divide left right = some result) :
    Certificate left right result := by
  obtain ⟨candidate, hcandidate, certificate⟩ :=
    compute?_exists_certificate gcd divide gcdLaws divideLaws left right
  rw [hresult] at hcandidate
  cases Option.some.inj hcandidate
  exact certificate

end Gauss

end CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD
