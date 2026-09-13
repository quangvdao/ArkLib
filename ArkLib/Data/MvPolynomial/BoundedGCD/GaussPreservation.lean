/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.NormalizedPseudoRemainder
public import Mathlib.RingTheory.Polynomial.Content
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.ToPoly.Core

/-!
# Gauss preservation for normalized pseudo-remainders

This module supplies the proof-only Gauss lemmas which upgrade checked coefficient normalization
to a primitive polynomial. The executable definitions remain those of `CoefficientNormalization`
and `NormalizedPseudoRemainder`.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.GaussPreservation

open CompPoly
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]

/-- A successful normalization exposes the coefficientwise division which produced it. -/
theorem normalize?_divideCoefficients_eq (gcd : R → R → R)
    (divide : R → R → Option R) (p : CPolynomial R) (data : Data R)
    (h : normalize? gcd divide p = some data) :
    divideCoefficients? divide data.content p = some data.primitive := by
  unfold normalize? at h
  dsimp only at h
  cases hdivide : divideCoefficients? divide (coefficientContent gcd p) p with
  | none => simp [hdivide] at h
  | some primitive =>
    by_cases hidentity : CPolynomial.C (coefficientContent gcd p) * primitive = p
    · simp only [hdivide, hidentity, ↓reduceIte, Option.some.injEq] at h
      subst data
      exact hdivide
    · simp [hdivide, hidentity] at h

/-- Checked removal of a greatest common coefficient produces a primitive semantic polynomial. -/
theorem normalize?_toPoly_isPrimitive (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (p : CPolynomial R) (data : Data R)
    (h : normalize? gcd divide p = some data) (hp : p ≠ 0) :
    data.primitive.toPoly.IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro scalar hscalar
  have hcontent : data.content ≠ 0 := by
    intro hzero
    apply hp
    rw [← normalize?_identity gcd divide p data h, hzero]
    simp
  have hdivide := normalize?_divideCoefficients_eq gcd divide p data h
  unfold divideCoefficients? at hdivide
  cases hlist : divideList? divide data.content p.val.toList with
  | none => simp [hlist] at hdivide
  | some quotients =>
    simp only [hlist, Option.map_some, Option.some.injEq] at hdivide
    have hcoefficients := divideList?_identity divide divideLaws data.content
      p.val.toList quotients hlist
    have hscalarCoefficients := (Polynomial.C_dvd_iff_dvd_coeff scalar
      data.primitive.toPoly).mp hscalar
    have hproduct : data.content * scalar ∣ coefficientContent gcd p := by
      apply dvd_coefficientContent gcd gcdLaws p
      intro coefficient hcoefficient
      rw [hcoefficients] at hcoefficient
      obtain ⟨quotient, hquotient, rfl⟩ := List.mem_map.mp hcoefficient
      obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hquotient
      have hprimitiveCoefficient : data.primitive.toPoly.coeff index = quotient := by
        rw [← CPolynomial.coeff_toPoly, ← hdivide, CPolynomial.coeff_ofArray,
          Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_eq_getElem hindex, hget, Option.getD_some]
      obtain ⟨scalarQuotient, hscalarQuotient⟩ := hscalarCoefficients index
      refine ⟨scalarQuotient, ?_⟩
      rw [hprimitiveCoefficient] at hscalarQuotient
      calc
        data.content * quotient = data.content * (scalar * scalarQuotient) := by
          rw [hscalarQuotient]
        _ = (data.content * scalar) * scalarQuotient := by ring
    rw [← normalize?_content_eq gcd divide p data h] at hproduct
    obtain ⟨factor, hfactor⟩ := hproduct
    apply IsUnit.of_mul_eq_one factor
    apply mul_left_cancel₀ hcontent
    calc
      data.content * (scalar * factor) = (data.content * scalar) * factor := by ring
      _ = data.content := hfactor.symm
      _ = data.content * 1 := by simp

omit [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R] in
private theorem divideList?_exists (divide : R → R → Option R)
    (laws : DivideLaws divide) (content : R) (hcontent : content ≠ 0)
    (coefficients : List R) (hcoefficients : ∀ coefficient ∈ coefficients,
      content ∣ coefficient) :
    ∃ quotients, divideList? divide content coefficients = some quotients := by
  induction coefficients with
  | nil => exact ⟨[], rfl⟩
  | cons coefficient coefficients ih =>
    obtain ⟨quotient, hquotient⟩ := laws.complete hcontent <|
      hcoefficients coefficient (List.mem_cons_self ..)
    obtain ⟨quotients, hquotients⟩ := ih fun item hitem =>
      hcoefficients item (List.mem_cons_of_mem coefficient hitem)
    exact ⟨quotient :: quotients, by simp [divideList?, hquotient, hquotients]⟩

private theorem array_getD_toList {α : Type*} (values : Array α) (index : ℕ)
    (default : α) : values.getD index default = values.toList.getD index default := by
  cases values
  simp

omit [DecidableEq R] [IsDomain R] in
private theorem coeff_eq_toList_getD (p : CPolynomial R) (index : ℕ) :
    p.coeff index = p.val.toList.getD index 0 := by
  rw [CPolynomial.coeff_toPoly]
  change p.val.toPoly.coeff index = _
  rw [CPolynomial.Raw.coeff_toPoly, CPolynomial.Raw.coeff,
    Array.getD_eq_getD_getElem?,
    ← Array.getElem?_eq_toList, List.getD_eq_getElem?_getD]

omit [DecidableEq R] in
/-- Exact lower-dimensional division reconstructs the polynomial produced coefficientwise. -/
private theorem divideCoefficients?_exists_identity (divide : R → R → Option R)
    (laws : DivideLaws divide) (content : R) (hcontent : content ≠ 0)
    (p : CPolynomial R) (hcoefficients : ∀ coefficient ∈ p.val.toList,
      content ∣ coefficient) :
    ∃ primitive, divideCoefficients? divide content p = some primitive ∧
      CPolynomial.C content * primitive = p := by
  obtain ⟨quotients, hquotients⟩ := divideList?_exists divide laws content hcontent
    p.val.toList hcoefficients
  refine ⟨CPolynomial.ofArray quotients.toArray, ?_, ?_⟩
  · simp [divideCoefficients?, hquotients]
  · apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]
    apply Polynomial.ext
    intro index
    rw [Polynomial.coeff_C_mul, ← CPolynomial.coeff_toPoly,
      CPolynomial.coeff_ofArray, array_getD_toList, List.toList_toArray,
      ← CPolynomial.coeff_toPoly]
    have hlist := divideList?_identity divide laws content p.val.toList quotients hquotients
    rw [coeff_eq_toList_getD, hlist]
    simpa using (List.getD_map quotients 0 (n := index)
      (fun quotient => content * quotient)).symm

/-- Greatest coefficient content and exact coefficient division make normalization total on
nonzero inputs. -/
theorem normalize?_exists (gcd : R → R → R) (divide : R → R → Option R)
    (gcdLaws : GcdLaws gcd) (divideLaws : DivideLaws divide)
    (p : CPolynomial R) (hp : p ≠ 0) : ∃ data, normalize? gcd divide p = some data := by
  have hcontent : coefficientContent gcd p ≠ 0 := by
    intro hzero
    apply hp
    rw [CPolynomial.eq_zero_iff_coeff_zero]
    intro index
    by_cases hindex : index < p.val.size
    · have hmem : p.val[index] ∈ p.val.toList := by simp
      have hdvd := coefficientContent_dvd_of_mem gcd gcdLaws p hmem
      rw [hzero, zero_dvd_iff] at hdvd
      rw [CPolynomial.coeff_toPoly]
      change p.val.toPoly.coeff index = 0
      rw [CPolynomial.Raw.coeff_toPoly,
        CPolynomial.Raw.Trim.coeff_eq_getElem hindex]
      exact hdvd
    · exact CPolynomial.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hindex)
  obtain ⟨primitive, hdivide, hidentity⟩ := divideCoefficients?_exists_identity divide
    divideLaws (coefficientContent gcd p) hcontent p fun coefficient hcoefficient =>
      coefficientContent_dvd_of_mem gcd gcdLaws p hcoefficient
  exact ⟨⟨coefficientContent gcd p, primitive⟩, by
    simp [normalize?, hdivide, hidentity]⟩

/-- Exact coefficient operations make a normalized pseudo-remainder step total. -/
theorem compute?_exists (gcd : R → R → R) (divide : R → R → Option R)
    (gcdLaws : GcdLaws gcd) (divideLaws : DivideLaws divide)
    (dividend divisor : CPolynomial R) :
    ∃ data, NormalizedPseudoRemainder.compute? gcd divide dividend divisor = some data := by
  by_cases hraw : (pseudoDivide dividend divisor).remainder = 0
  · exact ⟨⟨(pseudoDivide dividend divisor).scale,
      (pseudoDivide dividend divisor).quotient, 1, 0⟩, by
        simp [NormalizedPseudoRemainder.compute?, hraw]⟩
  · obtain ⟨normalized, hnormalized⟩ := normalize?_exists gcd divide gcdLaws divideLaws
      (pseudoDivide dividend divisor).remainder hraw
    exact ⟨⟨(pseudoDivide dividend divisor).scale,
      (pseudoDivide dividend divisor).quotient, normalized.content, normalized.primitive⟩, by
        simp [NormalizedPseudoRemainder.compute?, hraw, hnormalized]⟩

/-- Every bounded pseudo-division run retains a nonzero scale for a nonzero divisor. -/
theorem pseudoDivideAux_scale_ne_zero (fuel : ℕ) (divisor : CPolynomial R)
    (state : PseudoDivisionState R) (hdivisor : divisor ≠ 0) (hscale : state.scale ≠ 0) :
    (pseudoDivideAux fuel divisor state).scale ≠ 0 := by
  induction fuel generalizing state with
  | zero => exact hscale
  | succ fuel ih =>
    simp only [pseudoDivideAux]
    split
    · exact hscale
    · apply ih
      exact mul_ne_zero (CPolynomial.leadingCoeff_ne_zero hdivisor) hscale

/-- The default pseudo-division run has nonzero scale for a nonzero divisor. -/
theorem pseudoDivide_scale_ne_zero (dividend divisor : CPolynomial R)
    (hdivisor : divisor ≠ 0) : (pseudoDivide dividend divisor).scale ≠ 0 :=
  pseudoDivideAux_scale_ne_zero _ divisor (.initial dividend) hdivisor one_ne_zero

omit [DecidableEq R] in
/-- Stored divisibility agrees with divisibility after passing to the semantic polynomial. -/
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

section Gauss

variable [NormalizedGCDMonoid R]

omit [DecidableEq R] [BEq R] [LawfulBEq R] in
/-- A primitive polynomial divisor cannot be hidden in a nonzero constant factor. -/
theorem cancel_content {divisor polynomial : Polynomial R} (content : R)
    (hdivisor : divisor.IsPrimitive) (hpolynomial : polynomial.IsPrimitive)
    (hcontent : content ≠ 0) (h : divisor ∣ Polynomial.C content * polynomial) :
    divisor ∣ polynomial := by
  have hproduct : Polynomial.C content * polynomial ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hcontent) hpolynomial.ne_zero
  rw [← hdivisor.dvd_primPart_iff_dvd hproduct] at h
  have hassociated := Polynomial.associated_primPart_mul hproduct
  rw [hpolynomial.primPart_eq] at hassociated
  exact h.trans <| (hassociated.trans <| associated_unit_mul_left polynomial _
    (Polynomial.isUnit_primPart_C content)).dvd

omit [NormalizedGCDMonoid R] in
/-- A successful nonzero normalized pseudo-remainder is primitive. -/
theorem compute?_remainder_toPoly_isPrimitive (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (dividend divisor : CPolynomial R)
    (data : NormalizedPseudoRemainder.Data R)
    (h : NormalizedPseudoRemainder.compute? gcd divide dividend divisor = some data)
    (hremainder : data.remainder ≠ 0) : data.remainder.toPoly.IsPrimitive := by
  have hraw : (pseudoDivide dividend divisor).remainder ≠ 0 := by
    exact fun hzero => hremainder <|
      (NormalizedPseudoRemainder.compute?_remainder_eq_zero_iff
        gcd divide dividend divisor data h).mpr hzero
  unfold NormalizedPseudoRemainder.compute? at h
  dsimp only at h
  simp only [hraw, ↓reduceIte] at h
  cases hnormalize : normalize? gcd divide (pseudoDivide dividend divisor).remainder with
  | none => simp [hnormalize] at h
  | some normalized =>
    simp only [hnormalize, Option.some.injEq] at h
    subst data
    exact normalize?_toPoly_isPrimitive gcd divide gcdLaws divideLaws _ normalized
      hnormalize hraw

/-- Removing checked coefficient content preserves every primitive common divisor. -/
theorem compute?_common_divisor_preserved_primitive (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (dividend divisor common : CPolynomial R)
    (data : NormalizedPseudoRemainder.Data R)
    (h : NormalizedPseudoRemainder.compute? gcd divide dividend divisor = some data)
    (hremainder : data.remainder ≠ 0) (hcommonPrimitive : common.toPoly.IsPrimitive)
    (hdividend : common ∣ dividend) (hdivisor : common ∣ divisor) :
    common ∣ data.remainder := by
  have hcontent : data.content ≠ 0 := by
    intro hzero
    apply hremainder
    have hidentity := NormalizedPseudoRemainder.compute?_raw_remainder_identity
      gcd divide dividend divisor data h
    have hraw : (pseudoDivide dividend divisor).remainder ≠ 0 := fun hzero' => hremainder <|
      (NormalizedPseudoRemainder.compute?_remainder_eq_zero_iff
        gcd divide dividend divisor data h).mpr hzero'
    exact False.elim <| hraw <| by simpa [hzero] using hidentity.symm
  have hproductStored := NormalizedPseudoRemainder.compute?_common_divisor_preserved
    gcd divide dividend divisor common data h hdividend hdivisor
  have hproduct : common.toPoly ∣ Polynomial.C data.content * data.remainder.toPoly := by
    simpa [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] using
      (toPoly_dvd_iff common (CPolynomial.C data.content * data.remainder)).mpr hproductStored
  have hremainderPrimitive := compute?_remainder_toPoly_isPrimitive gcd divide gcdLaws
    divideLaws dividend divisor data h hremainder
  exact (toPoly_dvd_iff common data.remainder).mp <|
    cancel_content data.content hcommonPrimitive hremainderPrimitive hcontent hproduct

/-- For primitive inputs, every common divisor remains a divisor of a nonzero normalized
pseudo-remainder. -/
theorem compute?_common_divisor_preserved (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (dividend divisor common : CPolynomial R)
    (data : NormalizedPseudoRemainder.Data R)
    (h : NormalizedPseudoRemainder.compute? gcd divide dividend divisor = some data)
    (hremainder : data.remainder ≠ 0) (hdividendPrimitive : dividend.toPoly.IsPrimitive)
    (hdividend : common ∣ dividend) (hdivisor : common ∣ divisor) :
    common ∣ data.remainder := by
  have hcommonPrimitive : common.toPoly.IsPrimitive :=
    Polynomial.isPrimitive_of_dvd hdividendPrimitive <|
      (toPoly_dvd_iff common dividend).mpr hdividend
  exact compute?_common_divisor_preserved_primitive gcd divide gcdLaws divideLaws
    dividend divisor common data h hremainder hcommonPrimitive hdividend hdivisor

/-- A divisor of the divisor and primitive normalized remainder also divides the primitive
dividend. This is the reverse Gauss step needed by the recursive gcd proof. -/
theorem compute?_common_divisor_reflected (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor common : CPolynomial R)
    (data : NormalizedPseudoRemainder.Data R)
    (h : NormalizedPseudoRemainder.compute? gcd divide dividend divisor = some data)
    (hdividendPrimitive : dividend.toPoly.IsPrimitive)
    (hdivisorPrimitive : divisor.toPoly.IsPrimitive)
    (hcommonPrimitive : common.toPoly.IsPrimitive)
    (hdivisor : common ∣ divisor) (hremainder : common ∣ data.remainder) :
    common ∣ dividend := by
  have hscaled : common ∣ CPolynomial.C data.scale * dividend := by
    rw [NormalizedPseudoRemainder.compute?_certifies gcd divide dividend divisor data h]
    exact dvd_add (dvd_mul_of_dvd_right hdivisor data.quotient)
      (dvd_mul_of_dvd_right hremainder (CPolynomial.C data.content))
  have hscale : data.scale ≠ 0 := by
    rw [NormalizedPseudoRemainder.compute?_scale_eq gcd divide dividend divisor data h]
    exact pseudoDivide_scale_ne_zero dividend divisor <|
      (CPolynomial.toPoly_eq_zero_iff divisor).not.mp hdivisorPrimitive.ne_zero
  have hscaledSemantic : common.toPoly ∣ Polynomial.C data.scale * dividend.toPoly := by
    simpa [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] using
      (toPoly_dvd_iff common (CPolynomial.C data.scale * dividend)).mpr hscaled
  exact (toPoly_dvd_iff common dividend).mp <|
    cancel_content data.scale hcommonPrimitive hdividendPrimitive hscale hscaledSemantic

/-- Proof certificate that an executable candidate is a primitive greatest common divisor. -/
structure CandidateCertificate (left right result : CPolynomial R) : Prop where
  result_isPrimitive : result.toPoly.IsPrimitive
  dvd_left : result ∣ left
  dvd_right : result ∣ right
  greatest : ∀ common, common ∣ left → common ∣ right → common ∣ result

/-- With exact coefficient operations and enough degree fuel, the normalized pseudo-remainder
worker returns a primitive greatest common divisor of primitive inputs. The right input may be zero
to express the terminal recursive state. -/
theorem candidateAux?_exists_certificate (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (fuel : ℕ) (left right : CPolynomial R)
    (hleftPrimitive : left.toPoly.IsPrimitive)
    (hrightPrimitive : right = 0 ∨ right.toPoly.IsPrimitive)
    (hfuel : degreeMeasure right ≤ fuel) :
    ∃ result, NormalizedPseudoRemainder.candidateAux? gcd divide fuel left right = some result ∧
      CandidateCertificate left right result := by
  induction fuel generalizing left right with
  | zero =>
    have hright : right = 0 := by
      by_contra hright
      simp [degreeMeasure, hright] at hfuel
    subst right
    refine ⟨left, by simp [NormalizedPseudoRemainder.candidateAux?], ?_⟩
    exact ⟨hleftPrimitive, dvd_rfl, dvd_zero left, fun common hcommon _ => hcommon⟩
  | succ fuel ih =>
    by_cases hright : right = 0
    · subst right
      refine ⟨left, by simp [NormalizedPseudoRemainder.candidateAux?], ?_⟩
      exact ⟨hleftPrimitive, dvd_rfl, dvd_zero left, fun common hcommon _ => hcommon⟩
    · have hrightSemantic : right.toPoly.IsPrimitive := hrightPrimitive.resolve_left hright
      have hrightStored : right ≠ 0 := hright
      obtain ⟨step, hstep⟩ := compute?_exists gcd divide gcdLaws divideLaws left right
      have hdecrease := NormalizedPseudoRemainder.compute?_degreeMeasure_lt
        gcd divide left right step hstep hrightStored
      have hnextFuel : degreeMeasure step.remainder ≤ fuel := by omega
      have hstepPrimitive : step.remainder = 0 ∨ step.remainder.toPoly.IsPrimitive := by
        by_cases hremainder : step.remainder = 0
        · exact Or.inl hremainder
        · exact Or.inr <| compute?_remainder_toPoly_isPrimitive gcd divide gcdLaws divideLaws
            left right step hstep hremainder
      obtain ⟨result, hresult, certificate⟩ := ih right step.remainder hrightSemantic
        hstepPrimitive hnextFuel
      have hresultLeft : result ∣ left := compute?_common_divisor_reflected gcd divide
        left right result step hstep hleftPrimitive hrightSemantic
        certificate.result_isPrimitive certificate.dvd_left certificate.dvd_right
      refine ⟨result, ?_, ?_⟩
      · simp [NormalizedPseudoRemainder.candidateAux?, hright, hstep, hresult]
      · refine ⟨certificate.result_isPrimitive, hresultLeft, certificate.dvd_left, ?_⟩
        intro common hcommonLeft hcommonRight
        have hcommonRemainder : common ∣ step.remainder := by
          by_cases hremainder : step.remainder = 0
          · simp [hremainder]
          · exact compute?_common_divisor_preserved gcd divide gcdLaws divideLaws
              left right common step hstep hremainder hleftPrimitive hcommonLeft hcommonRight
        exact certificate.greatest common hcommonRight hcommonRemainder

/-- The degree-sized public candidate is total and maximal on primitive inputs. -/
theorem candidate?_exists_certificate (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (left right : CPolynomial R)
    (hleftPrimitive : left.toPoly.IsPrimitive)
    (hrightPrimitive : right = 0 ∨ right.toPoly.IsPrimitive) :
    ∃ result, NormalizedPseudoRemainder.candidate? gcd divide left right = some result ∧
      CandidateCertificate left right result := by
  apply candidateAux?_exists_certificate gcd divide gcdLaws divideLaws
    (degreeMeasure right + 1) left right hleftPrimitive hrightPrimitive
  omega

/-- Any successful degree-sized result on primitive inputs carries the maximality certificate. -/
theorem candidate?_certificate (gcd : R → R → R)
    (divide : R → R → Option R) (gcdLaws : GcdLaws gcd)
    (divideLaws : DivideLaws divide) (left right result : CPolynomial R)
    (hleftPrimitive : left.toPoly.IsPrimitive)
    (hrightPrimitive : right = 0 ∨ right.toPoly.IsPrimitive)
    (hresult : NormalizedPseudoRemainder.candidate? gcd divide left right = some result) :
    CandidateCertificate left right result := by
  obtain ⟨candidate, hcandidate, certificate⟩ := candidate?_exists_certificate
    gcd divide gcdLaws divideLaws left right hleftPrimitive hrightPrimitive
  rw [hresult] at hcandidate
  cases Option.some.inj hcandidate
  exact certificate

end Gauss

end CPoly.CMvPolynomial.BoundedGCD.GaussPreservation
