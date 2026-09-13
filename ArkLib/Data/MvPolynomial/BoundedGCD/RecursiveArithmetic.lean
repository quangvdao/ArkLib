/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.FunctionFieldBridge
public import ArkLib.Data.MvPolynomial.CheckedExactDivision
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.ToPoly.Core

/-!
# Recursive arithmetic for stored multivariate polynomials

This module closes the executable coefficient-arithmetic recursion used by the
bounded content/primitive gcd.  Exact division first runs the flat checked
leading-term divider.  If that fast path exhausts its fuel, a nested
fraction-free division uses pseudo-division in the final variable and the
already constructed exact divider on its coefficient ring.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.RecursiveArithmetic

open CompPoly
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization

variable {E : Type*} [Field E] [DecidableEq E]

section CoefficientDivision

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [IsDomain R]

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

omit [DecidableEq R] in
/-- Successful coefficientwise exact division reconstructs the input polynomial. -/
theorem divideCoefficients?_identity (divide : R → R → Option R)
    (laws : DivideLaws divide) (content : R) (p quotient : CPolynomial R)
    (hdivide : divideCoefficients? divide content p = some quotient) :
    CPolynomial.C content * quotient = p := by
  unfold divideCoefficients? at hdivide
  cases hlist : divideList? divide content p.val.toList with
  | none => simp [hlist] at hdivide
  | some quotients =>
    simp only [hlist, Option.map_some, Option.some.injEq] at hdivide
    subst quotient
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]
    apply Polynomial.ext
    intro index
    rw [Polynomial.coeff_C_mul, ← CPolynomial.coeff_toPoly,
      CPolynomial.coeff_ofArray, array_getD_toList, List.toList_toArray,
      ← CPolynomial.coeff_toPoly]
    have hidentity := divideList?_identity divide laws content p.val.toList
      quotients hlist
    rw [coeff_eq_toList_getD, hidentity]
    simpa using (List.getD_map quotients 0 (n := index)
      (fun item => content * item)).symm

omit [DecidableEq R] [IsDomain R] in
/-- If a nonzero scalar divides every coefficient, executable coefficientwise division succeeds. -/
theorem divideCoefficients?_exists (divide : R → R → Option R)
    (laws : DivideLaws divide) (content : R) (hcontent : content ≠ 0)
    (p : CPolynomial R) (hcoefficients : ∀ coefficient ∈ p.val.toList,
      content ∣ coefficient) :
    ∃ quotient, divideCoefficients? divide content p = some quotient := by
  obtain ⟨quotients, hquotients⟩ := divideList?_exists divide laws content hcontent
    p.val.toList hcoefficients
  exact ⟨CPolynomial.ofArray quotients.toArray, by
    simp [divideCoefficients?, hquotients]⟩

omit [DecidableEq R] [IsDomain R] in
private theorem coefficients_dvd_of_eq_C_mul {content : R}
    {expected p : CPolynomial R} (hp : p = CPolynomial.C content * expected) :
    ∀ coefficient ∈ p.val.toList, content ∣ coefficient := by
  intro coefficient hcoefficient
  obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hcoefficient
  refine ⟨expected.coeff index, ?_⟩
  have hcoeff : p.toPoly.coeff index = coefficient := by
    rw [← CPolynomial.coeff_toPoly, coeff_eq_toList_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex,
      hget, Option.getD_some]
  rw [hp, CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
    Polynomial.coeff_C_mul, ← CPolynomial.coeff_toPoly] at hcoeff
  exact hcoeff.symm

end CoefficientDivision

section NestedDivision

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [IsDomain R]

/-- Fraction-free exact division in one polynomial variable. -/
def pseudoExactQuotient? (coefficientDivide : R → R → Option R)
    (dividend divisor : CPolynomial R) : Option (CPolynomial R) :=
  if divisor = 0 then none
  else
    let state := pseudoDivide dividend divisor
    if state.remainder = 0 then
      divideCoefficients? coefficientDivide state.scale state.quotient
    else none

omit [DecidableEq R] [IsDomain R] in
private theorem C_ne_zero {a : R} (ha : a ≠ 0) :
    (CPolynomial.C a : CPolynomial R) ≠ 0 := by
  intro h
  have h' := congrArg CPolynomial.toPoly h
  rw [CPolynomial.toPoly_C, CPolynomial.toPoly_zero] at h'
  have hcoeff := congrArg (fun p : Polynomial R => p.coeff 0) h'
  exact ha (by simpa using hcoeff)

omit [DecidableEq R] in
private theorem toPoly_dvd {p q : CPolynomial R} (h : p ∣ q) :
    p.toPoly ∣ q.toPoly := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a.toPoly, CPolynomial.toPoly_mul _ _⟩

/-- Exact divisibility forces the terminal pseudo-remainder to vanish. -/
theorem pseudoDivide_remainder_eq_zero_of_dvd (dividend divisor : CPolynomial R)
    (hdivisor : divisor ≠ 0) (hdivides : divisor ∣ dividend) :
    (pseudoDivide dividend divisor).remainder = 0 := by
  by_cases hzero : (pseudoDivide dividend divisor).remainder = 0
  · exact hzero
  · exfalso
    have hterminal := pseudoDivide_terminal dividend divisor hdivisor
    rcases hterminal with hzero' | hdegree
    · exact hzero hzero'
    obtain ⟨expected, hexpected⟩ := hdivides
    have hcert := pseudoDivide_certifies dividend divisor
    have hdvdRemainder : divisor ∣ (pseudoDivide dividend divisor).remainder := by
      refine ⟨CPolynomial.C (pseudoDivide dividend divisor).scale * expected -
        (pseudoDivide dividend divisor).quotient, ?_⟩
      unfold PseudoDivisionState.Certifies at hcert
      calc
        (pseudoDivide dividend divisor).remainder =
            CPolynomial.C (pseudoDivide dividend divisor).scale * dividend -
              (pseudoDivide dividend divisor).quotient * divisor := by
                linear_combination -hcert
        _ = CPolynomial.C (pseudoDivide dividend divisor).scale *
              (divisor * expected) -
              (pseudoDivide dividend divisor).quotient * divisor := by rw [hexpected]
        _ = divisor * (CPolynomial.C (pseudoDivide dividend divisor).scale * expected -
              (pseudoDivide dividend divisor).quotient) := by ring
    have hdegree' := Polynomial.natDegree_le_of_dvd (toPoly_dvd hdvdRemainder)
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hzero)
    rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly] at hdegree'
    omega

/-- The nested fraction-free divider is sound. -/
theorem pseudoExactQuotient?_identity (coefficientDivide : R → R → Option R)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    {dividend divisor quotient : CPolynomial R}
    (h : pseudoExactQuotient? coefficientDivide dividend divisor = some quotient) :
    quotient * divisor = dividend := by
  unfold pseudoExactQuotient? at h
  by_cases hdivisor : divisor = 0
  · simp [hdivisor] at h
  simp only [hdivisor, ↓reduceIte] at h
  let state := pseudoDivide dividend divisor
  change (if state.remainder = 0 then
      divideCoefficients? coefficientDivide state.scale state.quotient else none) =
    some quotient at h
  by_cases hremainder : state.remainder = 0
  · simp only [hremainder, ↓reduceIte] at h
    have hquotient := divideCoefficients?_identity coefficientDivide
      coefficientDivideLaws state.scale state.quotient quotient h
    have hcert := pseudoDivide_certifies dividend divisor
    change PseudoDivisionState.Certifies dividend divisor state at hcert
    unfold PseudoDivisionState.Certifies at hcert
    rw [hremainder, add_zero, ← hquotient] at hcert
    have hscaled : CPolynomial.C state.scale * (quotient * divisor) =
        CPolynomial.C state.scale * dividend := by
      calc
      CPolynomial.C state.scale * (quotient * divisor) =
          (CPolynomial.C state.scale * quotient) * divisor := by ring
      _ = CPolynomial.C state.scale * dividend := hcert.symm
    apply CPolynomial.toPoly_injective
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr <|
      GaussPreservation.pseudoDivide_scale_ne_zero dividend divisor hdivisor)
    simpa [CPolynomial.toPoly_mul, CPolynomial.toPoly_C] using
      congrArg CPolynomial.toPoly hscaled
  · simp [hremainder] at h

/-- The nested fraction-free divider succeeds on every exact nonzero divisor. -/
theorem pseudoExactQuotient?_complete (coefficientDivide : R → R → Option R)
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    {dividend divisor : CPolynomial R} (hdivisor : divisor ≠ 0)
    (hdivides : divisor ∣ dividend) :
    ∃ quotient, pseudoExactQuotient? coefficientDivide dividend divisor = some quotient := by
  let state := pseudoDivide dividend divisor
  have hremainder : state.remainder = 0 :=
    pseudoDivide_remainder_eq_zero_of_dvd dividend divisor hdivisor hdivides
  obtain ⟨expected, hexpected⟩ := hdivides
  have hcert := pseudoDivide_certifies dividend divisor
  change PseudoDivisionState.Certifies dividend divisor state at hcert
  unfold PseudoDivisionState.Certifies at hcert
  rw [hremainder, add_zero, hexpected] at hcert
  have hquotient : state.quotient = CPolynomial.C state.scale * expected := by
    apply CPolynomial.toPoly_injective
    apply mul_right_cancel₀ ((CPolynomial.toPoly_eq_zero_iff divisor).not.mpr hdivisor)
    rw [← CPolynomial.toPoly_mul, ← CPolynomial.toPoly_mul]
    apply congrArg CPolynomial.toPoly
    calc
      state.quotient * divisor =
          CPolynomial.C state.scale * (divisor * expected) := hcert.symm
      _ = (CPolynomial.C state.scale * expected) * divisor := by ring
  have hscale : state.scale ≠ 0 :=
    GaussPreservation.pseudoDivide_scale_ne_zero dividend divisor hdivisor
  obtain ⟨quotient, hdivide⟩ := divideCoefficients?_exists coefficientDivide
    coefficientDivideLaws state.scale hscale state.quotient
      (coefficients_dvd_of_eq_C_mul hquotient)
  exact ⟨quotient, by
    simp [pseudoExactQuotient?, hdivisor, state, hremainder, hdivide]⟩

theorem pseudoExactQuotient?_laws (coefficientDivide : R → R → Option R)
    (coefficientDivideLaws : DivideLaws coefficientDivide) :
    DivideLaws (pseudoExactQuotient? coefficientDivide) :=
  ⟨fun h => pseudoExactQuotient?_identity coefficientDivide coefficientDivideLaws h,
    fun hdivisor hdivides => pseudoExactQuotient?_complete coefficientDivide
      coefficientDivideLaws hdivisor hdivides⟩

end NestedDivision

section Successor

variable {r : ℕ}

/-- Exact division in one more variable.  The existing flat leading-term divider is the fast
path; certified fraction-free division in the last variable is the total fallback. -/
def successorDivide
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (dividend divisor : CMvPolynomial (r + 1) E) :
    Option (CMvPolynomial (r + 1) E) :=
  match CPoly.CMvPolynomial.CheckedExactDivision.exactQuotient? dividend divisor with
  | some quotient => some quotient
  | none =>
      (pseudoExactQuotient? coefficientDivide
        (CPoly.TaylorReconstruction.splitLast dividend)
        (CPoly.TaylorReconstruction.splitLast divisor)).map
          CPoly.TaylorReconstruction.flattenLast

/-- Every returned successor quotient reconstructs its dividend. -/
theorem successorDivide_identity
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    {dividend divisor quotient : CMvPolynomial (r + 1) E}
    (h : successorDivide coefficientDivide dividend divisor = some quotient) :
    quotient * divisor = dividend := by
  unfold successorDivide at h
  cases hfast : CPoly.CMvPolynomial.CheckedExactDivision.exactQuotient?
      dividend divisor with
  | some fastQuotient =>
      simp only [hfast, Option.some.injEq] at h
      subst quotient
      exact CPoly.CMvPolynomial.CheckedExactDivision.exactQuotient?_identity
        dividend divisor fastQuotient hfast
  | none =>
      simp only [hfast] at h
      obtain ⟨nestedQuotient, hnested, rfl⟩ := Option.map_eq_some_iff.mp h
      have hidentity := pseudoExactQuotient?_identity coefficientDivide
        coefficientDivideLaws hnested
      have hflatten := congrArg
        (CPoly.TaylorReconstruction.flattenLast (r := r) (E := E)) hidentity
      simpa using hflatten

/-- Exact divisibility makes the successor divider succeed. -/
theorem successorDivide_complete
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (coefficientDivideLaws : DivideLaws coefficientDivide)
    {dividend divisor : CMvPolynomial (r + 1) E} (hdivisor : divisor ≠ 0)
    (hdivides : divisor ∣ dividend) :
    ∃ quotient, successorDivide coefficientDivide dividend divisor = some quotient := by
  cases hfast : CPoly.CMvPolynomial.CheckedExactDivision.exactQuotient?
      dividend divisor with
  | some quotient => exact ⟨quotient, by simp [successorDivide, hfast]⟩
  | none =>
      have hsplitDivisor : CPoly.TaylorReconstruction.splitLast divisor ≠ 0 := by
        intro hzero
        apply hdivisor
        rw [← CPoly.TaylorReconstruction.flattenLast_splitLast divisor, hzero]
        simp
      have hsplitDvd : CPoly.TaylorReconstruction.splitLast divisor ∣
          CPoly.TaylorReconstruction.splitLast dividend :=
        map_dvd CPoly.TaylorReconstruction.splitLast hdivides
      obtain ⟨nestedQuotient, hnested⟩ := pseudoExactQuotient?_complete
        coefficientDivide coefficientDivideLaws hsplitDivisor hsplitDvd
      exact ⟨CPoly.TaylorReconstruction.flattenLast nestedQuotient, by
        simp [successorDivide, hfast, hnested]⟩

theorem successorDivide_laws
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (coefficientDivideLaws : DivideLaws coefficientDivide) :
    DivideLaws (successorDivide coefficientDivide) :=
  ⟨fun h => successorDivide_identity coefficientDivide coefficientDivideLaws h,
    fun hdivisor hdivides => successorDivide_complete coefficientDivide
      coefficientDivideLaws hdivisor hdivides⟩

/-- Content/primitive gcd in one more variable, flattened back to the stored representation. -/
def successorGcd
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (left right : CMvPolynomial (r + 1) E) : CMvPolynomial (r + 1) E :=
  match ContentPrimitiveGCD.compute? coefficientGcd coefficientDivide
      (CPoly.TaylorReconstruction.splitLast left)
      (CPoly.TaylorReconstruction.splitLast right) with
  | some result => CPoly.TaylorReconstruction.flattenLast result
  | none => 0

/-- The recursively assembled successor gcd has the universal gcd property. -/
theorem successorGcd_laws
    (coefficientGcd : CMvPolynomial r E → CMvPolynomial r E → CMvPolynomial r E)
    (coefficientDivide : CMvPolynomial r E → CMvPolynomial r E →
      Option (CMvPolynomial r E))
    (coefficientGcdLaws : GcdLaws coefficientGcd)
    (coefficientDivideLaws : DivideLaws coefficientDivide) :
    GcdLaws (successorGcd coefficientGcd coefficientDivide) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right
    obtain ⟨result, hresult, certificate⟩ :=
      ContentPrimitiveGCD.compute?_exists_certificate coefficientGcd coefficientDivide
        coefficientGcdLaws coefficientDivideLaws
        (CPoly.TaylorReconstruction.splitLast left)
        (CPoly.TaylorReconstruction.splitLast right)
    rw [successorGcd, hresult]
    simpa using map_dvd CPoly.TaylorReconstruction.flattenLast certificate.dvd_left
  · intro left right
    obtain ⟨result, hresult, certificate⟩ :=
      ContentPrimitiveGCD.compute?_exists_certificate coefficientGcd coefficientDivide
        coefficientGcdLaws coefficientDivideLaws
        (CPoly.TaylorReconstruction.splitLast left)
        (CPoly.TaylorReconstruction.splitLast right)
    rw [successorGcd, hresult]
    simpa using map_dvd CPoly.TaylorReconstruction.flattenLast certificate.dvd_right
  · intro common left right hleft hright
    obtain ⟨result, hresult, certificate⟩ :=
      ContentPrimitiveGCD.compute?_exists_certificate coefficientGcd coefficientDivide
        coefficientGcdLaws coefficientDivideLaws
        (CPoly.TaylorReconstruction.splitLast left)
        (CPoly.TaylorReconstruction.splitLast right)
    rw [successorGcd, hresult]
    have hcommon := certificate.greatest
      (CPoly.TaylorReconstruction.splitLast common)
      (map_dvd CPoly.TaylorReconstruction.splitLast hleft)
      (map_dvd CPoly.TaylorReconstruction.splitLast hright)
    simpa using map_dvd CPoly.TaylorReconstruction.flattenLast hcommon

end Successor

/-- The unique scalar coefficient of a zero-variable stored polynomial. -/
def scalarCoefficient (p : CMvPolynomial 0 E) : E :=
  p.coeff (CMvMonomial.ofFinsupp 0)

theorem eq_C_scalarCoefficient (p : CMvPolynomial 0 E) :
    p = CMvPolynomial.C (scalarCoefficient p) := by
  apply eq_iff_fromCMvPolynomial.mpr
  rw [MvPolynomial.eq_C_of_isEmpty (fromCMvPolynomial p),
    CMvPolynomial.fromCMvPolynomial_C]
  congr 1

@[simp] theorem scalarCoefficient_C (a : E) :
    scalarCoefficient (CMvPolynomial.C a : CMvPolynomial 0 E) = a := by
  rw [scalarCoefficient, ← CPoly.coeff_eq]
  simp [CMvPolynomial.fromCMvPolynomial_C]

/-- Field gcd on the coefficient ring with no variables. -/
def scalarGcd (left right : CMvPolynomial 0 E) : CMvPolynomial 0 E :=
  if left = 0 then right else if right = 0 then left else 1

/-- Checked scalar division at the base of the recursion. -/
def scalarDivide (dividend divisor : CMvPolynomial 0 E) : Option (CMvPolynomial 0 E) :=
  if divisor = 0 then none
  else some (CMvPolynomial.C (scalarCoefficient dividend / scalarCoefficient divisor))

private theorem scalarCoefficient_ne_zero {p : CMvPolynomial 0 E} (hp : p ≠ 0) :
    scalarCoefficient p ≠ 0 := by
  intro h
  apply hp
  rw [eq_C_scalarCoefficient p, h]
  rfl

theorem scalarDivide_identity {dividend divisor quotient : CMvPolynomial 0 E}
    (h : scalarDivide dividend divisor = some quotient) :
    quotient * divisor = dividend := by
  unfold scalarDivide at h
  by_cases hd : divisor = 0
  · simp [hd] at h
  simp only [hd, ↓reduceIte, Option.some.injEq] at h
  subst quotient
  rw [eq_C_scalarCoefficient dividend, eq_C_scalarCoefficient divisor]
  apply eq_iff_fromCMvPolynomial.mpr
  simp only [scalarCoefficient_C]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C,
    CMvPolynomial.fromCMvPolynomial_C, CMvPolynomial.fromCMvPolynomial_C,
    ← MvPolynomial.C_mul]
  congr 1
  exact div_mul_cancel₀ _ (scalarCoefficient_ne_zero hd)

theorem scalarDivide_laws : DivideLaws (scalarDivide (E := E)) := by
  refine ⟨fun h => scalarDivide_identity h, ?_⟩
  intro dividend divisor hd hdivides
  refine ⟨CMvPolynomial.C
    (scalarCoefficient dividend / scalarCoefficient divisor), ?_⟩
  simp [scalarDivide, hd]

private theorem dvd_one_of_ne_zero_zeroVariables {p : CMvPolynomial 0 E}
    (hp : p ≠ 0) : p ∣ 1 := by
  rw [eq_C_scalarCoefficient p]
  refine ⟨CMvPolynomial.C (scalarCoefficient p)⁻¹, ?_⟩
  apply eq_iff_fromCMvPolynomial.mpr
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C,
    CMvPolynomial.fromCMvPolynomial_C, ← MvPolynomial.C_mul]
  simp [scalarCoefficient_ne_zero hp]

theorem scalarGcd_laws : GcdLaws (scalarGcd (E := E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right
    by_cases hl : left = 0
    · simp [scalarGcd, hl]
    · by_cases hr : right = 0
      · simp [scalarGcd, hl, hr]
      · simp [scalarGcd, hl, hr]
  · intro left right
    by_cases hl : left = 0
    · simp [scalarGcd, hl]
    · by_cases hr : right = 0
      · simp [scalarGcd, hl, hr]
      · simp [scalarGcd, hl, hr]
  · intro divisor left right hleft hright
    by_cases hl : left = 0
    · simpa [scalarGcd, hl] using hright
    · by_cases hr : right = 0
      · simpa [scalarGcd, hl, hr] using hleft
      · have hd : divisor ≠ 0 := by
          intro hz
          subst divisor
          exact hl (zero_dvd_iff.mp hleft)
        simpa [scalarGcd, hl, hr] using dvd_one_of_ne_zero_zeroVariables hd

/-- Executable gcd and exact-division operations at a fixed variable count. -/
structure Operations (n : ℕ) where
  gcd : CMvPolynomial n E → CMvPolynomial n E → CMvPolynomial n E
  divide : CMvPolynomial n E → CMvPolynomial n E → Option (CMvPolynomial n E)

/-- Structural recursion from scalar field arithmetic through content/primitive gcd and
fraction-free exact division. -/
def operations : (n : ℕ) → Operations (E := E) n
  | 0 => ⟨scalarGcd, scalarDivide⟩
  | n + 1 =>
      let lower := operations n
      ⟨successorGcd lower.gcd lower.divide, successorDivide lower.divide⟩

/-- Concrete recursive gcd for `n` stored variables. -/
def gcd (n : ℕ) : CMvPolynomial n E → CMvPolynomial n E → CMvPolynomial n E :=
  (operations n).gcd

/-- Concrete recursive exact divider for `n` stored variables. -/
def divide (n : ℕ) :
    CMvPolynomial n E → CMvPolynomial n E → Option (CMvPolynomial n E) :=
  (operations n).divide

/-- Both operations produced by the structural recursion satisfy their algebraic contracts. -/
theorem operations_laws (n : ℕ) :
    GcdLaws (operations (E := E) n).gcd ∧
      DivideLaws (operations (E := E) n).divide := by
  induction n with
  | zero => exact ⟨scalarGcd_laws, scalarDivide_laws⟩
  | succ n ih =>
      exact ⟨successorGcd_laws (operations n).gcd (operations n).divide ih.1 ih.2,
        successorDivide_laws (operations n).divide ih.2⟩

theorem gcd_laws (n : ℕ) : GcdLaws (gcd (E := E) n) :=
  (operations_laws n).1

theorem divide_laws (n : ℕ) : DivideLaws (divide (E := E) n) :=
  (operations_laws n).2

end CPoly.CMvPolynomial.BoundedGCD.RecursiveArithmetic
