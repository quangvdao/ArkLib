/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.CoefficientNormalization

/-!
# Normalized pseudo-remainders

This module performs one pseudo-remainder computation and immediately removes its coefficient
content using a checked lower-dimensional normalization operation. The resulting reconstruction
certificate records both the pseudo-division scale and the removed content.

The bounded sequence below deliberately returns `none` when it exhausts its budget. Successful
results are executable candidates only; no maximal-gcd property is claimed here.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.NormalizedPseudoRemainder

open CompPoly
open CPoly.CMvPolynomial.BoundedGCD
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]

/-- The checked result of removing coefficient content from a terminal pseudo-remainder. -/
structure Data (R : Type*) [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] where
  scale : R
  quotient : CPolynomial R
  content : R
  remainder : CPolynomial R

/-- Compute a terminal pseudo-remainder and immediately normalize its coefficient content.
The zero remainder is represented canonically with content one. -/
def compute? (gcd : R → R → R) (divide : R → R → Option R)
    (dividend divisor : CPolynomial R) : Option (Data R) :=
  let raw := pseudoDivide dividend divisor
  if raw.remainder = 0 then
    some ⟨raw.scale, raw.quotient, 1, 0⟩
  else
    match normalize? gcd divide raw.remainder with
    | none => none
    | some normalized =>
        some ⟨raw.scale, raw.quotient, normalized.content, normalized.primitive⟩

/-- Successful normalization reconstructs the raw pseudo-remainder. -/
theorem compute?_raw_remainder_identity (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) :
    CPolynomial.C data.content * data.remainder =
      (pseudoDivide dividend divisor).remainder := by
  unfold compute? at h
  dsimp only at h
  by_cases hz : (pseudoDivide dividend divisor).remainder = 0
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst data
    simpa using hz.symm
  · simp only [hz, ↓reduceIte] at h
    cases hn : normalize? gcd divide (pseudoDivide dividend divisor).remainder with
    | none => simp [hn] at h
    | some normalized =>
      simp only [hn, Option.some.injEq] at h
      subst data
      exact normalize?_identity gcd divide _ normalized hn

/-- Successful normalization retains the pseudo-division scale. -/
theorem compute?_scale_eq (gcd : R → R → R) (divide : R → R → Option R)
    (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) :
    data.scale = (pseudoDivide dividend divisor).scale := by
  unfold compute? at h
  dsimp only at h
  by_cases hz : (pseudoDivide dividend divisor).remainder = 0
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst data
    rfl
  · simp only [hz, ↓reduceIte] at h
    cases hn : normalize? gcd divide (pseudoDivide dividend divisor).remainder with
    | none => simp [hn] at h
    | some normalized =>
      simp only [hn, Option.some.injEq] at h
      subst data
      rfl

/-- Successful normalization retains the pseudo-division quotient. -/
theorem compute?_quotient_eq (gcd : R → R → R) (divide : R → R → Option R)
    (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) :
    data.quotient = (pseudoDivide dividend divisor).quotient := by
  unfold compute? at h
  dsimp only at h
  by_cases hz : (pseudoDivide dividend divisor).remainder = 0
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst data
    rfl
  · simp only [hz, ↓reduceIte] at h
    cases hn : normalize? gcd divide (pseudoDivide dividend divisor).remainder with
    | none => simp [hn] at h
    | some normalized =>
      simp only [hn, Option.some.injEq] at h
      subst data
      rfl

/-- The normalized pseudo-remainder retains the fraction-free reconstruction identity. -/
theorem compute?_certifies (gcd : R → R → R) (divide : R → R → Option R)
    (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) :
    CPolynomial.C data.scale * dividend =
      data.quotient * divisor + CPolynomial.C data.content * data.remainder := by
  have hpseudo := pseudoDivide_certifies dividend divisor
  unfold PseudoDivisionState.Certifies at hpseudo
  rw [compute?_scale_eq gcd divide dividend divisor data h,
    compute?_quotient_eq gcd divide dividend divisor data h]
  rw [compute?_raw_remainder_identity gcd divide dividend divisor data h]
  exact hpseudo

/-- Every common divisor of the pseudo-division inputs divides the removed-content product. -/
theorem compute?_common_divisor_preserved (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor common : CPolynomial R)
    (data : Data R) (h : compute? gcd divide dividend divisor = some data)
    (hdividend : common ∣ dividend) (hdivisor : common ∣ divisor) :
    common ∣ CPolynomial.C data.content * data.remainder := by
  obtain ⟨dividendQuotient, rfl⟩ := hdividend
  obtain ⟨divisorQuotient, rfl⟩ := hdivisor
  refine ⟨CPolynomial.C data.scale * dividendQuotient -
    data.quotient * divisorQuotient, ?_⟩
  have hidentity := compute?_certifies gcd divide
    (common * dividendQuotient) (common * divisorQuotient) data h
  calc
    CPolynomial.C data.content * data.remainder =
        CPolynomial.C data.scale * (common * dividendQuotient) -
          data.quotient * (common * divisorQuotient) := by rw [hidentity]; ring
    _ = common * (CPolynomial.C data.scale * dividendQuotient -
          data.quotient * divisorQuotient) := by ring

/-- A successful normalized pseudo-remainder is zero exactly when the raw remainder is zero. -/
theorem compute?_remainder_eq_zero_iff (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) :
    data.remainder = 0 ↔ (pseudoDivide dividend divisor).remainder = 0 := by
  constructor
  · intro hz
    rw [← compute?_raw_remainder_identity gcd divide dividend divisor data h, hz, mul_zero]
  · intro hz
    unfold compute? at h
    dsimp only at h
    simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst data
    rfl

/-- Removing nonzero coefficient content preserves the degree of a nonzero raw remainder. -/
theorem compute?_natDegree_eq (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data)
    (hraw : (pseudoDivide dividend divisor).remainder ≠ 0) :
    data.remainder.natDegree = (pseudoDivide dividend divisor).remainder.natDegree := by
  have hidentity := compute?_raw_remainder_identity gcd divide dividend divisor data h
  have hcontent : data.content ≠ 0 := by
    intro hz
    apply hraw
    rw [← hidentity, hz]
    simp
  have hremainder : data.remainder ≠ 0 := by
    intro hz
    exact hraw ((compute?_remainder_eq_zero_iff gcd divide dividend divisor data h).mp hz)
  rw [← hidentity]
  rw [CPolynomial.natDegree_toPoly]
  rw [CPolynomial.natDegree_toPoly]
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C, Polynomial.natDegree_C_mul]
  exact hcontent

/-- A successful normalized result is terminal for pseudo-division by a nonzero divisor. -/
theorem compute?_terminal (gcd : R → R → R) (divide : R → R → Option R)
    (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) (hdivisor : divisor ≠ 0) :
    data.remainder = 0 ∨ data.remainder.natDegree < divisor.natDegree := by
  rcases pseudoDivide_terminal dividend divisor hdivisor with hzero | hdegree
  · exact Or.inl ((compute?_remainder_eq_zero_iff gcd divide dividend divisor data h).mpr hzero)
  · by_cases hzero : (pseudoDivide dividend divisor).remainder = 0
    · exact Or.inl ((compute?_remainder_eq_zero_iff gcd divide dividend divisor data h).mpr hzero)
    · right
      rw [compute?_natDegree_eq gcd divide dividend divisor data h hzero]
      exact hdegree

/-- A successful normalized result strictly lowers the zero-aware degree measure. -/
theorem compute?_degreeMeasure_lt (gcd : R → R → R)
    (divide : R → R → Option R) (dividend divisor : CPolynomial R) (data : Data R)
    (h : compute? gcd divide dividend divisor = some data) (hdivisor : divisor ≠ 0) :
    degreeMeasure data.remainder < degreeMeasure divisor := by
  rcases compute?_terminal gcd divide dividend divisor data h hdivisor with hzero | hdegree
  · simp [degreeMeasure, hzero, hdivisor]
  · by_cases hremainder : data.remainder = 0
    · simp [degreeMeasure, hremainder, hdivisor]
    · simp [degreeMeasure, hremainder, hdivisor, hdegree]

/-- A bounded normalized pseudo-remainder sequence. Failure records either normalization failure or
budget exhaustion; it is not silently converted into a gcd candidate. -/
def candidateAux? (gcd : R → R → R) (divide : R → R → Option R) :
    ℕ → CPolynomial R → CPolynomial R → Option (CPolynomial R)
  | 0, left, right => if right = 0 then some left else none
  | fuel + 1, left, right =>
      if right = 0 then some left
      else
        match compute? gcd divide left right with
        | none => none
        | some step => candidateAux? gcd divide fuel right step.remainder

/-- Degree-sized executable candidate from the normalized pseudo-remainder sequence. -/
def candidate? (gcd : R → R → R) (divide : R → R → Option R)
    (left right : CPolynomial R) : Option (CPolynomial R) :=
  candidateAux? gcd divide (degreeMeasure right + 1) left right

end CPoly.CMvPolynomial.BoundedGCD.NormalizedPseudoRemainder
