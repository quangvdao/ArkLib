/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.StoredField

/-!
# Canonical stored representatives of rational functions

The quotient used by `StoredField.Carrier` deliberately keeps the representative
hidden.  This file supplies a computable section of that quotient.  It cancels the
gcd computed by CompPoly's Euclidean algorithm and scales the remaining denominator
to be monic.  Its run-time definitions use only stored polynomial arithmetic and
`Quotient.lift`; the comparison with `RatFunc.num` and `RatFunc.denom` is confined to
the correctness proofs.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

namespace Fraction

omit [LawfulBEq F] in
/-- Extensionality of stored fractions. -/
@[ext] theorem ext' {a b : Fraction F} (hnum : a.num = b.num) (hden : a.den = b.den) : a = b := by
  cases a
  cases b
  simp_all

open scoped Classical in
private theorem gcdMonic_toPoly_eq_gcd (p q : CPolynomial F) :
    (gcdMonic p q).toPoly = GCDMonoid.gcd p.toPoly q.toPoly := by
  rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd, ← normalize_gcd p.toPoly q.toPoly]
  apply normalize_eq_normalize
  · exact dvd_gcd (EuclideanDomain.gcd_dvd_left p.toPoly q.toPoly)
      (EuclideanDomain.gcd_dvd_right p.toPoly q.toPoly)
  · exact EuclideanDomain.dvd_gcd (gcd_dvd_left p.toPoly q.toPoly)
      (gcd_dvd_right p.toPoly q.toPoly)

/-- Cancel the (unnormalized) Euclidean gcd and make the denominator monic. -/
def canonical (a : Fraction F) : Fraction F :=
  let g := CPolynomial.gcdMonic a.num a.den
  let n := a.num.div g
  let d := a.den.div g
  let c := d.leadingCoeff⁻¹
  ⟨c • n, c • d⟩

open scoped Classical in
/-- The stored numerator produced by `canonical` is Mathlib's canonical numerator. -/
theorem canonical_num_toPoly (a : Fraction F) (_ha : a.Valid) :
    a.canonical.num.toPoly = a.value.num := by
  unfold value
  rw [RatFunc.num_div]
  simp only [canonical, toPoly_smul, div_toPoly_eq_div, leadingCoeff_toPoly,
    gcdMonic_toPoly_eq_gcd, Polynomial.smul_eq_C_mul]

open scoped Classical in
/-- The stored denominator produced by `canonical` is Mathlib's canonical monic denominator. -/
theorem canonical_den_toPoly (a : Fraction F) (ha : a.Valid) :
    a.canonical.den.toPoly = a.value.denom := by
  unfold value
  rw [RatFunc.denom_div _ ha]
  simp only [canonical, toPoly_smul, div_toPoly_eq_div, leadingCoeff_toPoly,
    gcdMonic_toPoly_eq_gcd, Polynomial.smul_eq_C_mul]

/-- Canonicalization preserves the nonzero-denominator invariant. -/
theorem valid_canonical (a : Fraction F) (ha : a.Valid) : a.canonical.Valid := by
  rw [Valid, canonical_den_toPoly a ha]
  exact RatFunc.denom_ne_zero _

/-- Canonicalization preserves the represented rational function. -/
theorem value_canonical (a : Fraction F) (ha : a.Valid) :
    a.canonical.value = a.value := by
  rw [value, canonical_num_toPoly a ha, canonical_den_toPoly a ha,
    RatFunc.num_div_denom]

/-- The canonical stored denominator is monic. -/
theorem canonical_den_monic (a : Fraction F) (ha : a.Valid) :
    a.canonical.den.monic := by
  rw [monic_toPoly_iff, canonical_den_toPoly a ha]
  exact RatFunc.monic_denom _

/-- The canonical stored numerator and denominator are coprime. -/
theorem canonical_isCoprime (a : Fraction F) (ha : a.Valid) :
    IsCoprime a.canonical.num.toPoly a.canonical.den.toPoly := by
  rw [canonical_num_toPoly a ha, canonical_den_toPoly a ha]
  exact RatFunc.isCoprime_num_denom _

/-- Zero has the unique conventional representative `0 / 1`. -/
theorem canonical_eq_zero_iff (a : Fraction F) (ha : a.Valid) :
    a.canonical = Fraction.ofPolynomial 0 ↔ a.value = 0 := by
  constructor
  · intro h
    rw [← value_canonical a ha, h, Fraction.value_ofPolynomial, toPoly_zero, map_zero]
  · intro h
    apply Fraction.ext'
    · apply toPolyLinearEquiv.injective
      simp only [toPolyLinearEquiv_apply]
      rw [canonical_num_toPoly a ha, h, RatFunc.num_zero, Fraction.ofPolynomial, toPoly_zero]
    · apply toPolyLinearEquiv.injective
      simp only [toPolyLinearEquiv_apply]
      rw [canonical_den_toPoly a ha, h, RatFunc.denom_zero, Fraction.ofPolynomial, toPoly_one]

end Fraction

/-- A fraction certified to use the unique coprime, monic-denominator representation. -/
structure CanonicalRepresentative (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The executable stored fraction. -/
  fraction : Fraction F
  /-- Its denominator is nonzero. -/
  valid : fraction.Valid
  /-- Its numerator agrees with the canonical mathematical numerator. -/
  num_eq : fraction.num.toPoly = fraction.value.num
  /-- Its denominator agrees with the canonical mathematical denominator. -/
  den_eq : fraction.den.toPoly = fraction.value.denom

namespace CanonicalRepresentative

/-- Canonicalize a valid stored fraction. -/
def ofFraction (a : Fraction F) (ha : a.Valid) : CanonicalRepresentative F :=
  ⟨a.canonical, Fraction.valid_canonical a ha,
    by rw [Fraction.value_canonical a ha]; exact Fraction.canonical_num_toPoly a ha,
    by rw [Fraction.value_canonical a ha]; exact Fraction.canonical_den_toPoly a ha⟩

/-- Numerator projection used by denominator clearing. -/
def numerator (a : CanonicalRepresentative F) : CPolynomial F := a.fraction.num

/-- Denominator projection used by denominator clearing. -/
def denominator (a : CanonicalRepresentative F) : CPolynomial F := a.fraction.den

/-- Mathematical interpretation of the stored representative. -/
noncomputable def value (a : CanonicalRepresentative F) : RatFunc F := a.fraction.value

theorem denominator_ne_zero (a : CanonicalRepresentative F) : a.denominator.toPoly ≠ 0 :=
  a.valid

theorem denominator_monic (a : CanonicalRepresentative F) : a.denominator.monic := by
  rw [monic_toPoly_iff]
  change a.fraction.den.toPoly.Monic
  rw [a.den_eq]
  exact RatFunc.monic_denom _

theorem isCoprime (a : CanonicalRepresentative F) :
    IsCoprime a.numerator.toPoly a.denominator.toPoly := by
  rw [numerator, denominator, a.num_eq, a.den_eq]
  exact RatFunc.isCoprime_num_denom _

theorem value_eq_div (a : CanonicalRepresentative F) :
    a.value = algebraMap (Polynomial F) (RatFunc F) a.numerator.toPoly /
      algebraMap (Polynomial F) (RatFunc F) a.denominator.toPoly := rfl

/-- Canonical valid fractions with equal values are structurally equal. -/
theorem eq_of_value_eq (a b : CanonicalRepresentative F) (h : a.value = b.value) : a = b := by
  change a.fraction.value = b.fraction.value at h
  have hnum : a.fraction.num = b.fraction.num := by
    apply toPolyLinearEquiv.injective
    rw [toPolyLinearEquiv_apply, toPolyLinearEquiv_apply]
    rw [a.num_eq, b.num_eq, h]
  have hden : a.fraction.den = b.fraction.den := by
    apply toPolyLinearEquiv.injective
    rw [toPolyLinearEquiv_apply, toPolyLinearEquiv_apply]
    rw [a.den_eq, b.den_eq, h]
  have hfrac : a.fraction = b.fraction := Fraction.ext' hnum hden
  cases a
  cases b
  simp_all

end CanonicalRepresentative

namespace StoredField

/-- A computable canonical lift out of `Carrier`.  This is a quotient lift whose
representative-independence follows from canonical-fraction uniqueness. -/
def canonical : Carrier F → CanonicalRepresentative F :=
  Quotient.lift (fun a => CanonicalRepresentative.ofFraction a.val a.property) (by
    intro a b hab
    apply CanonicalRepresentative.eq_of_value_eq
    change a.val.canonical.value = b.val.canonical.value
    rw [Fraction.value_canonical a.val a.property, Fraction.value_canonical b.val b.property]
    exact (related_iff_value a b).mp hab)

/-- Canonical numerator of a stored rational-function coefficient. -/
def numerator (a : Carrier F) : CPolynomial F := (canonical a).numerator

/-- Canonical monic denominator of a stored rational-function coefficient. -/
def denominator (a : Carrier F) : CPolynomial F := (canonical a).denominator

@[simp] theorem canonical_value (a : Carrier F) : (canonical a).value = StoredField.value a := by
  induction a using Quotient.inductionOn with
  | h a => exact Fraction.value_canonical a.val a.property

theorem denominator_ne_zero (a : Carrier F) : (denominator a).toPoly ≠ 0 :=
  (canonical a).denominator_ne_zero

theorem denominator_monic (a : Carrier F) : (denominator a).monic :=
  (canonical a).denominator_monic

theorem numerator_denominator_isCoprime (a : Carrier F) :
    IsCoprime (numerator a).toPoly (denominator a).toPoly :=
  (canonical a).isCoprime

theorem value_eq_num_div_den (a : Carrier F) :
    StoredField.value a = algebraMap (Polynomial F) (RatFunc F) (numerator a).toPoly /
      algebraMap (Polynomial F) (RatFunc F) (denominator a).toPoly := by
  rw [← canonical_value a, CanonicalRepresentative.value_eq_div]
  rfl

@[simp] theorem numerator_zero : numerator (0 : Carrier F) = 0 := by
  apply toPolyLinearEquiv.injective
  simp only [toPolyLinearEquiv_apply]
  change (canonical (0 : Carrier F)).fraction.num.toPoly = (0 : CPolynomial F).toPoly
  rw [(canonical (0 : Carrier F)).num_eq]
  change (canonical (0 : Carrier F)).value.num = (0 : CPolynomial F).toPoly
  rw [canonical_value, value_zero, RatFunc.num_zero,
    toPoly_zero]

@[simp] theorem denominator_zero : denominator (0 : Carrier F) = 1 := by
  apply toPolyLinearEquiv.injective
  simp only [toPolyLinearEquiv_apply]
  change (canonical (0 : Carrier F)).fraction.den.toPoly = (1 : CPolynomial F).toPoly
  rw [(canonical (0 : Carrier F)).den_eq]
  change (canonical (0 : Carrier F)).value.denom = (1 : CPolynomial F).toPoly
  rw [canonical_value, value_zero, RatFunc.denom_zero,
    toPoly_one]

end StoredField

end Polynomial.FunctionFieldAlgorithms
