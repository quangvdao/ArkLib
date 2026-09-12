/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CanonicalRepresentative
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.Euclidean
public import ArkLib.ToCompPoly.Bivariate.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
-- Representation-level coefficient bridges used only in correctness proofs.
import all CompPoly.Univariate.Basic

/-!
# Executable denominator clearing and primitive descent

For a stored polynomial over `F(X)`, `denominatorProduct` multiplies the
canonical denominator of every stored coefficient.  Each descended coefficient
is obtained by exact polynomial division of that product.  The main identity is
global in `F[X][Y]` before any specialization; in particular no fiber is removed
when one of the intermediate rational-function denominators vanishes.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms

open CompPoly CPolynomial StoredField

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

namespace ClearDenominators

/-- Product of all canonical coefficient denominators. -/
def denominatorProduct (p : CPolynomial (Carrier F)) : CPolynomial F :=
  ∏ i ∈ Finset.range p.val.size, StoredField.denominator (p.coeff i)

/-- The common denominator with one coefficient denominator divided out. -/
def complementaryProduct (p : CPolynomial (Carrier F)) (i : ℕ) : CPolynomial F :=
  (denominatorProduct p).div (StoredField.denominator (p.coeff i))

/-- A coefficient after multiplication by the common denominator. -/
def clearedCoefficient (p : CPolynomial (Carrier F)) (i : ℕ) : CPolynomial F :=
  StoredField.numerator (p.coeff i) * complementaryProduct p i

/-- Descend from `F(X)[Y]` to the global stored polynomial `F[X][Y]`. -/
def descended (p : CPolynomial (Carrier F)) : CPolynomial (CPolynomial F) :=
  CPolynomial.ofArray <| Array.ofFn fun i : Fin p.val.size => clearedCoefficient p i

/-- Embed a global stored bivariate polynomial into the stored function-field
coefficient ring.  This is the input shape used by function-field Euclid. -/
def embed (h : CBivariate F) : CPolynomial (Carrier F) :=
  CPolynomial.ofArray <| Array.ofFn fun i : Fin h.val.size =>
    StoredField.ofPolynomial (CPolynomial.coeff h i)

/-- Mathematical coefficient-field embedding of a global bivariate polynomial. -/
noncomputable def valueGlobal (h : CBivariate F) : Polynomial (RatFunc F) :=
  h.toPoly.map (algebraMap (Polynomial F) (RatFunc F))

/-- Primitive content, with a total zero convention. -/
def primitiveContent (h : CBivariate F) : CPolynomial F :=
  if h == 0 then 1 else CBivariate.yContent h

/-- Executable primitive descent, with zero mapped to zero. -/
def primitivePart (h : CBivariate F) : CPolynomial (CPolynomial F) :=
  if h == 0 then 0 else CBivariate.primitivePartY h

/-- A global `Y`-primitive certificate: every polynomial dividing all
`Y`-coefficients is a unit. -/
def IsYPrimitive (h : CBivariate F) : Prop :=
  ∀ d : Polynomial F, (∀ i, d ∣ (h.val.coeff i).toPoly) → IsUnit d

/-- The complete output of denominator clearing and primitive descent. -/
structure Result (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- Nonzero common denominator. -/
  scale : CPolynomial F
  /-- Global polynomial before content removal. -/
  global : CPolynomial (CPolynomial F)
  /-- Its totalized content. -/
  content : CPolynomial F
  /-- Its totalized primitive part. -/
  primitive : CPolynomial (CPolynomial F)
  /-- The common denominator is never zero. -/
  scale_ne_zero : scale.toPoly ≠ 0

private theorem toPoly_prod (s : Finset ℕ) (f : ℕ → CPolynomial F) :
    (∏ i ∈ s, f i).toPoly = ∏ i ∈ s, (f i).toPoly := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toPoly_one]
  | @insert i s hi ih => simp [hi, ih, toPoly_mul]

/-- Every canonical coefficient denominator occurs as a factor of the product. -/
theorem denominator_mul_complementaryProduct (p : CPolynomial (Carrier F)) {i : ℕ}
    (hi : i < p.val.size) :
    StoredField.denominator (p.coeff i) * complementaryProduct p i = denominatorProduct p := by
  apply toPolyLinearEquiv.injective
  simp only [toPolyLinearEquiv_apply, toPoly_mul, complementaryProduct, div_toPoly_eq_div]
  apply EuclideanDomain.mul_div_cancel'
  · exact StoredField.denominator_ne_zero _
  · refine ⟨(∏ j ∈ (Finset.range p.val.size).erase i,
        StoredField.denominator (p.coeff j)).toPoly, ?_⟩
    rw [← toPoly_mul]
    apply congrArg CPolynomial.toPoly
    exact (Finset.mul_prod_erase (Finset.range p.val.size)
      (fun j => StoredField.denominator (p.coeff j)) (Finset.mem_range.mpr hi)).symm

/-- The finite product of valid canonical denominators is nonzero. -/
theorem denominatorProduct_ne_zero (p : CPolynomial (Carrier F)) :
    (denominatorProduct p).toPoly ≠ 0 := by
  rw [denominatorProduct, toPoly_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => StoredField.denominator_ne_zero (p.coeff i)

/-- One descended coefficient satisfies a polynomial, rather than localized,
cross-multiplication identity. -/
theorem clearedCoefficient_mul_denominator (p : CPolynomial (Carrier F)) {i : ℕ}
    (hi : i < p.val.size) :
    (clearedCoefficient p i).toPoly * (StoredField.denominator (p.coeff i)).toPoly =
      (denominatorProduct p).toPoly * (StoredField.numerator (p.coeff i)).toPoly := by
  rw [clearedCoefficient, toPoly_mul, mul_assoc,
    mul_comm (complementaryProduct p i).toPoly,
    ← toPoly_mul, denominator_mul_complementaryProduct p hi]
  ac_rfl

theorem coeff_descended_of_lt (p : CPolynomial (Carrier F)) {i : ℕ}
    (hi : i < p.val.size) :
    CPolynomial.coeff (descended p) i = clearedCoefficient p i := by
  rw [descended, CPolynomial.coeff_ofArray]
  simp [Array.getD_eq_getD_getElem?, hi]

theorem coeff_descended_of_size_le (p : CPolynomial (Carrier F)) {i : ℕ}
    (hi : p.val.size ≤ i) :
    CPolynomial.coeff (descended p) i = 0 := by
  rw [descended, CPolynomial.coeff_ofArray]
  simp [Array.getD_eq_getD_getElem?, hi]

theorem coeff_embed_of_lt (h : CBivariate F) {i : ℕ} (hi : i < h.val.size) :
    (embed h).coeff i = StoredField.ofPolynomial (CPolynomial.coeff h i) := by
  rw [embed, CPolynomial.coeff_ofArray]
  simp [Array.getD_eq_getD_getElem?, hi]

theorem coeff_embed_of_size_le (h : CBivariate F) {i : ℕ} (hi : h.val.size ≤ i) :
    (embed h).coeff i = 0 := by
  rw [embed, CPolynomial.coeff_ofArray]
  simp [Array.getD_eq_getD_getElem?, hi]

/-- The descended polynomial is globally equal to the common denominator times
the input after embedding into `F(X)[Y]`. -/
theorem valueGlobal_descended (p : CPolynomial (Carrier F)) :
    valueGlobal (descended p) =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) (denominatorProduct p).toPoly) *
        FunctionFieldEuclid.value p := by
  ext i
  by_cases hi : i < p.val.size
  · rw [valueGlobal, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      FunctionFieldEuclid.value, Polynomial.coeff_map,
      CBivariate.toPoly_coeff, ← CPolynomial.coeff_toPoly p i,
      coeff_descended_of_lt p hi]
    change _ = _ * StoredField.value (p.coeff i)
    rw [StoredField.value_eq_num_div_den]
    have hden := RatFunc.algebraMap_ne_zero (StoredField.denominator_ne_zero (p.coeff i))
    rw [← mul_div_assoc]
    apply (eq_div_iff hden).mpr
    rw [← map_mul, clearedCoefficient_mul_denominator p hi, map_mul]
  · have hsize : p.val.size ≤ i := Nat.le_of_not_gt hi
    rw [valueGlobal, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      FunctionFieldEuclid.value, Polynomial.coeff_map,
      CBivariate.toPoly_coeff, ← CPolynomial.coeff_toPoly p i,
      coeff_descended_of_size_le p hsize,
      CPolynomial.coeff_eq_zero_of_size_le p hsize, toPoly_zero, map_zero]
    change (0 : RatFunc F) = _ * StoredField.value (0 : Carrier F)
    rw [StoredField.value_zero, MulZeroClass.mul_zero]

/-- Embedding a global polynomial agrees with coefficientwise algebraic embedding. -/
theorem value_embed (h : CBivariate F) :
    FunctionFieldEuclid.value (embed h) = valueGlobal h := by
  ext i
  rw [FunctionFieldEuclid.value, valueGlobal, Polynomial.coeff_map, Polynomial.coeff_map]
  by_cases hi : i < h.val.size
  · rw [← CPolynomial.coeff_toPoly (embed h) i, CBivariate.toPoly_coeff,
      coeff_embed_of_lt h hi]
    change StoredField.value (StoredField.ofPolynomial (CPolynomial.coeff h i)) = _
    rw [StoredField.value_ofPolynomial]
  · have hsize : h.val.size ≤ i := Nat.le_of_not_gt hi
    rw [← CPolynomial.coeff_toPoly (embed h) i, CBivariate.toPoly_coeff,
      coeff_embed_of_size_le h hsize, CPolynomial.coeff_eq_zero_of_size_le h hsize,
      toPoly_zero, map_zero]
    simp only [map_zero]

theorem valueGlobal_mul (a b : CBivariate F) :
    valueGlobal (a * b) = valueGlobal a * valueGlobal b := by
  simp only [valueGlobal, CBivariate.toPoly_mul, Polynomial.map_mul]

theorem valueGlobal_C (a : CPolynomial F) :
    valueGlobal (CPolynomial.C a : CPolynomial (CPolynomial F)) =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) a.toPoly) := by
  ext i
  rw [valueGlobal, Polynomial.coeff_map, CBivariate.toPoly_coeff]
  cases i with
  | zero => rw [CPolynomial.coeff_C]; simp
  | succ i => rw [CPolynomial.coeff_C]; simp [CPolynomial.toPoly_zero]

@[simp] theorem valueGlobal_zero : valueGlobal (0 : CBivariate F) = 0 := by
  simpa [CPolynomial.toPoly_zero] using valueGlobal_C (0 : CPolynomial F)

/-- Totalized primitive descent reconstructs the global polynomial exactly. -/
theorem content_mul_primitivePart (h : CBivariate F) :
    (CPolynomial.C (primitiveContent h) : CPolynomial (CPolynomial F)) *
      primitivePart h = (show CPolynomial (CPolynomial F) from h) := by
  by_cases hh : h = 0
  · simp [primitiveContent, primitivePart, hh]
  · simp only [primitiveContent, primitivePart, beq_iff_eq, hh, ↓reduceIte]
    exact CBivariate.C_yContent_mul_primitivePartY hh

/-- The totalized content is always nonzero, including the zero-input convention. -/
theorem primitiveContent_ne_zero (h : CBivariate F) :
    (primitiveContent h).toPoly ≠ 0 := by
  by_cases hh : h = 0
  · simp [primitiveContent, hh, CPolynomial.toPoly_one]
  · rw [primitiveContent, if_neg (by simpa using hh)]
    exact (CPolynomial.toPoly_eq_zero_iff (CBivariate.yContent h)).not.mpr
      (CBivariate.yContent_ne_zero hh)

omit [BEq F] [LawfulBEq F] in
private theorem raw_coeff_eq_coeff (q : CPolynomial (CPolynomial F)) (i : ℕ) :
    q.val.coeff i = CPolynomial.coeff q i := rfl

/-- Dividing by the computed global content really produces a primitive
polynomial; this is a divisibility certificate over `F[X]`. -/
theorem primitivePart_isYPrimitive {h : CBivariate F} (hh : h ≠ 0) :
    IsYPrimitive (primitivePart h) := by
  intro d hd
  have hc : (primitiveContent h).toPoly ≠ 0 := primitiveContent_ne_zero h
  have hdiv : (primitiveContent h).toPoly * d ∣ (primitiveContent h).toPoly := by
    rw [primitiveContent, if_neg (by simpa using hh)] at ⊢
    rw [CBivariate.dvd_yContent_iff]
    intro i
    obtain ⟨e, he⟩ := hd i
    refine ⟨e, ?_⟩
    have hcoeff : h.val.coeff i =
        CBivariate.yContent h * (CBivariate.primitivePartY h).val.coeff i := by
      calc
        h.val.coeff i = CPolynomial.coeff (↑h : CPolynomial (CPolynomial F)) i :=
          raw_coeff_eq_coeff _ _
        _ = CPolynomial.coeff
            ((CPolynomial.C (CBivariate.yContent h) : CPolynomial (CPolynomial F)) *
              CBivariate.primitivePartY h) i := congrArg
                (fun q : CPolynomial (CPolynomial F) => CPolynomial.coeff q i)
                (CBivariate.C_yContent_mul_primitivePartY hh).symm
        _ = _ := CPolynomial.coeff_C_mul _ _ i
        _ = _ := congrArg (CBivariate.yContent h * ·) (raw_coeff_eq_coeff _ _).symm
    rw [hcoeff, CPolynomial.toPoly_mul]
    rw [primitivePart, if_neg (by simpa using hh)] at he
    rw [he]
    ac_rfl
  obtain ⟨e, he⟩ := hdiv
  have hone : (1 : Polynomial F) = d * e := by
    apply mul_left_cancel₀ hc
    simpa [mul_assoc] using he
  exact isUnit_iff_dvd_one.mpr ⟨e, hone⟩

/-- The executable common-divisor certificate implies Mathlib's standard
`Polynomial.IsPrimitive` predicate on the mathematical nested polynomial. -/
theorem IsYPrimitive.isPrimitive {h : CBivariate F} (hh : IsYPrimitive h) :
    (CBivariate.toPoly h).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro d hd
  apply hh d
  intro i
  rw [raw_coeff_eq_coeff]
  rw [← CBivariate.toPoly_coeff]
  exact (Polynomial.C_dvd_iff_dvd_coeff d (CBivariate.toPoly h)).mp hd i

/-- The primitive descent identity after coefficient-field embedding. -/
theorem valueGlobal_content_mul_primitivePart (h : CBivariate F) :
    Polynomial.C
        (algebraMap (Polynomial F) (RatFunc F) (primitiveContent h).toPoly) *
      valueGlobal (primitivePart h) = valueGlobal h := by
  rw [← valueGlobal_C, ← valueGlobal_mul, content_mul_primitivePart]

/-- Construct the complete certified result. -/
def clear (p : CPolynomial (Carrier F)) : Result F :=
  ⟨denominatorProduct p, descended p, primitiveContent (descended p),
    primitivePart (descended p), denominatorProduct_ne_zero p⟩

/-- The result fields retain the global denominator-clearing identity. -/
theorem clear_global_identity (p : CPolynomial (Carrier F)) :
    valueGlobal (clear p).global =
      Polynomial.C
          (algebraMap (Polynomial F) (RatFunc F) (clear p).scale.toPoly) *
        FunctionFieldEuclid.value p :=
  valueGlobal_descended p

/-- The result fields retain the primitive reconstruction identity globally. -/
theorem clear_primitive_identity (p : CPolynomial (Carrier F)) :
    (CPolynomial.C (clear p).content : CPolynomial (CPolynomial F)) *
      (clear p).primitive =
      (clear p).global :=
  content_mul_primitivePart _

/-- Combined semantic identity: primitive descent differs from the original
function-field polynomial only by explicit nonzero scalar polynomials. -/
theorem clear_combined_identity (p : CPolynomial (Carrier F)) :
    Polynomial.C
        (algebraMap (Polynomial F) (RatFunc F) (clear p).content.toPoly) *
      valueGlobal (clear p).primitive =
    Polynomial.C
        (algebraMap (Polynomial F) (RatFunc F) (clear p).scale.toPoly) *
      FunctionFieldEuclid.value p := by
  change Polynomial.C
      (algebraMap (Polynomial F) (RatFunc F) (primitiveContent (descended p)).toPoly) *
    valueGlobal (primitivePart (descended p)) = _
  rw [valueGlobal_content_mul_primitivePart]
  exact valueGlobal_descended p

/-- Primitive descent is associated to the original function-field polynomial.
Both explicit scalar factors are units after embedding into `F(X)`. -/
theorem clear_primitive_associated (p : CPolynomial (Carrier F)) :
    Associated (valueGlobal (clear p).primitive) (FunctionFieldEuclid.value p) := by
  have hc0 : algebraMap (Polynomial F) (RatFunc F) (clear p).content.toPoly ≠ 0 :=
    RatFunc.algebraMap_ne_zero (primitiveContent_ne_zero (descended p))
  have hs0 : algebraMap (Polynomial F) (RatFunc F) (clear p).scale.toPoly ≠ 0 :=
    RatFunc.algebraMap_ne_zero (clear p).scale_ne_zero
  have hc : IsUnit (Polynomial.C
      (algebraMap (Polynomial F) (RatFunc F) (clear p).content.toPoly)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  have hs : IsUnit (Polynomial.C
      (algebraMap (Polynomial F) (RatFunc F) (clear p).scale.toPoly)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hs0)
  exact (associated_unit_mul_left _ _ hc).symm |>.trans <|
    (Associated.of_eq (clear_combined_identity p)) |>.trans
      (associated_unit_mul_left _ _ hs)

/-- A nonzero input has a nonzero global descent. -/
theorem clear_global_ne_zero {p : CPolynomial (Carrier F)}
    (hp : FunctionFieldEuclid.value p ≠ 0) : (clear p).global ≠ 0 := by
  intro hglobal
  have h := clear_global_identity p
  rw [hglobal, valueGlobal_zero] at h
  have hs : Polynomial.C
      (algebraMap (Polynomial F) (RatFunc F) (clear p).scale.toPoly) ≠ 0 := by
    rw [Polynomial.C_ne_zero]
    exact RatFunc.algebraMap_ne_zero (clear p).scale_ne_zero
  exact hp (mul_eq_zero.mp h.symm |>.resolve_left hs)

/-- The result carries a primitive certificate whenever the input is nonzero. -/
theorem clear_primitive_isYPrimitive {p : CPolynomial (Carrier F)}
    (hp : FunctionFieldEuclid.value p ≠ 0) : IsYPrimitive (clear p).primitive :=
  primitivePart_isYPrimitive (clear_global_ne_zero hp)

/-- The primitive result satisfies the standard certificate consumed by the
regular-center obstruction interface. -/
theorem clear_primitive_isPrimitive {p : CPolynomial (Carrier F)}
    (hp : FunctionFieldEuclid.value p ≠ 0) :
    (CBivariate.toPoly (clear p).primitive).IsPrimitive :=
  (clear_primitive_isYPrimitive hp).isPrimitive

/-- Gauss descent for callers such as function-field gcd: once the original
stored polynomial divides a global polynomial after localization, its primitive
descent already divides that polynomial in `F[X][Y]`. -/
theorem clear_primitive_dvd_global {p : CPolynomial (Carrier F)}
    (hp : FunctionFieldEuclid.value p ≠ 0) {h : CBivariate F}
    (hdiv : FunctionFieldEuclid.value p ∣ valueGlobal h) :
    CBivariate.toPoly (clear p).primitive ∣ CBivariate.toPoly h := by
  apply (clear_primitive_isPrimitive hp).dvd_of_fraction_map_dvd_fraction_map
    (K := RatFunc F)
  exact (clear_primitive_associated p).dvd.trans hdiv

/-- Before localization, every coefficient satisfies the cross-product identity.
This statement can be specialized at a zero of an intermediate denominator. -/
theorem clear_global_coefficient_identity (p : CPolynomial (Carrier F)) {i : ℕ}
    (hi : i < p.val.size) :
    (CPolynomial.coeff (clear p).global i).toPoly *
        (StoredField.denominator (p.coeff i)).toPoly =
      (clear p).scale.toPoly * (StoredField.numerator (p.coeff i)).toPoly := by
  change (CPolynomial.coeff (descended p) i).toPoly * _ = _
  rw [coeff_descended_of_lt p hi]
  exact clearedCoefficient_mul_denominator p hi

end ClearDenominators

end Polynomial.FunctionFieldAlgorithms
