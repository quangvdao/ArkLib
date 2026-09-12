/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.Quotient
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Computed polynomial-basis coordinates for supplied finite fields

This module gives a supplied monic quotient a concrete coefficient-vector
indexing. Prefix generation maps only the requested range through the radix
index; it never allocates the complete field alphabet.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

open CompPoly CompPoly.CPolynomial PolynomialQuotient

/-- Certified computable indexing of a finite coefficient field. -/
structure FiniteIndex (E : Type*) where
  cardinality : Nat
  one_lt_cardinality : 1 < cardinality
  decode : Fin cardinality → E
  encode : E → Fin cardinality
  decode_encode : ∀ a, decode (encode a) = a
  encode_decode : ∀ i, encode (decode i) = i

namespace FiniteIndex

variable {E : Type*}

/-- The stored mutually inverse functions as an executable finite equivalence. -/
def equivFin (index : FiniteIndex E) : Fin index.cardinality ≃ E where
  toFun := index.decode
  invFun := index.encode
  left_inv := index.encode_decode
  right_inv := index.decode_encode

/-- The complete stored coefficient list, used only inside bounded polynomial search. -/
def values (index : FiniteIndex E) : List E := List.ofFn index.decode

@[simp] theorem length_values (index : FiniteIndex E) :
    index.values.length = index.cardinality := by simp [values]

theorem mem_values (index : FiniteIndex E) (a : E) : a ∈ index.values := by
  rw [values, List.mem_ofFn]
  exact ⟨index.encode a, index.decode_encode a⟩

theorem nodup_values (index : FiniteIndex E) : index.values.Nodup := by
  rw [values, List.nodup_ofFn]
  intro i j h
  rw [← index.encode_decode i, ← index.encode_decode j, h]

end FiniteIndex

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Reassemble little-endian monomial coordinates as a stored polynomial. -/
def coefficientPolynomial {d : Nat} (v : Fin d → E) : CPolynomial E :=
  CPolynomial.ofArray (Array.ofFn v)

@[simp] theorem coefficientPolynomial_coeff {d : Nat} (v : Fin d → E) (n : Nat) :
    (coefficientPolynomial v).coeff n = if h : n < d then v ⟨n, h⟩ else 0 := by
  rw [coefficientPolynomial, CPolynomial.coeff_ofArray]
  simp [Array.getD]

theorem coefficientPolynomial_degree {d : Nat} (v : Fin d → E) :
    (coefficientPolynomial v).toPoly.degree < d := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [← CPolynomial.coeff_toPoly, coefficientPolynomial_coeff, dif_neg (by omega)]

variable (m : CPolynomial E) [Fact m.monic]

/-- Canonical quotient element with the prescribed monomial coordinates. -/
def quotientOfCoefficients (v : Fin m.natDegree → E) : Carrier m :=
  canonical m (coefficientPolynomial v)

@[simp] theorem quotientOfCoefficients_val (v : Fin m.natDegree → E) :
    (quotientOfCoefficients m v).val = coefficientPolynomial v := by
  apply CPolynomial.toPoly_injective
  change (reduce m (coefficientPolynomial v)).toPoly = _
  rw [reduce, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out]
  apply (Polynomial.modByMonic_eq_self_iff
    ((CPolynomial.monic_toPoly_iff m).mp Fact.out)).mpr
  have hm0 : m.toPoly ≠ 0 := ((CPolynomial.monic_toPoly_iff m).mp Fact.out).ne_zero
  rw [Polynomial.degree_eq_natDegree hm0, ← CPolynomial.natDegree_toPoly]
  exact coefficientPolynomial_degree v

/-- Executable monomial-coordinate equivalence for the supplied quotient. -/
def quotientCoefficientsEquiv : Carrier m ≃ (Fin m.natDegree → E) where
  toFun a i := a.val.coeff i.val
  invFun := quotientOfCoefficients m
  left_inv a := by
    apply Subtype.ext
    rw [quotientOfCoefficients_val]
    apply CPolynomial.toPoly_injective
    apply Polynomial.ext
    intro n
    rw [← CPolynomial.coeff_toPoly, coefficientPolynomial_coeff,
      ← CPolynomial.coeff_toPoly]
    split
    · rfl
    · have hm0 : m.toPoly ≠ 0 :=
        ((CPolynomial.monic_toPoly_iff m).mp Fact.out).ne_zero
      have hdegree := degree_lt m a
      rw [Polynomial.degree_eq_natDegree hm0,
        ← CPolynomial.natDegree_toPoly] at hdegree
      rw [CPolynomial.coeff_toPoly]
      exact ((Polynomial.degree_lt_iff_coeff_zero _ _).mp hdegree n (by omega)).symm
  right_inv v := by
    funext i
    change (quotientOfCoefficients m v).val.coeff i.val = v i
    rw [quotientOfCoefficients_val, coefficientPolynomial_coeff, dif_pos i.isLt]

/-- Coordinatewise conversion between radix digits and coefficient-field values. -/
def coefficientIndexEquiv (index : FiniteIndex E) (d : Nat) :
    (Fin d → Fin index.cardinality) ≃ (Fin d → E) where
  toFun v i := index.decode (v i)
  invFun v i := index.encode (v i)
  left_inv v := funext fun i => index.encode_decode (v i)
  right_inv v := funext fun i => index.decode_encode (v i)

/-- Little-endian radix indexing of the supplied polynomial-basis quotient. -/
def polynomialBasisIndex (index : FiniteIndex E) :
    Fin (index.cardinality ^ m.natDegree) ≃ Carrier m :=
  finFunctionFinEquiv.symm |>.trans
    ((coefficientIndexEquiv index m.natDegree).trans (quotientCoefficientsEquiv m).symm)

/-- One indexed quotient value, with zero outside the finite radix range. -/
def polynomialBasisElement (index : FiniteIndex E) (n : Nat) : Carrier m :=
  if h : n < index.cardinality ^ m.natDegree then
    polynomialBasisIndex m index ⟨n, h⟩
  else 0

/-- Requested prefix only; the complete quotient alphabet is never allocated. -/
def polynomialBasisPrefix (index : FiniteIndex E) (count : Nat) : List (Carrier m) :=
  (List.range count).map (polynomialBasisElement m index)

@[simp] theorem polynomialBasisPrefix_length (index : FiniteIndex E) (count : Nat) :
    (polynomialBasisPrefix m index count).length = count := by
  simp [polynomialBasisPrefix]

theorem polynomialBasisElement_injective_of_lt (index : FiniteIndex E)
    {a b : Nat} (ha : a < index.cardinality ^ m.natDegree)
    (hb : b < index.cardinality ^ m.natDegree)
    (h : polynomialBasisElement m index a = polynomialBasisElement m index b) : a = b := by
  rw [polynomialBasisElement, dif_pos ha, polynomialBasisElement, dif_pos hb] at h
  exact Fin.ext_iff.mp ((polynomialBasisIndex m index).injective h)

theorem polynomialBasisPrefix_nodup (index : FiniteIndex E) {count : Nat}
    (hcount : count ≤ index.cardinality ^ m.natDegree) :
    (polynomialBasisPrefix m index count).Nodup := by
  apply List.Nodup.map_on
      (l := List.range count) (f := polynomialBasisElement m index)
  · intro a ha b hb hab
    exact polynomialBasisElement_injective_of_lt m index
      (lt_of_lt_of_le (List.mem_range.mp ha) hcount)
      (lt_of_lt_of_le (List.mem_range.mp hb) hcount) hab
  · exact List.nodup_range

/-- Symbolic quotient cardinality, obtained from the coefficient equivalence. -/
theorem carrier_cardinality (index : FiniteIndex E) :
    Nat.card (Carrier m) = index.cardinality ^ m.natDegree := by
  have hE : Nat.card E = index.cardinality := by
    simpa using (Nat.card_congr index.equivFin).symm
  rw [Nat.card_congr (quotientCoefficientsEquiv m), Nat.card_fun, hE, Nat.card_fin]

/-- A supplied irreducible quotient retains the characteristic of its coefficient field. -/
instance carrierCharP {p : Nat} [CharP E p] [Fact (Irreducible m.toPoly)] :
    CharP (Carrier m) p :=
  charP_of_injective_ringHom
    (embedding_injective m (Polynomial.degree_pos_of_irreducible Fact.out)) p

@[simp] theorem carrier_characteristic {p : Nat} [CharP E p]
    [Fact (Irreducible m.toPoly)] : ringChar (Carrier m) = p := ringChar.eq _ p

end ArkLib.FiniteField.ExplicitConstruction
