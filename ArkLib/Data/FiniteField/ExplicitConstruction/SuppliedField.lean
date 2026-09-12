/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasis
public import ArkLib.Data.QuadraticAlgebra.FiniteWitness
public import Mathlib.Data.List.FinRange

/-!
# Coordinate indexing for supplied finite fields

The supplied polynomial-basis path reuses stored quotient arithmetic. Coordinate prefixes
allocate only the requested count. Quadratic indexing preserves the real coordinate as the
low radix digit, so the first entries are embedded base-field elements and the next block
crosses the base-field boundary. No primitive-element conversion is used.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Prime-field coefficient digits use the stored canonical natural-number representative. -/
def primeFiniteIndex (p : ℕ) [Fact p.Prime] : FiniteIndex (ZMod p) where
  cardinality := p
  one_lt_cardinality := (Fact.out : p.Prime).one_lt
  decode i := i.val
  encode a := ⟨a.val, a.val_lt⟩
  decode_encode a := ZMod.natCast_zmod_val a
  encode_decode i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- The actual supplied polynomial-basis field, indexed by its little-endian coefficient vector.
Irreducibility is needed for its Field instance, while the coordinate map needs only monicity. -/
def suppliedIndex (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] : Fin (p ^ f.natDegree) ≃ Carrier f :=
  polynomialBasisIndex f (primeFiniteIndex p)

/-- Cardinality of the supplied quotient comes from the actual modulus degree. -/
theorem suppliedCardinality (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] : Nat.card (Carrier f) = p ^ f.natDegree :=
  carrier_cardinality f (primeFiniteIndex p)

/-- The supplied irreducible presentation has positive degree, including degree one. -/
theorem suppliedDegree_pos (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact (Irreducible f.toPoly)] : 0 < f.natDegree := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_irreducible Fact.out)

/-- The field characteristic is the supplied prime, not the cardinality p^degree. -/
theorem suppliedCharacteristic (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] : ringChar (Carrier f) = p :=
  carrier_characteristic f

/-- A requested initial segment of a certified finite coordinate index. -/
def indexedPrefix {F : Type*} {q : ℕ} (index : Fin q ≃ F) (count : ℕ)
    (hcount : count ≤ q) : List F :=
  (List.finRange count).map fun i => index ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩

@[simp] theorem indexedPrefix_length {F : Type*} {q : ℕ} (index : Fin q ≃ F)
    (count : ℕ) (hcount : count ≤ q) : (indexedPrefix index count hcount).length = count := by
  simp [indexedPrefix]

theorem indexedPrefix_nodup {F : Type*} {q : ℕ} (index : Fin q ≃ F)
    (count : ℕ) (hcount : count ≤ q) : (indexedPrefix index count hcount).Nodup := by
  apply List.Nodup.map _ (List.nodup_finRange count)
  intro i j h
  have he := index.injective h
  exact Fin.ext (congrArg (fun i : Fin q => i.val) he)

/-- Allocate exactly the requested center prefix in the supplied polynomial-basis field. -/
def suppliedCenterPrefix (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] (count : ℕ) (hcount : count ≤ p ^ f.natDegree) : List (Carrier f) :=
  indexedPrefix (suppliedIndex p f) count hcount

@[simp] theorem suppliedCenterPrefix_length (p : ℕ) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] (count : ℕ)
    (hcount : count ≤ p ^ f.natDegree) :
    (suppliedCenterPrefix p f count hcount).length = count := indexedPrefix_length _ _ _

theorem suppliedCenterPrefix_nodup (p : ℕ) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] (count : ℕ)
    (hcount : count ≤ p ^ f.natDegree) :
    (suppliedCenterPrefix p f count hcount).Nodup := indexedPrefix_nodup _ _ _

/-- Index a quadratic algebra by two existing base-field coordinate indices. -/
def quadraticIndex {F : Type*} {q : ℕ} (index : Fin q ≃ F) (a b : F) :
    Fin (q ^ 2) ≃ QuadraticAlgebra F a b :=
  (finCongr (pow_two q)).trans <|
    finProdFinEquiv.symm.trans <|
      (Equiv.prodComm (Fin q) (Fin q)).trans <|
        (Equiv.prodCongr index index).trans (QuadraticAlgebra.equivProd a b).symm

/-- Quadratic cardinality is certified by coordinate equivalence, without enumerating values. -/
theorem quadraticIndex_cardinality {F : Type*} {q : ℕ} (index : Fin q ≃ F) (a b : F) :
    Nat.card (QuadraticAlgebra F a b) = q ^ 2 := by
  rw [← Nat.card_congr (quadraticIndex index a b), Nat.card_fin]

end ArkLib.FiniteField.ExplicitConstruction
