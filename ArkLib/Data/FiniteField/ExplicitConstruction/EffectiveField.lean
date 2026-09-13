/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField

/-!
# Operational data for an effective supplied finite field

The existing `Field` and lawful boolean equality instances own arithmetic and equality.
This record adds the presentation-specific executable operations and their laws. It
contains no cost assumptions and requires no conversion to an absolute polynomial basis.
The index order is supplied explicitly; prefixes compute only the requested entries.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Presentation-specific operations over existing executable field instances.
The inverse Frobenius callback may close over reusable preprocessing data. -/
structure EffectiveField (p : Nat) (K : Type*) [Field K] [BEq K] [LawfulBEq K] where
  prime : p.Prime
  characteristic : CharP K p
  degree : Nat
  degree_pos : 0 < degree
  index : FiniteIndex K
  cardinality_eq : index.cardinality = p ^ degree
  primeEmbedding : ZMod p →+* K
  inverseFrobenius : K → K
  inverseFrobenius_pow : ∀ a, inverseFrobenius a ^ p = a

namespace EffectiveField

variable {p : Nat} {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- Decode a canonical coordinate number, without enumerating the field. -/
def unindex (F : EffectiveField p K) : Fin F.index.cardinality → K := F.index.decode

/-- Encode an element in the supplied canonical coordinate order. -/
def elementIndex (F : EffectiveField p K) : K → Fin F.index.cardinality := F.index.encode

@[simp] theorem unindex_elementIndex (F : EffectiveField p K) (a : K) :
    F.unindex (F.elementIndex a) = a := F.index.decode_encode a

@[simp] theorem elementIndex_unindex (F : EffectiveField p K)
    (i : Fin F.index.cardinality) : F.elementIndex (F.unindex i) = i :=
  F.index.encode_decode i

/-- Prefix allocation visits exactly `count` coordinate numbers. -/
def elementPrefix (F : EffectiveField p K) (count : Nat) (hcount : count ≤ F.index.cardinality) :
    List K := indexedPrefix F.index.equivFin count hcount

@[simp] theorem prefix_length (F : EffectiveField p K) (count : Nat)
    (hcount : count ≤ F.index.cardinality) : (F.elementPrefix count hcount).length = count :=
  indexedPrefix_length _ _ _

theorem prefix_nodup (F : EffectiveField p K) (count : Nat)
    (hcount : count ≤ F.index.cardinality) : (F.elementPrefix count hcount).Nodup :=
  indexedPrefix_nodup _ _ _

/-- The coordinate bijection certifies the cardinality independently of enumeration. -/
theorem cardinality (F : EffectiveField p K) : Nat.card K = p ^ F.degree := by
  rw [← Nat.card_congr F.index.equivFin, Nat.card_fin, F.cardinality_eq]

/-- The characteristic law can be installed locally by a generic consumer. -/
theorem ringChar_eq (F : EffectiveField p K) : ringChar K = p := by
  let := F.characteristic
  exact ringChar.eq K p

/-- The supplied prime-field map is faithful. -/
theorem primeEmbedding_injective (F : EffectiveField p K) :
    Function.Injective F.primeEmbedding := by
  let : Fact p.Prime := ⟨F.prime⟩
  exact F.primeEmbedding.injective

end EffectiveField

/-- The prime-field representation itself needs no extension or Frobenius preprocessing. -/
def effectivePrimeField (p : Nat) [Fact p.Prime] : EffectiveField p (ZMod p) where
  prime := Fact.out
  characteristic := inferInstance
  degree := 1
  degree_pos := Nat.zero_lt_one
  index := primeFiniteIndex p
  cardinality_eq := (pow_one p).symm
  primeEmbedding := RingHom.id _
  inverseFrobenius := id
  inverseFrobenius_pow := ZMod.pow_card

end ArkLib.FiniteField.ExplicitConstruction
