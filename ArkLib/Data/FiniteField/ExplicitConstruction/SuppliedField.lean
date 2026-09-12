/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.Quotient
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
