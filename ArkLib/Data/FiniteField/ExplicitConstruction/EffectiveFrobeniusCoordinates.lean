/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveField
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Supplied Frobenius-coordinate operational adapter

The caller supplies actual canonical coordinates and their cyclic Frobenius law.
Arithmetic continues to use the existing field instances. This does not construct
normal bases or assert arithmetic costs for an arbitrary supplied implementation.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Operational data furnished by a supplied cyclic Frobenius coordinate system.
The coordinate indices rotate under the `p`-power map; no linearity is asserted. -/
structure SuppliedFrobeniusCoordinates (p d : Nat) (K : Type*) [Field K] where
  prime : p.Prime
  characteristic : CharP K p
  degree_pos : 0 < d
  coordinates : K ≃ (Fin d → ZMod p)
  primeEmbedding : ZMod p →+* K
  frobenius_coordinates : ∀ a i,
    coordinates (a ^ p) i = coordinates a ((finRotate d).symm i)

namespace SuppliedFrobeniusCoordinates

variable {p d : Nat} {K : Type*} [Field K]

/-- Inverse Frobenius is one cyclic shift of the supplied coordinates. -/
def inverseFrobenius (N : SuppliedFrobeniusCoordinates p d K) (a : K) : K :=
  N.coordinates.symm fun i => N.coordinates a (finRotate d i)

/-- Evaluation reads exactly the next cyclic coordinate. -/
theorem inverseFrobenius_coordinates (N : SuppliedFrobeniusCoordinates p d K) (a : K)
    (i : Fin d) :
    N.coordinates (N.inverseFrobenius a) i = N.coordinates a (finRotate d i) := by
  simp only [inverseFrobenius, Equiv.apply_symm_apply]

/-- The inverse shift is certified by the supplied forward Frobenius law. -/
theorem inverseFrobenius_pow (N : SuppliedFrobeniusCoordinates p d K) (a : K) :
    N.inverseFrobenius a ^ p = a := by
  apply N.coordinates.injective
  funext i
  rw [N.frobenius_coordinates]
  simp only [inverseFrobenius, Equiv.apply_symm_apply]

/-- Prime-field radix digits, interpreted in the supplied Frobenius coordinates. -/
def elementEquiv (N : SuppliedFrobeniusCoordinates p d K) : Fin (p ^ d) ≃ K :=
  letI : Fact p.Prime := ⟨N.prime⟩
  finFunctionFinEquiv.symm |>.trans
    ((coefficientIndexEquiv (primeFiniteIndex p) d).trans N.coordinates.symm)

/-- Assemble operational field data without changing arithmetic representations. -/
def effectiveField [BEq K] [LawfulBEq K] (N : SuppliedFrobeniusCoordinates p d K) :
    EffectiveField p K where
  prime := N.prime
  characteristic := N.characteristic
  degree := d
  degree_pos := N.degree_pos
  index := {
    cardinality := p ^ d
    one_lt_cardinality := Nat.one_lt_pow (Nat.ne_of_gt N.degree_pos) N.prime.one_lt
    decode := N.elementEquiv
    encode := N.elementEquiv.symm
    decode_encode := N.elementEquiv.apply_symm_apply
    encode_decode := N.elementEquiv.symm_apply_apply }
  cardinality_eq := rfl
  primeEmbedding := N.primeEmbedding
  prepareInverseFrobenius := fun _ => {
    inverseFrobenius := N.inverseFrobenius
    inverseFrobenius_pow := N.inverseFrobenius_pow }

end SuppliedFrobeniusCoordinates

end ArkLib.FiniteField.ExplicitConstruction
