/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveFrobeniusCoordinates
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveRelativeQuotient

/-! Acceptance clients for supplied cyclic Frobenius coordinates. -/

namespace EffectiveFrobeniusCoordinatesTests

open ArkLib.FiniteField.ExplicitConstruction

/-- The normal basis `1` of a prime field, including its explicit coordinates. -/
def primeCoordinates (p : Nat) [Fact p.Prime] : SuppliedFrobeniusCoordinates p 1 (ZMod p) where
  prime := Fact.out
  characteristic := inferInstance
  degree_pos := Nat.zero_lt_one
  coordinates := {
    toFun a _ := a
    invFun v := v 0
    left_inv _ := rfl
    right_inv v := by
      funext i
      change v 0 = v i
      exact congrArg v (Subsingleton.elim _ _) }
  primeEmbedding := RingHom.id _
  frobenius_coordinates a _ := ZMod.pow_card a

example {p d : Nat} {K : Type*} [Field K] (N : SuppliedFrobeniusCoordinates p d K) (a : K) :
    N.inverseFrobenius a ^ p = a := N.inverseFrobenius_pow a

example {p d : Nat} {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (N : SuppliedFrobeniusCoordinates p d K) : Nat.card K = p ^ d := N.effectiveField.cardinality

/-- Convert monomial coordinates to the normal basis `(theta, theta²)` of F4. -/
def binaryBasisChange : (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2) where
  toFun v := ![v 1 + v 0, v 0]
  invFun v := ![v 1, v 0 - v 1]
  left_inv v := by funext i; fin_cases i <;> simp
  right_inv v := by funext i; fin_cases i <;> simp

/-- The supplied F4 coordinates use an actual two-cycle under Frobenius. -/
def binaryCoordinateEquiv : EffectiveRelativeQuotientTests.F4 ≃ (Fin 2 → ZMod 2) :=
  (quotientCoefficientsEquiv PolynomialBasisFrobeniusTests.Binary.modulus).trans
    ((Equiv.piCongrLeft (fun _ : Fin 2 => ZMod 2)
      (finCongr PolynomialBasisFrobeniusTests.Binary.modulus_degree)).trans binaryBasisChange)

theorem binary_frobenius_coordinates :
    ∀ (a : Fin 4) (i : Fin 2),
      binaryCoordinateEquiv ((EffectiveRelativeQuotientTests.baseIndex a) ^ 2) i =
        binaryCoordinateEquiv (EffectiveRelativeQuotientTests.baseIndex a)
          ((finRotate 2).symm i) := by decide +kernel

/-- This F4 fixture happens to use normal-basis coordinates with their proved shift law. -/
def binaryCoordinates : SuppliedFrobeniusCoordinates 2 2 EffectiveRelativeQuotientTests.F4 where
  prime := by decide
  characteristic := inferInstance
  degree_pos := by decide
  coordinates := binaryCoordinateEquiv
  primeEmbedding := embedding PolynomialBasisFrobeniusTests.Binary.modulus
  frobenius_coordinates a i := by
    have h := binary_frobenius_coordinates
      (EffectiveRelativeQuotientTests.baseIndex.symm a) i
    simpa using h

/-- Frobenius-coordinate consumers use the same explicitly prepared generic field interface. -/
def run : IO Unit := do
  EffectiveFieldTests.check (primeCoordinates 2).effectiveField 2 (by decide)
  EffectiveFieldTests.check (primeCoordinates 3).effectiveField 3 (by decide)
  EffectiveFieldTests.check binaryCoordinates.effectiveField 4 (by decide)

#print axioms SuppliedFrobeniusCoordinates.inverseFrobenius_pow
#print axioms SuppliedFrobeniusCoordinates.effectiveField

end EffectiveFrobeniusCoordinatesTests
