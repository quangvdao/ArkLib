/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.Goldilocks
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Concrete fields used by the Reed--Solomon examples

Concrete probability bounds use both the cardinality and the characteristic of their challenge
field. Recording only a natural number for the field size would leave open whether a field with
the required algebraic properties has actually been selected. This module supplies canonical
mathematical models for the two fields used by the Reed--Solomon examples.

## Reading the statements

`BN254Scalar` is CompPoly's canonical `ZMod r`, where `r` is the certified BN254 scalar prime.
Its cardinality and characteristic are both `r`. `GoldilocksCubic` is Mathlib's degree-three
Galois field over CompPoly's certified Goldilocks prime `p`. Its cardinality is `p^3`, while its
characteristic remains `p`. The distinction matters because list-decoding assumptions constrain
the characteristic, whereas probability denominators use the cardinality.

## Mathematical scope

The types here are abstract finite-field models. This module does not choose evaluation points,
construct roots of unity, fix a serialized extension-field representation, or identify a
protocol implementation with these models. Concrete coding theorems receive a domain embedding
separately.
-/

namespace ArkLibExamples.ReedSolomon.ConcreteFields

noncomputable section

/-- The canonical BN254 scalar field. -/
abbrev BN254Scalar := BN254.ScalarField

/-- The BN254 model has exactly the scalar-prime number of elements. -/
theorem bn254Scalar_card : Fintype.card BN254Scalar = BN254.scalarFieldSize :=
  ZMod.card BN254.scalarFieldSize

/-- The characteristic of the canonical BN254 model is its scalar prime. -/
theorem bn254Scalar_ringChar : ringChar BN254Scalar = BN254.scalarFieldSize :=
  ZMod.ringChar_zmod_n BN254.scalarFieldSize

/-- CompPoly's primality certificate supplies the instance needed by `GaloisField`. -/
instance goldilocksPrimeFact : Fact Goldilocks.fieldSize.Prime := ⟨Goldilocks.is_prime⟩

/-- The degree-three extension of the Goldilocks prime field. -/
abbrev GoldilocksCubic := GaloisField Goldilocks.fieldSize 3

instance : Fintype GoldilocksCubic := Fintype.ofFinite GoldilocksCubic

/-- The cubic Goldilocks model has `p^3` elements. -/
theorem goldilocksCubic_card :
    Fintype.card GoldilocksCubic = Goldilocks.fieldSize ^ 3 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card Goldilocks.fieldSize 3 (by decide)]

/-- The cubic extension retains Goldilocks characteristic. -/
theorem goldilocksCubic_ringChar : ringChar GoldilocksCubic = Goldilocks.fieldSize := by
  exact ringChar.eq GoldilocksCubic Goldilocks.fieldSize

end

end ArkLibExamples.ReedSolomon.ConcreteFields
