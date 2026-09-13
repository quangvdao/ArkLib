/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasis
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Proof and exhaustive runtime checks for computed inverse Frobenius maps. -/

namespace PolynomialBasisFrobeniusTests

open ArkLib.FiniteField.ExplicitConstruction CompPoly CompPoly.CPolynomial

namespace Binary

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def index : FiniteIndex (ZMod 2) where
  cardinality := 2
  one_lt_cardinality := by decide
  decode i := i.val
  encode a := ⟨a.val, a.val_lt⟩
  decode_encode a := ZMod.natCast_zmod_val a
  encode_decode i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- The degree-one presentation of F2, whose quotient generator is zero. -/
abbrev linearModulus : CPolynomial (ZMod 2) := X

instance : Fact linearModulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

instance : Fact (Irreducible linearModulus.toPoly) := ⟨by
  rw [CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

/-- `X² + X + 1` is the supplied irreducible modulus for F4. -/
abbrev modulus : CPolynomial (ZMod 2) := X ^ 2 + X + C 1

instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  convert Polynomial.monic_X_pow_add (n := 2)
    (p := Polynomial.X + Polynomial.C (1 : ZMod 2))
    (by rw [Polynomial.degree_X_add_C]; decide) using 1
  ring⟩

theorem modulus_degree : modulus.natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.natDegree_quadratic (R := ZMod 2)
    (a := 1) (b := 1) (c := 1) one_ne_zero)

theorem modulus_irreducible : Irreducible modulus.toPoly := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hroot := (Polynomial.mem_roots' (p := modulus.toPoly)).mp hx
    have heval : x ^ 2 + x + 1 = 0 := by
      simpa [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.IsRoot] using hroot.2
    have hxval : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    have hxlt := x.val_lt
    interval_cases h : x.val
    all_goals rw [hxval] at heval
    case «0» => exact (show (0 : ZMod 2) ^ 2 + 0 + 1 ≠ 0 by decide) heval
    case «1» => exact (show (1 : ZMod 2) ^ 2 + 1 + 1 ≠ 0 by decide) heval
  · rw [← CPolynomial.natDegree_toPoly, modulus_degree]
  · rw [← CPolynomial.natDegree_toPoly, modulus_degree]
    decide

instance : Fact (Irreducible modulus.toPoly) := ⟨modulus_irreducible⟩

end Binary

namespace Ternary

abbrev linearModulus :=
  ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.linearModulus

instance : Fact (Irreducible linearModulus.toPoly) := ⟨by
  rw [CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

end Ternary

example : frobeniusTheta 2 Binary.linearModulus = 0 := by
  simp [frobeniusTheta, canonical_modulus_eq_zero]

example : frobeniusRootGCD 2 Binary.linearModulus =
    X - C (frobeniusBeta 2 Binary.linearModulus) :=
  frobeniusRootGCD_eq_X_sub_C 2 Binary.linearModulus

example (a : Carrier Binary.modulus) : inverseFrobenius 2 Binary.modulus a ^ 2 = a :=
  inverseFrobenius_pow 2 Binary.modulus a

example (a : Carrier Binary.modulus) :
    (prepareInverseFrobenius 2 Binary.modulus).apply 2 Binary.modulus a =
      inverseFrobenius 2 Binary.modulus a :=
  prepareInverseFrobenius_apply 2 Binary.modulus a

example (a : Carrier
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus) :
    inverseFrobenius 3
      ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus a ^ 3 = a :=
  inverseFrobenius_pow 3
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus a

/-- Exhaustively execute the computed gcd and inverse map on F2, F4, and F9. -/
def run : IO Unit := do
  let f2 := polynomialBasisPrefix Binary.linearModulus Binary.index 2
  unless frobeniusTheta 2 Binary.linearModulus == 0 &&
      frobeniusBeta 2 Binary.linearModulus == 0 &&
      frobeniusBeta 2 Binary.linearModulus ^ 2 ==
        frobeniusTheta 2 Binary.linearModulus &&
      (frobeniusRootGCD 2 Binary.linearModulus).natDegree == 1 &&
      frobeniusRootGCD 2 Binary.linearModulus ==
        X - C (frobeniusBeta 2 Binary.linearModulus) do
    throw <| IO.userError "F2 degree-one theta-zero gcd/root check failed"
  let indexF2 := polynomialBasisIndex Binary.linearModulus Binary.index
  unless f2.all (fun a =>
      inverseFrobenius 2 Binary.linearModulus a ^ 2 == a &&
      boundedInverseFrobenius 2 Binary.linearModulus 3 (by decide) a ^ 2 == a &&
      indexF2 (indexF2.symm a) == a) do
    throw <| IO.userError "F2 inverse Frobenius failed"
  let f4 := polynomialBasisPrefix Binary.modulus Binary.index 4
  let preparedF4 := prepareInverseFrobenius 2 Binary.modulus
  let certificateF4 := boundedInverseFrobeniusCertificate 2 Binary.modulus 3 (by decide)
  unless f4.length == 4 &&
      preparedF4.beta == frobeniusBeta 2 Binary.modulus &&
      preparedF4.powers.size == 2 &&
      preparedF4.power 2 Binary.modulus ⟨0, by decide⟩ == 1 &&
      preparedF4.power 2 Binary.modulus ⟨1, by decide⟩ == preparedF4.beta &&
      frobeniusBeta 2 Binary.modulus ^ 2 == frobeniusTheta 2 Binary.modulus &&
      (frobeniusRootGCD 2 Binary.modulus).natDegree == 1 &&
      frobeniusRootGCD 2 Binary.modulus == X - C (frobeniusBeta 2 Binary.modulus) do
    throw <| IO.userError "F4 computed gcd/root check failed"
  let indexF4 := polynomialBasisIndex Binary.modulus Binary.index
  unless f4.all (fun a =>
      preparedF4.apply 2 Binary.modulus a == inverseFrobenius 2 Binary.modulus a &&
      certificateF4.inverse a == preparedF4.apply 2 Binary.modulus a &&
      inverseFrobenius 2 Binary.modulus a ^ 2 == a &&
      boundedInverseFrobenius 2 Binary.modulus 3 (by decide) a ^ 2 == a &&
      indexF4 (indexF4.symm a) == a) do
    throw <| IO.userError "F4 prepared inverse Frobenius failed"
  let modulus9 := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
  let index3 := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.index3
  let f3 := polynomialBasisPrefix Ternary.linearModulus index3 3
  unless frobeniusTheta 3 Ternary.linearModulus == 0 &&
      frobeniusBeta 3 Ternary.linearModulus == 0 &&
      (frobeniusRootGCD 3 Ternary.linearModulus).natDegree == 1 &&
      frobeniusRootGCD 3 Ternary.linearModulus ==
        X - C (frobeniusBeta 3 Ternary.linearModulus) do
    throw <| IO.userError "F3 degree-one theta-zero gcd/root check failed"
  let indexF3 := polynomialBasisIndex Ternary.linearModulus index3
  unless f3.all (fun a => inverseFrobenius 3 Ternary.linearModulus a ^ 3 == a &&
      boundedInverseFrobenius 3 Ternary.linearModulus 3 (by decide) a ^ 3 == a &&
      indexF3 (indexF3.symm a) == a) do
    throw <| IO.userError "F3 inverse Frobenius failed"
  let f9 := polynomialBasisPrefix modulus9 index3 9
  unless f9.length == 9 &&
      frobeniusBeta 3 modulus9 ^ 3 == frobeniusTheta 3 modulus9 &&
      (frobeniusRootGCD 3 modulus9).natDegree == 1 &&
      frobeniusRootGCD 3 modulus9 == X - C (frobeniusBeta 3 modulus9) do
    throw <| IO.userError "F9 computed gcd/root check failed"
  let indexF9 := polynomialBasisIndex modulus9 index3
  unless f9.all (fun a => inverseFrobenius 3 modulus9 a ^ 3 == a &&
      boundedInverseFrobenius 3 modulus9 3 (by decide) a ^ 3 == a &&
      indexF9 (indexF9.symm a) == a) do
    throw <| IO.userError "F9 exhaustive inverse Frobenius failed"

#print axioms frobeniusRootGCD_eq_X_sub_C
#print axioms prepareInverseFrobenius_apply
#print axioms inverseFrobenius_pow
#print axioms boundedInverseFrobenius_pow

end PolynomialBasisFrobeniusTests
