/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasis
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic

/-! Runtime and proof checks for supplied polynomial-basis finite fields. -/

namespace ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis

open ArkLib.FiniteField.ExplicitConstruction CompPoly CompPoly.CPolynomial
  ArkLib.PolynomialQuotient

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def index3 : FiniteIndex (ZMod 3) where
  cardinality := 3
  one_lt_cardinality := by decide
  decode i := i.val
  encode a := ⟨a.val, a.val_lt⟩
  decode_encode a := ZMod.natCast_zmod_val a
  encode_decode i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- `X² + 1` is the supplied irreducible modulus for the actual field F₉. -/
abbrev modulus : CPolynomial (ZMod 3) := X ^ 2 + C 1

instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  rw [CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_add_C (n := 2) (1 : ZMod 3) (by decide)⟩

theorem modulus_degree : modulus.natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  rw [CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  exact Polynomial.natDegree_X_pow_add_C

theorem modulus_irreducible : Irreducible modulus.toPoly := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hroot := (Polynomial.mem_roots' (p := modulus.toPoly)).mp hx
    have heval : x ^ 2 + 1 = 0 := by
      simpa [modulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.IsRoot] using hroot.2
    have hxval : x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
    have hxlt := x.val_lt
    interval_cases h : x.val
    all_goals rw [hxval] at heval
    case «0» => exact (show (0 : ZMod 3) ^ 2 + 1 ≠ 0 by decide) heval
    case «1» => exact (show (1 : ZMod 3) ^ 2 + 1 ≠ 0 by decide) heval
    case «2» => exact (show (2 : ZMod 3) ^ 2 + 1 ≠ 0 by decide) heval
  · rw [← CPolynomial.natDegree_toPoly, modulus_degree]
  · rw [← CPolynomial.natDegree_toPoly, modulus_degree]
    decide

instance : Fact (Irreducible modulus.toPoly) := ⟨modulus_irreducible⟩

example : (polynomialBasisPrefix modulus index3 0).length = 0 := by simp
example : (polynomialBasisPrefix modulus index3 1).length = 1 := by simp
example : (polynomialBasisPrefix modulus index3 9).length = 9 := by simp
example : (polynomialBasisPrefix modulus index3 9).Nodup := by
  apply polynomialBasisPrefix_nodup
  rw [modulus_degree]
  decide
example : Nat.card (Carrier modulus) = 9 := by
  rw [carrier_cardinality modulus index3, modulus_degree]
  decide
example : ringChar (Carrier modulus) = 3 := carrier_characteristic modulus

/-- Degree-one supplied presentation; its generator is zero in the quotient. -/
abbrev linearModulus : CPolynomial (ZMod 3) := X
instance : Fact linearModulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  rw [CPolynomial.X_toPoly]
  exact (Polynomial.monic_X : (Polynomial.X : Polynomial (ZMod 3)).Monic)⟩

example : (canonical linearModulus X : Carrier linearModulus) = 0 := by
  rw [← canonical_zero linearModulus]
  apply Subtype.ext
  apply CPolynomial.toPoly_injective
  change (X.modByMonic linearModulus).toPoly =
    ((0 : CPolynomial (ZMod 3)).modByMonic linearModulus).toPoly
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic X linearModulus Fact.out,
    CPolynomial.modByMonic_toPoly_eq_modByMonic 0 linearModulus Fact.out,
    CPolynomial.X_toPoly, CPolynomial.toPoly_zero]
  rw [Polynomial.modByMonic_self Polynomial.monic_X, Polynomial.zero_modByMonic]

/-- Executable assertions for the radix trace and both directions of the index. -/
def run : IO Unit := do
  let xs := polynomialBasisPrefix modulus index3 9
  unless (polynomialBasisPrefix modulus index3 0).length == 0 do
    throw <| IO.userError "zero-length prefix failed"
  unless (polynomialBasisPrefix modulus index3 1).length == 1 do
    throw <| IO.userError "one-element prefix failed"
  unless xs.length == 9 do
    throw <| IO.userError "full F9 prefix failed"
  let low := xs.map (fun a => a.val.coeff 0)
  let high := xs.map (fun a => a.val.coeff 1)
  unless low == [0, 1, 2, 0, 1, 2, 0, 1, 2] do
    throw <| IO.userError s!"unexpected low-coordinate trace: {repr low}"
  unless high == [0, 0, 0, 1, 1, 1, 2, 2, 2] do
    throw <| IO.userError s!"unexpected high-coordinate trace: {repr high}"
  have hcard : index3.cardinality ^ modulus.natDegree = 9 := by
    rw [modulus_degree]
    decide
  unless (List.finRange 9).all (fun i =>
      let j := (finCongr hcard).symm i
      (polynomialBasisIndex modulus index3).symm
        (polynomialBasisIndex modulus index3 j) == j) do
    throw <| IO.userError "forward/reverse radix index round-trip failed"
  unless xs.all (fun a =>
      polynomialBasisIndex modulus index3
        ((polynomialBasisIndex modulus index3).symm a) == a) do
    throw <| IO.userError "reverse/forward quotient index round-trip failed"
  let linear := polynomialBasisPrefix linearModulus index3 3
  unless linear.length == 3 do
    throw <| IO.userError "degree-one full prefix failed"
  unless (canonical linearModulus X : Carrier linearModulus) == 0 do
    throw <| IO.userError "degree-one theta is not zero"


end ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis
