/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.MvPolynomial.CheckedExactDivision
import Mathlib.Algebra.Field.ZMod

/-! Executable and theorem-level tests for general-order checked exact division. -/

namespace CheckedExactDivisionTests

open CPoly CPoly.CMvPolynomial
open CPoly.CMvPolynomial.CheckedExactDivision

private def x {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F :=
  CMvPolynomial.X 0
private def y {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F :=
  CMvPolynomial.X 1
private def z {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F :=
  CMvPolynomial.X 2

private def divisor {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F := x + y + 1
private def quotient {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F :=
  z ^ 2 + x * y + 3
private def dividend {F : Type*} [Field F] [DecidableEq F] : CMvPolynomial 3 F :=
  quotient * divisor

/-- Exercise a three-variable exact quotient. -/
def runExact {F : Type*} [Field F] [DecidableEq F] : IO Unit := do
  unless (exactQuotient? (dividend (F := F)) (divisor (F := F))).isSome do
    throw (IO.userError "three-variable exact division failed")

/-- Exercise failure when the supplied fuel permits no cancellation step. -/
def runNoFuel {F : Type*} [Field F] [DecidableEq F] : IO Unit := do
  unless (exactQuotientWithFuel? 0 (dividend (F := F)) (divisor (F := F))).isNone do
    throw (IO.userError "zero division fuel unexpectedly succeeded")

/-- Exercise rejection of a polynomial that does not divide the dividend. -/
def runNondivisor {F : Type*} [Field F] [DecidableEq F] : IO Unit := do
  unless (exactQuotient? (dividend (F := F)) (x (F := F) + z (F := F))).isNone do
    throw (IO.userError "a nondivisor passed the exact product check")

/-- Exercise rejection of division by zero. -/
def runZeroDivisor {F : Type*} [Field F] [DecidableEq F] : IO Unit := do
  unless (exactQuotient? (dividend (F := F)) (0 : CMvPolynomial 3 F)).isNone do
    throw (IO.userError "division by zero was accepted")

/-- Run every executable exact-division test. -/
private def runExactSeven : IO Unit := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact runExact (F := ZMod 7)

private def runNoFuelSeven : IO Unit := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact runNoFuel (F := ZMod 7)

private def runNondivisorSeven : IO Unit := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact runNondivisor (F := ZMod 7)

private def runZeroDivisorSeven : IO Unit := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact runZeroDivisor (F := ZMod 7)

def run : IO Unit := do
  runExactSeven
  runNoFuelSeven
  runNondivisorSeven
  runZeroDivisorSeven

section

variable {F : Type*} [Field F] [DecidableEq F]

example (fuel : ℕ) (a b q : CMvPolynomial 4 F)
    (h : exactQuotientWithFuel? fuel a b = some q) : q * b = a :=
  exactQuotientWithFuel?_identity fuel a b q h

example (fuel : ℕ) (a b q expected : CMvPolynomial 4 F) (hb : b ≠ 0)
    (h : exactQuotientWithFuel? fuel a b = some q) (hexpected : expected * b = a) :
    q = expected :=
  quotient_eq_of_exactQuotientWithFuel?_eq_some fuel a b q expected hb h hexpected

example (fuel : ℕ) (a b q : CMvPolynomial 4 F) (ha : a ≠ 0)
    (h : exactQuotientWithFuel? fuel a b = some q) :
    (fromCMvPolynomial q).totalDegree ≤ (fromCMvPolynomial a).totalDegree :=
  totalDegree_quotient_le_of_exactQuotientWithFuel?_eq_some fuel a b q ha h

end

#print axioms exactQuotientWithFuel?_identity
#print axioms exactQuotient?_identity
#print axioms quotient_eq_of_exactQuotientWithFuel?_eq_some
#print axioms fromCMvPolynomial_dvd_of_exactQuotientWithFuel?_eq_some
#print axioms fromCMvPolynomial_dvd_of_exactQuotient?_eq_some
#print axioms totalDegree_quotient_le_of_exactQuotientWithFuel?_eq_some
#print axioms totalDegree_quotient_le_of_exactQuotient?_eq_some
#print axioms eval₂_mul_of_exactQuotientWithFuel?_eq_some
#print axioms eval₂_mul_of_exactQuotient?_eq_some

end CheckedExactDivisionTests
