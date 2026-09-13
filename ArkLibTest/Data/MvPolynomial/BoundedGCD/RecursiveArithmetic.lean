/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.Recursive
import Mathlib.Algebra.Field.ZMod

/-! Runtime and proof-level tests for recursive stored polynomial arithmetic. -/

namespace RecursiveArithmeticTests

open CompPoly CPoly
open CPoly.CMvPolynomial.BoundedGCD
open ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

private def x₂ : CMvPolynomial 2 E := CMvPolynomial.X 0
private def y₂ : CMvPolynomial 2 E := CMvPolynomial.X 1

private def common₂ : CMvPolynomial 2 E := (x₂ + 1) * (y₂ + 1)
private def left₂ : CMvPolynomial 2 E := common₂ * (y₂ + x₂) ^ 2
private def right₂ : CMvPolynomial 2 E := common₂ * (y₂ + 2)

private def x₃ : CMvPolynomial 3 E := CMvPolynomial.X 0
private def y₃ : CMvPolynomial 3 E := CMvPolynomial.X 1
private def z₃ : CMvPolynomial 3 E := CMvPolynomial.X 2

private def common₃ : CMvPolynomial 3 E := (x₃ + y₃ + 1) * (z₃ + 1)
private def left₃ : CMvPolynomial 3 E := common₃ * (z₃ + x₃) * (y₃ + 2)
private def right₃ : CMvPolynomial 3 E := common₃ * (z₃ + y₃) ^ 2

/-- A three-jet fixture with coefficient content, a repeated factor, two retained factors, and
an ambient independent variable omitted before initial specialization. -/
private def initialFixture : CMvPolynomial 3 E :=
  let a := CMvPolynomial.X 0
  let b := CMvPolynomial.X 1
  let z := CMvPolynomial.X 2
  (a + b + 1) * (z - a) ^ 2 * (z + b) * (z - 1)

private def ambientFixture : CMvPolynomial 4 E :=
  CMvPolynomial.rename Fin.succ initialFixture

private def expectedRegular : CMvPolynomial 3 E :=
  let b := CMvPolynomial.X 1
  let z := CMvPolynomial.X 2
  (z + b) * (z - 1)

/-- Exercise exact division and gcd at two and three coefficient-variable levels, then the
actual `General.runInitial?` adapter at order two. -/
def run : IO Unit := do
  let coefficientX : CMvPolynomial 1 E := CMvPolynomial.X 0
  let nestedDivisor : CPolynomial (CMvPolynomial 1 E) :=
    CPolynomial.C (coefficientX + 1) * CPolynomial.X + CPolynomial.C coefficientX
  let nestedExpected : CPolynomial (CMvPolynomial 1 E) :=
    CPolynomial.C (coefficientX + 2) * CPolynomial.X + 1
  let nestedDividend := nestedExpected * nestedDivisor
  let some nestedQuotient := RecursiveArithmetic.pseudoExactQuotient?
      (RecursiveArithmetic.divide 1) nestedDividend nestedDivisor
    | throw (IO.userError "fraction-free exact division failed on a nonunit leading coefficient")
  unless nestedQuotient * nestedDivisor == nestedDividend do
    throw (IO.userError "fraction-free exact division reconstructed the wrong polynomial")
  let gcd₂ := RecursiveArithmetic.gcd 2 left₂ right₂
  let some leftQuotient₂ := RecursiveArithmetic.divide 2 left₂ gcd₂
    | throw (IO.userError "the two-variable gcd did not divide the left input")
  unless leftQuotient₂ * gcd₂ == left₂ do
    throw (IO.userError "two-variable exact division reconstructed the wrong left input")
  let some rightQuotient₂ := RecursiveArithmetic.divide 2 right₂ gcd₂
    | throw (IO.userError "the two-variable gcd did not divide the right input")
  unless rightQuotient₂ * gcd₂ == right₂ do
    throw (IO.userError "two-variable exact division reconstructed the wrong right input")
  let some commonQuotient₂ := RecursiveArithmetic.divide 2 gcd₂ common₂
    | throw (IO.userError "the two-variable gcd lost nonconstant coefficient content")
  unless commonQuotient₂ * common₂ == gcd₂ do
    throw (IO.userError "the two-variable common factor reconstruction failed")
  let gcd₃ := RecursiveArithmetic.gcd 3 left₃ right₃
  let some leftQuotient₃ := RecursiveArithmetic.divide 3 left₃ gcd₃
    | throw (IO.userError "the three-variable gcd did not divide the left input")
  unless leftQuotient₃ * gcd₃ == left₃ do
    throw (IO.userError "three-variable exact division reconstructed the wrong left input")
  let some rightQuotient₃ := RecursiveArithmetic.divide 3 right₃ gcd₃
    | throw (IO.userError "the three-variable gcd did not divide the right input")
  unless rightQuotient₃ * gcd₃ == right₃ do
    throw (IO.userError "three-variable exact division reconstructed the wrong right input")
  let some commonQuotient₃ := RecursiveArithmetic.divide 3 gcd₃ common₃
    | throw (IO.userError "the three-variable gcd lost mixed coefficient content")
  unless commonQuotient₃ * common₃ == gcd₃ do
    throw (IO.userError "the three-variable common factor reconstruction failed")
  let some data :=
      ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.RecursiveArithmetic.runInitial?
        3 ambientFixture
    | throw (IO.userError "the concrete recursive General.runInitial? adapter failed")
  unless General.component data == expectedRegular do
    throw (IO.userError "the repeated/separant pipeline returned the wrong regular component")

example (n : ℕ) :
    CoefficientNormalization.GcdLaws (RecursiveArithmetic.gcd (E := E) n) :=
  RecursiveArithmetic.gcd_laws n

example (n : ℕ) :
    CoefficientNormalization.DivideLaws (RecursiveArithmetic.divide (E := E) n) :=
  RecursiveArithmetic.divide_laws n

#print axioms RecursiveArithmetic.gcd_laws
#print axioms RecursiveArithmetic.divide_laws
#print axioms General.runInitial?_exists_certificate

end RecursiveArithmeticTests
