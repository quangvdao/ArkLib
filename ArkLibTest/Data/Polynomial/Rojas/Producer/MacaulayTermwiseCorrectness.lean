/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayTermwiseCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and executable checks for termwise Macaulay divisibility. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayTermwiseCorrectnessTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

example {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system) :
    extraneousFactor system ∣ characteristic system :=
  extraneousFactor_dvd_characteristic_of_determinantProductsDivisible
    system htermwise

example {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system) :
    ∃ quotient ≠ 0, macaulayQuotient? system = some quotient :=
  exists_ne_zero_macaulayQuotient?_eq_some_of_determinantProductsDivisible
    system htermwise

def main : IO Unit := do
  unless (extraneousIndices twoRoots).length == 1 do
    throw <| IO.userError "termwise branch did not exercise a nonempty minor"
  unless determinantProductsDivisibleB twoRoots do
    throw <| IO.userError "Leibniz products failed checked extraneous division"
  match macaulayQuotient? twoRoots with
  | none => throw <| IO.userError "termwise branch did not produce a quotient"
  | some quotient =>
      unless quotient != 0 do
        throw <| IO.userError "termwise branch accepted the spurious zero quotient"
      unless quotient * extraneousFactor twoRoots = characteristic twoRoots do
        throw <| IO.userError "termwise branch quotient failed its product certificate"
  IO.println "Rojas Macaulay termwise branch: nonempty minor and quotient passed"

#print axioms extraneousFactor_dvd_determinantProduct
#print axioms extraneousFactor_dvd_characteristic_of_determinantProductsDivisible
#print axioms macaulayQuotient?_isSome_of_determinantProductsDivisible
#print axioms exists_ne_zero_macaulayQuotient?_eq_some_of_determinantProductsDivisible

end RojasMacaulayTermwiseCorrectnessTests

def rojasMacaulayTermwiseCorrectnessStandaloneMain : IO Unit :=
  RojasMacaulayTermwiseCorrectnessTests.main
