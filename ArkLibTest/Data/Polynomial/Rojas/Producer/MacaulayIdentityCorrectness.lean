/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayIdentityCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and executable checks for Canny's Macaulay determinant
specialization and the empty-minor success branch. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayIdentityCorrectnessTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private def linearThree : Fin 3 → CMvPolynomial 3 F
  | 0 => X 0 + X 1 + 1
  | 1 => X 1 + X 2 + 2
  | 2 => X 2 - X 0 + 3

example : extraneousFactor twoRoots ≠ 0 :=
  extraneousFactor_ne_zero twoRoots

example {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hindices : extraneousIndices system = []) :
    macaulayQuotient? system = some (characteristic system) :=
  macaulayQuotient?_eq_some_characteristic_of_extraneousIndices_eq_nil
    system hindices

def main : IO Unit := do
  unless (extraneousIndices twoRoots).length == 1 do
    throw <| IO.userError "expected a nonempty bivariate extraneous minor"
  unless extraneousFactor twoRoots != 0 do
    throw <| IO.userError "Canny specialization failed to witness nonvanishing"
  unless extraneousIndices linearThree == [] do
    throw <| IO.userError "all-linear three-variable system had an extraneous row"
  unless macaulayQuotient? linearThree == some (characteristic linearThree) do
    throw <| IO.userError "empty-minor executable quotient did not return determinant"
  IO.println "Rojas Macaulay identity: nonvanishing and empty-minor success passed"

#print axioms cannyParameterEval_matrix
#print axioms cannyParameterEval_extraneousFactor
#print axioms extraneousFactor_ne_zero
#print axioms extraneousFactor_eq_one_of_extraneousIndices_eq_nil
#print axioms extraneousFactor_dvd_characteristic_of_extraneousIndices_eq_nil
#print axioms macaulayQuotient?_eq_some_characteristic_of_extraneousIndices_eq_nil

end RojasMacaulayIdentityCorrectnessTests

def main : IO Unit := RojasMacaulayIdentityCorrectnessTests.main
