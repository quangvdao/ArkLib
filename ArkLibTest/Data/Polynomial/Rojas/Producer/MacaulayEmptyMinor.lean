/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayEmptyMinor
import Mathlib.Algebra.Field.ZMod

/-! Input-only total quotient checks, including zero, inseparable, and dependent inputs. -/

namespace RojasMacaulayEmptyMinorTests

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay ArkLib.Rojas.Producer.MacaulayQuotient

abbrev F := ZMod 3
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def inseparable : Fin 1 → CMvPolynomial 1 F := fun _ ↦ X 0 ^ 3 - 1
private def dependentLinear : Fin 2 → CMvPolynomial 2 F := fun _ ↦ X 0 + X 1 + 1
private def nonlinear : Fin 2 → CMvPolynomial 2 F := ![X 0 ^ 2 - 1, X 1 - X 0]

/-- Arbitrary coefficients and degree need no geometric hypothesis in dimension one. -/
example {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
    (system : Fin 1 → CMvPolynomial 1 K) :
    macaulayQuotient? system = some (characteristic system) :=
  macaulayQuotient?_eq_some_characteristic_univariate system

/-- The zero-variable boundary is included in the affine-linear theorem. -/
example (system : Fin 0 → CMvPolynomial 0 F) :
    macaulayQuotient? system = some (characteristic system) :=
  macaulayQuotient?_eq_some_characteristic_of_totalDegree_le_one system (fun i ↦ i.elim0)

example : macaulayQuotient? inseparable = some (characteristic inseparable) :=
  macaulayQuotient?_eq_some_characteristic_univariate inseparable

example : macaulayQuotient? dependentLinear = some (characteristic dependentLinear) :=
  macaulayQuotient?_eq_some_characteristic_of_totalDegree_le_one dependentLinear (by
    intro i
    simp only [dependentLinear]
    decide +kernel)

/-- Degree two in two variables escapes the proved empty-minor branch. -/
example : extraneousIndices nonlinear ≠ [] := by decide +kernel
example : extraneousFactor nonlinear ≠ 1 := by decide +kernel

/-- Execute total division on degenerate inputs and a genuine nonempty-minor control. -/
def main : IO Unit := do
  let unaryInputs : List (Fin 1 → CMvPolynomial 1 F) :=
    [fun _ ↦ 0, fun _ ↦ 1, inseparable, fun _ ↦ X 0 ^ 4 + X 0 + 1]
  for system in unaryInputs do
    unless extraneousIndices system == [] && extraneousFactor system == 1 do
      throw <| IO.userError "univariate input acquired an extraneous factor"
    unless macaulayQuotient? system == some (characteristic system) do
      throw <| IO.userError "univariate checked division failed"
  let zeroSystem : Fin 2 → CMvPolynomial 2 F := fun _ ↦ 0
  for system in [zeroSystem, dependentLinear] do
    unless extraneousIndices system == [] &&
        macaulayQuotient? system == some (characteristic system) do
      throw <| IO.userError "degenerate affine-linear input failed total division"
  unless extraneousIndices nonlinear != [] && extraneousFactor nonlinear != 1 do
    throw <| IO.userError "nonlinear control stopped exercising a genuine minor"
  IO.println "Macaulay empty minor: unary degrees, zero and dependent linear inputs passed"

#print axioms extraneousIndices_eq_nil_of_totalDegree_le_one
#print axioms extraneousIndices_eq_nil_univariate
#print axioms macaulayQuotient?_eq_some_characteristic_of_totalDegree_le_one
#print axioms macaulayQuotient?_eq_some_characteristic_univariate

end RojasMacaulayEmptyMinorTests

def main : IO Unit := RojasMacaulayEmptyMinorTests.main
