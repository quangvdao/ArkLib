/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.CenterDispatcher

/-! Branch and arithmetic checks for the executed center constructor. -/

namespace CenterDispatcherTests

open ArkLib.FiniteField.ExplicitConstruction

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : (centerDispatch 2 2).branch = .prime :=
  (centerDispatch_prime_iff _ _).mpr (by decide)

example : (centerDispatch 5 25).branch = .quadratic :=
  (centerDispatch_quadratic_iff _ _).mpr (by decide)

example (data : QuadraticCenters 5 25) : data.centers.Nodup := data.prefix_nodup

example (data : QuadraticCenters 5 25) : CharP data.FieldType 5 := inferInstance

example (data : QuadraticCenters 5 25) : DecidableEq data.FieldType := inferInstance

example (data : QuadraticCenters 5 25) : LawfulBEq data.FieldType := inferInstance

/-- Exercise every outcome, exact capacity boundaries and returned field arithmetic. -/
def run : IO Unit := do
  for count in [0, 1, 2] do
    unless (centerDispatch 2 count).branch == .prime do
      throw (IO.userError "sufficient characteristic-two prime branch was rejected")
    unless (primeCenterPrefix 2 count).length == count &&
        decide (primeCenterPrefix 2 count).Nodup do
      throw (IO.userError "prime center prefix failed zero/one/full boundary")
  unless (centerDispatch 2 3).branch == .unsupportedCharacteristic do
    throw (IO.userError "insufficient characteristic-two branch was not explicit")
  unless (centerDispatch 5 5).branch == .prime do
    throw (IO.userError "exact prime capacity triggered unnecessary quadratic search")
  unless (centerDispatch 5 26).branch == .insufficientCapacity do
    throw (IO.userError "quadratic capacity plus one did not reject")
  match centerDispatch 5 7 with
  | .quadratic data =>
      unless data.parameter == (2 : ZMod 5) do
        throw (IO.userError "dispatcher did not retain the first Euler parameter")
      unless data.centers.length == 7 && decide data.centers.Nodup do
        throw (IO.userError "returned quadratic prefix is not exactly seven distinct entries")
      unless (data.centers[5]?).map QuadraticAlgebra.re == some (0 : ZMod 5) &&
          (data.centers[5]?).map QuadraticAlgebra.im == some (1 : ZMod 5) do
        throw (IO.userError "returned prefix did not cross the prime-field boundary")
      for i in List.finRange 25 do
        let value := data.indexEquiv i
        unless data.indexEquiv.symm value == i do
          throw (IO.userError "computed quadratic radix index did not round-trip")
      let w : data.FieldType := ⟨0, 1⟩
      unless decide (w ^ 2 = data.embedding data.parameter ∧
          (w + 1) * (w + 1)⁻¹ = 1 ∧ data.embedding 3 + data.embedding 4 = data.embedding 2) do
        throw (IO.userError "returned field arithmetic or embedding failed")
  | _ => throw (IO.userError "genuinely required quadratic construction did not run")
  match centerDispatch 5 25 with
  | .quadratic data =>
      unless data.centers.length == 25 && decide data.centers.Nodup do
        throw (IO.userError "full quadratic cardinality prefix is not distinct")
  | _ => throw (IO.userError "exact quadratic capacity was rejected")

#print axioms ArkLib.FiniteField.ExplicitConstruction.centerDispatch_parameter
#print axioms ArkLib.FiniteField.ExplicitConstruction.centerDispatch_supported
#print axioms ArkLib.FiniteField.ExplicitConstruction.QuadraticCenters.cardinality
#print axioms ArkLib.FiniteField.ExplicitConstruction.QuadraticCenters.prefix_nodup

end CenterDispatcherTests
