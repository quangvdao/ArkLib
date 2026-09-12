/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.OddCenters
import ArkLib.Data.FiniteField.ExplicitConstruction.CenterDispatcher

/-! Test actual-cardinality Euler search over a nonprime current field and its extension. -/

namespace OddCenterTests
open ArkLib.FiniteField.ExplicitConstruction

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Build F9 with the earlier computed center constructor, then extend this current field
rather than restarting over F3. The supplied-polynomial adapter has separate acceptance tests. -/
def run : IO Unit := do
  match centerDispatch 3 4 with
  | .quadratic base =>
      let index := base.indexEquiv
      have hodd : ringChar base.FieldType ≠ 2 := by rw [ringChar.eq _ 3]; decide
      unless (OddCenters.run 9 4 index hodd).branch == .base do
        throw (IO.userError "nonprime base field was mistaken for its prime subfield")
      unless (indexedPrefix index 4 (by decide)).length == 4 &&
          decide (indexedPrefix index 4 (by decide)).Nodup do
        throw (IO.userError "base coordinate prefix failed above the characteristic")
      unless OddCenters.eulerTest 9 (1 : base.FieldType) == false do
        throw (IO.userError "Euler scan accepted the square one")
      match OddCenters.run 9 10 index hodd with
      | .quadratic extension =>
          unless extension.parameter == (⟨1, 1⟩ : base.FieldType) do
            throw (IO.userError "actual F9 Euler scan did not find the first nonsquare")
          let centers := extension.centers index
          unless centers.length == 10 && decide centers.Nodup do
            throw (IO.userError "F81 requested prefix is not distinct")
          unless (centers[9]?).map QuadraticAlgebra.re == some (0 : base.FieldType) &&
              (centers[9]?).map QuadraticAlgebra.im == some (1 : base.FieldType) do
            throw (IO.userError "quadratic prefix failed to cross the current F9 boundary")
          let w : extension.FieldType := ⟨0, 1⟩
          unless decide (w ^ 2 = extension.embedding extension.parameter ∧
              (w + 1) * (w + 1)⁻¹ = 1) do
            throw (IO.userError "field operations over the nonprime base failed")
      | _ => throw (IO.userError "required extension of the actual F9 was not constructed")
      match OddCenters.run 9 81 index hodd with
      | .quadratic extension =>
          unless (extension.centers index).length == 81 && decide (extension.centers index).Nodup do
            throw (IO.userError "full F81 coordinate prefix failed")
      | _ => throw (IO.userError "exact quadratic capacity was rejected")
      unless (OddCenters.run 9 82 index hodd).branch == .insufficientCapacity do
        throw (IO.userError "capacity plus one was not explicitly rejected")
  | _ => throw (IO.userError "test did not construct its nonprime current field")

#print axioms OddCenters.nonsquare?_ne_none
#print axioms OddCenters.run_parameter
#print axioms OddCenters.QuadraticData.cardinality

end OddCenterTests
