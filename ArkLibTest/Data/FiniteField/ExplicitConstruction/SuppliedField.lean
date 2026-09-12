/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
import ArkLib.Data.FiniteField.ExplicitConstruction.CenterDispatcher

/-! Runtime checks for prefix boundaries and the low-digit convention of quadratic coordinates. -/

namespace SuppliedFieldTests
open ArkLib.FiniteField.ExplicitConstruction

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def run : IO Unit := do
  let index := primeCenterIndex 3
  unless indexedPrefix index 0 (by decide) == [] &&
      indexedPrefix index 1 (by decide) == [0] &&
      indexedPrefix index 3 (by decide) == [0, 1, 2] do
    throw (IO.userError "prefix endpoints did not preserve coordinate order")
  let quadratic := quadraticIndex index (2 : ZMod 3) 0
  let values := indexedPrefix quadratic 9 (by decide)
  unless values.map QuadraticAlgebra.re == [0, 1, 2, 0, 1, 2, 0, 1, 2] &&
      values.map QuadraticAlgebra.im == [0, 0, 0, 1, 1, 1, 2, 2, 2] do
    throw (IO.userError "quadratic coordinates did not use the real low radix digit")
  unless decide values.Nodup do
    throw (IO.userError "full quadratic coordinate prefix contained duplicates")
  for i in List.finRange 9 do
    unless quadratic.symm (quadratic i) == i do
      throw (IO.userError "quadratic coordinate encoding failed to round trip")

#print axioms indexedPrefix_nodup
#print axioms quadraticIndex_cardinality

end SuppliedFieldTests
