/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.Padding

/-! Regression checks for square padding and dummy-label rejection. -/

namespace GabberGalilPaddingTest

open GabberGalil

example : ceilSqrt 0 = 0 := by decide
example : ceilSqrt 1 = 1 := by decide
example : ceilSqrt 5 = 3 := by decide +kernel
example : paddedSize 5 = 9 := by decide +kernel
example : 5 ≤ paddedSize 5 ∧ paddedSize 5 ≤ 4 * 5 := padding_bounds (by omega)

/-- Decode every real label and reject each of the four dummy vertices for `n=5`. -/
def run : IO Unit := do
  let decoded := (List.ofFn fun j : Fin 9 ↦
    unpad? (n := 5) (squareVertexEquiv 3 j))
  unless decoded.take 5 == (List.ofFn fun i : Fin 5 ↦ some i) do
    throw <| IO.userError "real position failed its padding round trip"
  unless (decoded.drop 5).all Option.isNone do
    throw <| IO.userError "dummy square vertex was accepted as a received label"
  unless decoded.length == 9 do
    throw <| IO.userError "ceil-sqrt square has the wrong size"
  IO.println "Gabber–Galil padding: 5 real labels and 4 dummy rejections passed"

end GabberGalilPaddingTest
