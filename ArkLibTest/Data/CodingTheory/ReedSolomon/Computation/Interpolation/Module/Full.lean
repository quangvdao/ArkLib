/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Full
import Mathlib.Data.ZMod.Basic

/-!
# Full local interpolation module tests

Checks full-frame dimensions, Jordan actions, generator construction, and normalization against
an independent second-order coefficient oracle, including both linear and quadratic error terms.
-/

namespace ReedSolomon.HiddenDerivative.InterpolationFullModuleTests

open InterpolationModule

example : [0, 1, 0, 0] ∈ fullFrame 2 2 1 := by decide
example : (fullFrame 1 4 3).length = 40 := by decide
example : fullFrame 2 0 3 = [] := by decide
example : (jordanMatrix 3 (2 : ZMod 5)) = [[2, 0, 0], [1, 2, 0], [0, 1, 2]] := by decide

example {F : Type*} [CommRing F] {d : ℕ} (m : ℕ) (a : F)
    (P : LocalPolynomial F d) :
    restrict (fullJordan m a (extend (fun e => MvPolynomial.coeff (index e) P))) =
      jordan m a (fun e => MvPolynomial.coeff (index e) P) :=
  restrict_fullJordan m a P

private def matrixCheck {F : Type*} [CommRing F] [BEq F] (a : F) : IO Unit := do
  let v : List F := [1, 2, 3, 4]
  let rows := jordanMatrix 4 a
  for t in List.range 4 do
    let actual := ((rows.getD t []).zipWith (· * ·) v).sum
    let expected := fullJordan (d := 2) 4 a
      (fun e => v.getD (e none) 0) (frameQuery 2 [t, 1, 0, 0])
    unless actual == expected do throw (IO.userError "full Jordan matrix/action mismatch")
  -- This is a genuine full-module row outside the old low-contact domain.
  unless fullJordan (d := 2) 2 a (fun _ => 1) (frameQuery 2 [0, 1, 0, 0]) == a do
    throw (IO.userError "full module incorrectly applied the contact cutoff")

private def generatorCheck {F : Type*} [CommRing F] [BEq F] (a y : F) : IO Unit := do
  let b : JetMonomial := ⟨2, [1]⟩
  let some seed := (zeroColumn 1 4 a y b).1
    | throw (IO.userError "scalar seed failed")
  let some values := generator? 1 4 3 a y b
    | throw (IO.userError "full generator failed")
  unless values.length == 40 do throw (IO.userError "full generator dimension mismatch")
  let expected := fullSeed 1 4 3 seed
  unless values == expected do throw (IO.userError "full generator seed mismatch")
  unless values.any (· != 0) do throw (IO.userError "full generator unexpectedly empty")
  for row in fullFrame 1 4 3 do
    let q := frameQuery 1 row
    if q none < q (some none) then
      unless extend (denseCoordinates (d := 1) seed) q == 0 do
        throw (IO.userError "extra normalization row was nonzero")
  let some out := buildFull? 1 4 3 4 15 [(a, y), (a + 1, y + 1)] [b, ⟨0, [0]⟩]
    | throw (IO.userError "full interpolation instance failed")
  unless out.blocks.length == 20 && out.generators.length == 2 &&
      out.generators.all (fun v => v.length == 80) do
    throw (IO.userError "full interpolation instance dimensions mismatch")
  unless (buildFull? 1 4 1 4 15 [(a, y)] [b]).isNone do
    throw (IO.userError "out-of-degree monomial was accepted")

/-- Direct expansion of `(2 + T Y₁ - T² Y₂ + T³ V)²` over `ZMod 5`.
The error terms at degrees three and six distinguish the `d * u` normalization shift. -/
private def secondOrderCoefficient : List ℕ → ZMod 5
  | [0, 0, 0, 0] => 4
  | [1, 0, 1, 0] => 4
  | [2, 0, 0, 1] => 1
  | [3, 1, 0, 0] => 4
  | [2, 0, 2, 0] => 1
  | [4, 0, 0, 2] => 1
  | [6, 2, 0, 0] => 1
  | [3, 0, 1, 1] => 3
  | [4, 1, 1, 0] => 2
  | [5, 1, 0, 1] => 3
  | _ => 0

private def secondOrderGeneratorCheck : IO Unit := do
  let some values := generator? 2 7 2 (1 : ZMod 5) 2 ⟨2, [0, 0]⟩
    | throw (IO.userError "second-order generator failed")
  let rows := fullFrame 2 7 2
  unless values.length == 70 do
    throw (IO.userError "second-order generator dimension mismatch")
  unless values == rows.map secondOrderCoefficient do
    throw (IO.userError "second-order normalization coefficient mismatch")

/-- Runtime checks for full module rows, actual generators and the materialized Jordan action. -/
def run : IO Unit := do
  secondOrderGeneratorCheck
  matrixCheck (1 : ZMod 2)
  matrixCheck (2 : ZMod 5)
  generatorCheck (1 : ZMod 2) 1
  generatorCheck (2 : ZMod 5) 3
  unless fullFrame 2 0 3 == [] do throw (IO.userError "zero truncation frame was nonempty")
  IO.println "InterpolationFullModuleTests: passed"

end ReedSolomon.HiddenDerivative.InterpolationFullModuleTests
