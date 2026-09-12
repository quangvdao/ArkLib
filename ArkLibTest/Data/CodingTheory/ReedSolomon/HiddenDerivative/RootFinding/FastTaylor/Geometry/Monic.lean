/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Geometry.Monic
import Mathlib.Algebra.Field.ZMod

/-! Nonidentity projection, unequal parameter/final degrees, and exact characteristic-two data. -/

namespace MonicProjectionTests
open CPoly CPoly.CMvPolynomial CPoly.TaylorReconstruction CompPoly
open ReedSolomon.HiddenDerivative.FastTaylor.Geometry.MonicProjection

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example (p : CMvPolynomial 2 ℚ) (values : List ℚ) (d : Data 1 ℚ)
    (hd : construct? p values = some d) : (splitLast d.polynomial).monic :=
  (construct?_sound p values d hd).2.2.2.2.1

/-- Execute normalization and reduction on a coordinate swap with a nontrivial leading scalar. -/
def run : IO Unit := do
  let p : CMvPolynomial 2 ℚ := 2 * X 0 ^ 2 + X 0 * X 1 + X 1 + 7
  let some d := construct? p [0, 1, 2] | throw (IO.userError "monic chart construction failed")
  unless decide (d.direction = ![1, 0]) && decide (d.forward != 1) do
    throw (IO.userError "test did not execute a nonidentity coordinate change")
  let t : CMvPolynomial 2 ℚ := X 0
  let z : CMvPolynomial 2 ℚ := X 1
  unless d.polynomial == z ^ 2 + C (1 / 2) * t * z + C (1 / 2) * t + C (7 / 2) do
    throw (IO.userError "normalization used an incorrect leading scalar or coordinate order")
  let h := splitLast d.polynomial
  unless h.monic && h.natDegree == 2 && h.coeff 2 == 1 &&
      h.coeff 1 == C (1 / 2) * X 0 && h.coeff 0 == C (1 / 2) * X 0 + C (7 / 2) do
    throw (IO.userError "monic projection has incorrect coefficient degrees")
  let f := z ^ 3
  let rem := flattenLast ((splitLast f).modByMonic h)
  unless rem.totalDegree ≤ f.totalDegree && (splitLast rem).natDegree < 2 do
    throw (IO.userError "monic reduction increased degree")
  let finite : CMvPolynomial 2 (ZMod 2) := X 0 ^ 2 - X 0 + X 1
  let some df := construct? finite [0, 1] |
    throw (IO.userError "characteristic-two polynomial data was lost")
  unless (splitLast df.polynomial).monic && (splitLast df.polynomial).natDegree == 2 do
    throw (IO.userError "characteristic-two exact degree collapsed to its evaluation function")
  let some dc := construct? (C 3 : CMvPolynomial 1 ℚ) [2] |
    throw (IO.userError "nonzero constant projection failed")
  unless dc.polynomial == 1 && (splitLast dc.polynomial).natDegree == 0 do
    throw (IO.userError "constant normalization failed")
  unless (construct? (0 : CMvPolynomial 1 ℚ) [0, 1]).isNone do
    throw (IO.userError "zero input produced a monic chart")

end MonicProjectionTests
