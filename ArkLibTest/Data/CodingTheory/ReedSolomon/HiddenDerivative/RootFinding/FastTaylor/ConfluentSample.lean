/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ConfluentSample
import Mathlib.Algebra.Field.ZMod

/-! Actual resultant selection retains repeated fibers and lifts a nonconstant separant inverse. -/

open CPoly CPoly.CMvPolynomial CPoly.TaylorReconstruction CompPoly ArkLib.ConfluentAlgebra
open ReedSolomon.HiddenDerivative.FastTaylor.ConfluentSample

namespace ConfluentSampleTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (0 < 2) := ⟨by decide⟩
private def h : CMvPolynomial 2 (ZMod 5) :=
  flattenLast (CPolynomial.X ^ 2 - CPolynomial.C (X 0))
private def s : CMvPolynomial 2 (ZMod 5) := 1 + X 1
private instance : Fact (splitLast h).monic := ⟨by
  rw [h, splitLast_flattenLast, CPolynomial.monic_toPoly_iff]
  simp only [CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_sub_C _ (by decide)⟩
private def zeroSample : Fin 1 → ZMod 5 := fun _ => 0

example (ha : select? h s [1, 0] = some zeroSample)
    (hb : 0 < (splitLast h).natDegree) : ∃ b, inverseAt? 2 h s zeroSample = some b :=
  inverseAt?_exists 2 h s [1, 0] zeroSample ha hb

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- Execute obstruction computation, first-point selection and the full quotient inverse. -/
def run : IO Unit := do
  check "actual separant resultant" <| obstruction h s == (1 - X 0 : CMvPolynomial 1 (ZMod 5))
  let some a := select? h s [1, 0] | throw (IO.userError "good repeated fiber not found")
  check "first point is rejected and second point selected" <| a 0 == 0
  check "selected constant fiber really has repeated roots" <|
    constantFiber a h == (CPolynomial.X ^ 2 : CPolynomial (ZMod 5))
  let some b := inverseAt? 2 h s a | throw (IO.userError "unit separant rejected")
  check "computed inverse is two-sided in the nonreduced quotient" <|
    localSeparant 2 h s a * b == 1 && b * localSeparant 2 h s a == 1
  let bad : Fin 1 → ZMod 5 := fun _ => 1
  check "nonunit specialization is rejected" <| (inverseAt? 2 h s bad).isNone
  check "exhausted grid is distinct from an inverse result" <| (select? h s [1]).isNone
  check "zero resultant is rejected" <| (select? h h [0, 1, 2]).isNone

end ConfluentSampleTests
