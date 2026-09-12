/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Constructor
import Mathlib.Algebra.Field.ZMod

/-! The actual chart pipeline: nonidentity projection, ramified fiber, differential doubling,
denominator clearing, and global recovery. Global coverage is not asserted by this runtime test. -/

namespace FastTaylorConstructorTests

open CompPoly CPoly CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def equation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 - CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 2 - CMvPolynomial.X 0

private def component : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 0 ^ 2 - CMvPolynomial.X 1

/-- Apply the proved agreement identity to the computed chart's cleared coefficients. -/
example (chart : ChartData (ZMod 5) 2 4) {A : Type*} [CommRing A]
    (base : ZMod 5 →+* A) (point : Fin 3 → A) (coefficients : Fin 4 → A)
    (hclear : ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
      CMvPolynomial.eval₂ base point chart.denominator * coefficients j)
    (alpha received : ZMod 5) :
    CMvPolynomial.eval₂ base point (chart.agreement alpha received) =
      CMvPolynomial.eval₂ base point chart.denominator *
        ((∑ j : Fin 4, coefficients j * (base alpha - base chart.center) ^ j.val) -
          base received) :=
  chart.eval₂_agreement_of_cleared base point coefficients hclear alpha received

/-- Execute the full local-to-global chain with order two and a repeated constant fiber. -/
def run : IO Unit := do
  match construct? 5 2 4 2 0 equation component [0, 1, 2] with
  | none => throw (IO.userError "positive-order one-chart pipeline failed")
  | some chart =>
    unless chart.projection 0 2 == 1 && chart.projection 1 0 == 1 &&
        chart.projection 2 1 == 1 do
      throw (IO.userError "chart did not execute the expected nonidentity direction")
    unless constantFiber (fun _ => 0) chart.equation ==
        (CPolynomial.X : CPolynomial (ZMod 5)) ^ 2 do
      throw (IO.userError "chart lost the repeated constant fiber")
    unless chart.denominator == 1 do
      throw (IO.userError "unit-separant clearing changed the denominator")
    let expected : Fin 4 → CMvPolynomial 3 (ZMod 5) :=
      ![CMvPolynomial.X 2, CMvPolynomial.X 0, CMvPolynomial.X 1,
        CMvPolynomial.C 2 * (CMvPolynomial.C 2 * CMvPolynomial.X 2 * CMvPolynomial.X 0 +
          CMvPolynomial.C 2 * CMvPolynomial.X 1 + 1)]
    for j in List.finRange 4 do
      unless chart.numerators j == expected j do
        throw (IO.userError "recovered Taylor numerator mismatch")
    unless (chart.agreement 1 0).eval ![0, 0, 0] == 2 do
      throw (IO.userError "computed cleared agreement residual mismatch")
  let e0 : BoxAlgebra.Carrier 2 10 (ZMod 5) := BoxAlgebra.eps 0
  let e1 : BoxAlgebra.Carrier 2 10 (ZMod 5) := BoxAlgebra.eps 1
  let mixed := e0 ^ 9 * e1 ^ 9
  unless mixed != 0 && mixed * e0 == 0 && mixed * e1 == 0 do
    throw (IO.userError "mixed nilpotence near the parameter-kernel bound failed")

#print axioms ReedSolomon.HiddenDerivative.FastTaylor.Lifting.newton_positive_sound

end FastTaylorConstructorTests
