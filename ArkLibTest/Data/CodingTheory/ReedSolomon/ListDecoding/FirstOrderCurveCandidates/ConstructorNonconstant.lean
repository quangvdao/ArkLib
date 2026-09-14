/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorNonconstant
import Mathlib.Algebra.Field.ZMod

/-! Tests for nonconstancy derived from constructed chart coordinates. -/

namespace ConstructorNonconstantTest

open CompPoly CPoly CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorNonconstant

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def equation : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 0

private def component : CMvPolynomial 2 (ZMod 5) :=
  CMvPolynomial.X 1 - CMvPolynomial.X 0 ^ 2

-- The actual first-order constructor swaps the coordinates, yielding V² - U.
-- Its U = 0 fiber is ramified; both original initial coordinates are still
-- recovered from the literal numerator vector.
def run : IO Unit := do
  match construct? 5 1 3 2 0 equation component [0, 1, 2] with
  | none => throw (IO.userError "first-order chart construction failed")
  | some chart =>
    unless chart.projection 0 1 == 1 && chart.projection 1 0 == 1 do
      throw (IO.userError "expected swapped coordinates")
    unless constantFiber (fun _ => 0) chart.equation ==
        (CPolynomial.X : CPolynomial (ZMod 5)) ^ 2 do
      throw (IO.userError "ramified fiber changed")
    unless chart.denominator == 1 && chart.numerators 0 == CMvPolynomial.X 1 &&
        chart.numerators 1 == CMvPolynomial.X 0 do
      throw (IO.userError "actual initial-ratio identity failed")

example (c : ℚ) : (Polynomial.X : Polynomial ℚ) ≠ Polynomial.C c :=
  parameter_not_base Polynomial.C (RingHom.id _) Function.injective_id (fun _ => rfl) c

#print axioms construct_initial_numerator
#print axioms construct_coordinate_eq_sum_ratios
#print axioms construct_exists_ratio_not_base
#print axioms construct_message_not_base
#print axioms construct_centered_message_not_base
#print axioms construct_universal_card_le_pred

-- At center 2, ascending [3,1] means 3 + (X-2), hence descending [1,1].
example : Polynomial.CoefficientList.centeredToDescending (2 : ZMod 5) [3, 1] = [1, 1] := by
  decide

end ConstructorNonconstantTest

def constructorNonconstantStandaloneMain : IO Unit := ConstructorNonconstantTest.run
