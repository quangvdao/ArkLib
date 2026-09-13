/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryDegreeBounds
import Mathlib.Algebra.Field.ZMod

/-! Unequal-axis, content, clearing, and supplied-bound consumer canaries. -/

namespace CommonCenterOrdinaryDegreeBoundsTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter
open OrdinaryDegreeBounds

private abbrev F := ZMod 37
private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def qx : CMvPolynomial 3 F := CMvPolynomial.X 0
private def qy : CMvPolynomial 3 F := CMvPolynomial.X 1
private def qz : CMvPolynomial 3 F := CMvPolynomial.X 2
private def unequal : CMvPolynomial 3 F := qz ^ 2 - qx ^ 5 * qy ^ 3
private def content : CMvPolynomial 3 F := (qy - qx ^ 2) ^ 3 * (qz - 2 * qx) ^ 2
private def x : K := StoredField.ofPolynomial CPolynomial.X
private def y : CPolynomial K := CPolynomial.X
private def rational : CPolynomial K :=
  CPolynomial.C (x⁻¹) * y ^ 2 + CPolynomial.C ((x + 1)⁻¹) * y + 1

/-- Run the actual conversion, state preparation, clearing, and ordinary finalization. -/
def runTests : IO Unit := do
  unless unequal.degreeOf 0 == 5 && unequal.degreeOf 1 == 3 && unequal.degreeOf 2 == 2 do
    throw (IO.userError "unequal supplied axes changed")
  unless (SuppliedInput.equation unequal).natDegree == 2 &&
      (ClearDenominators.primitivePart (SuppliedInput.equation content)).natDegree == 2 do
    throw (IO.userError "state degree or primitive content removal changed")
  match SuppliedInput.run 37 unequal with
  | .prepared tail =>
    unless tail.ordinary.natDegree == 3 &&
        (ClearDenominators.clear tail.ordinary).global.natDegree == 3 do
      throw (IO.userError "resultant ordinary message degree or clearing degree changed")
  | _ => throw (IO.userError "unequal-axis preparation failed")
  match SuppliedInput.run 37 content with
  | .prepared tail =>
    unless tail.ordinary.natDegree == 3 do
      throw (IO.userError "message content multiplicity was not included in the degree")
  | _ => throw (IO.userError "content preparation failed")
  let cleared := ClearDenominators.clear rational
  unless cleared.global.natDegree == rational.natDegree && cleared.scale.natDegree == 2 do
    throw (IO.userError "canonical denominators changed message degree or scale degree")
  match OrdinaryFinalization.run 37 id unequal with
  | some (_, .normalized data) =>
    unless data.regular.natDegree == 1 do
      throw (IO.userError "final radical did not remove ordinary repetitions")
  | _ => throw (IO.userError "actual bounded supplied-input finalization failed")
  unless (SuppliedInput.equation (0 : CMvPolynomial 3 F)).natDegree == 0 do
    throw (IO.userError "zero polynomial degree convention changed")

/-- A downstream caller supplies only the actual equation: its source-axis inequalities are
computed, and all internal state and ordinary degree hypotheses are discharged by the producer. -/
example : ∃ tail result, OrdinaryFinalization.run 37 id unequal = some (tail, result) ∧
    tail.ordinary ≠ 0 ∧
    OrdinaryNormalizationCorrectness.CorrectOutcome (OrdinaryFinalization.input tail.ordinary)
      result ∧ OrdinaryFinalization.guard tail.ordinary result ≠ 0 := by
  exact run_exists_of_axes 37 unequal (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The paper cutoff also elaborates directly from a concrete sparse equation. -/
example : ∃ tail result, OrdinaryFinalization.run 37 id (qz - qy + qx ^ 5) =
      some (tail, result) ∧ tail.ordinary ≠ 0 ∧
    OrdinaryNormalizationCorrectness.CorrectOutcome (OrdinaryFinalization.input tail.ordinary)
      result ∧ OrdinaryFinalization.guard tail.ordinary result ≠ 0 := by
  exact run_exists_of_kappa 37 (qz - qy + qx ^ 5) (by decide +kernel) 1
    (by decide +kernel) (by decide +kernel) (by decide)

#print axioms run_exists_of_kappa
#print axioms final_guard_input_natDegree_le
#print axioms equation_natDegree_le
#print axioms equation_degreeX_le
#print axioms primitive_equation_natDegree_le
#print axioms clear_global_natDegree
#print axioms finish_ordinary_natDegree_le
#print axioms supplied_ordinary_natDegree_le
#print axioms run_exists_partition_of_axes
#print axioms clearing_scale_natDegree_le
#print axioms guard_input_natDegree_le

end CommonCenterOrdinaryDegreeBoundsTests

def main : IO Unit := do
  CommonCenterOrdinaryDegreeBoundsTests.runTests
  IO.println "ordinary degree bounds: supplied axes, content, clearing, and finalization passed"
