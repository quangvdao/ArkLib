/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryFinalization
import Mathlib.Algebra.Field.ZMod

/-! Actual ordinary finalization and the ordinary-lifting consumer boundary. -/

namespace CommonCenterOrdinaryFinalizationTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter
open OrdinaryFinalization

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def x : K := StoredField.ofPolynomial CPolynomial.X
private def y : CPolynomial K := CPolynomial.X
private def repeatedRational : CPolynomial K :=
  CPolynomial.C (x⁻¹) * (y - CPolynomial.C (x ^ 2)) ^ 2
private def unequal : CPolynomial K := y ^ 2 - CPolynomial.C (x ^ 3)
private def qx : CMvPolynomial 3 F := CMvPolynomial.X 0
private def qy : CMvPolynomial 3 F := CMvPolynomial.X 1
private def qz : CMvPolynomial 3 F := CMvPolynomial.X 2

/-- Exercise real denominators, repeated roots, unequal axes, inseparability, no-tail, and
both exceptional zero-input boundaries. -/
def runTests : IO Unit := do
  let cleared := ClearDenominators.clear repeatedRational
  unless cleared.scale != 1 && cleared.scale != 0 do
    throw (IO.userError "nontrivial denominator fixture was lost")
  match h : finalize 7 id repeatedRational with
  | .normalized data =>
    unless data.regular.natDegree == 1 &&
        (ClearDenominators.embed data.regular).eval (x ^ 2) == 0 do
      throw (IO.userError "rational repeated graph was not reduced correctly")
    unless guard repeatedRational (.normalized data) == cleared.scale * data.obstruction &&
        (guard repeatedRational (.normalized data)).eval 0 == 0 &&
        (guard repeatedRational (.normalized data)).eval 1 != 0 do
      throw (IO.userError "denominator-inclusive guard failed")
    let _ := normalizedInput 7 id repeatedRational data h
  | _ => throw (IO.userError "rational repeated graph did not normalize")
  match finalize 7 id unequal with
  | .normalized data =>
    unless data.regular.natDegree == 2 &&
        (ClearDenominators.embed data.regular).eval (x ^ 2) != 0 &&
        data.obstruction.eval 0 == 0 && data.obstruction.eval 1 != 0 do
      throw (IO.userError "unequal X/Y exponents or singular-center guard failed")
  | _ => throw (IO.userError "unequal-axis curve failed")
  match finalize (F := F) 7 id (y ^ 7 - CPolynomial.C x) with
  | .constantRegularPart data =>
    unless data.regular.natDegree == 0 do
      throw (IO.userError "inseparable no-graph branch retained Y")
  | _ => throw (IO.userError "inseparable no-graph branch failed")
  match finalize (F := F) 7 id 1 with
  | .constantRegularPart _ => pure ()
  | _ => throw (IO.userError "constant ordinary input failed")
  match finalize (F := F) 7 id 0 with
  | .zeroInput => pure ()
  | _ => throw (IO.userError "zero ordinary input failed")
  match run (F := F) 7 id ((qy - qx ^ 2) ^ 2 * (qz - 2 * qx) ^ 2) with
  | some (_, .normalized data) =>
    unless data.regular.natDegree == 1 &&
        (ClearDenominators.embed data.regular).eval (x ^ 2) == 0 do
      throw (IO.userError "actual supplied repeated-content ordinary output failed")
  | _ => throw (IO.userError "actual supplied equation did not normalize")
  match run (F := F) 7 id (qz - qy ^ 2) with
  | some (_, .constantRegularPart _) => pure ()
  | _ => throw (IO.userError "actual supplied no-tail branch failed")
  unless (run (F := F) 7 id 0).isNone do
    throw (IO.userError "zero supplied input failed")

/-- P4-shaped client: a raw ordinary graph reaches the actual output equation in CMv `[X,Y]`
coordinates, and the chosen guard value supplies the executed modular inverse for lifting. -/
example (raw : CPolynomial K) (data : OrdinaryNormalization.Data F)
    (hd : (ClearDenominators.clear raw).global.natDegree < 7)
    (hr : finalize 7 id raw = .normalized data) (P : Polynomial F)
    (hP : raw.toPoly.eval₂ StoredField.valueHom
      (algebraMap (Polynomial F) (RatFunc F) P) = 0)
    (a : F) (ha : (guard raw (finalize 7 id raw)).eval a ≠ 0) :
    MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
      (fromCMvPolynomial (CBivariate.toOrdinaryCMv data.regular)) = 0 ∧
    ∃ inverse, CPolynomial.inverseMod?
      (RegularCenterObstruction.fiber data.regular a).derivative
      (CPolynomial.monicNormalize (RegularCenterObstruction.fiber data.regular a)) =
        some inverse := by
  have hlaw : 7 ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a : F, id a ^ 7 = a := fun h => False.elim (Nat.not_le_of_lt hd h)
  constructor
  · rw [← BivariateReducedSupport.fromOrdinaryCMv_graph,
      BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv]
    exact (normalized_graph_iff 7 id raw hlaw data hr P).mpr hP
  · exact (normalized_fiber 7 id raw hlaw data hr a ha).monicInverse

#print axioms input_graph_iff
#print axioms finalize_nonzero
#print axioms guard_ne_zero
#print axioms ordinaryRoot_iff
#print axioms normalizedInput
#print axioms normalized_fiber
#print axioms run_exists_partition

end CommonCenterOrdinaryFinalizationTests

def main : IO Unit := do
  CommonCenterOrdinaryFinalizationTests.runTests
  IO.println "ordinary finalization: all branch and supplied-input tests passed"
