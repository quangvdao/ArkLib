/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuardBounds
import Mathlib.Algebra.Field.ZMod

/-! Computed nested budgets on an unequal-axis equation with genuine coefficient poles. -/

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter
open EquationGuard

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def x : K := StoredField.ofPolynomial CPolynomial.X
private def y : CMvPolynomial 2 K := CMvPolynomial.X 0
private def z : CMvPolynomial 2 K := CMvPolynomial.X 1
private def curve : CMvPolynomial 2 K := (z - CMvPolynomial.C ((x - 5)⁻¹)) ^ 2 - y ^ 3

-- A downstream client consumes the actual guard without a desired-guard certificate.
example (c : Projection.Candidate K) (later : List (CPolynomial F)) :
    (run 7 id 1 c later).natDegree ≤
      (GuardAssembly.run 7 id 1 c []).natDegree + denominatorBudget c.equation +
        (later.map CPolynomial.natDegree).sum :=
  run_natDegree_le_budgets 7 id 1 c later

#print axioms denominatorBudget_eq_nested
#print axioms coefficientCount_eq_nested
#print axioms denominatorBudget_le_count_mul
#print axioms coefficientCount_le_rectangle
#print axioms run_eq_previous_mul
#print axioms run_natDegree_le_previous
#print axioms run_natDegree_le_budgets

/-- Degree accounting retains repeated poles and explicit later factors. -/
def main : IO Unit := do
  let some c := Projection.search 3 curve | throw (IO.userError "projection failed")
  unless coefficientCount c.equation == 6 && denominatorBudget c.equation == 3 do
    throw (IO.userError "sparse nested count or pole multiplicities changed")
  unless (GuardAssembly.run 7 id 1 c []).natDegree == 0 do
    throw (IO.userError "prior guard fixture changed")
  let later : List (CPolynomial F) := [CPolynomial.X - 2, CPolynomial.X - 2]
  let h := run 7 id 1 c later
  unless h.natDegree == 5 && h.eval 2 == 0 && h.eval 5 == 0 && h.eval 6 != 0 do
    throw (IO.userError "actual guard lost repeated later factors or equation poles")
  unless h == GuardAssembly.run 7 id 1 c later * (coefficientFactors c.equation).prod do
    throw (IO.userError "prior guard factorization failed")
  unless denominatorBudget (0 : CBivariate K) == 0 && coefficientCount (0 : CBivariate K) == 0 do
    throw (IO.userError "zero equation budget was nonzero")
  unless (run 7 id 1 c [0]).natDegree == 0 do
    throw (IO.userError "zero later factor did not annihilate actual guard")
  IO.println "equation guard budgets: nested counts, repeated poles, later factors passed"
