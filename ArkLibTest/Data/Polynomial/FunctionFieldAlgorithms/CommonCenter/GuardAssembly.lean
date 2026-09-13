/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.GuardAssembly
import Mathlib.Algebra.Field.ZMod

/-! Actual rational projection factors and distinct bad-center causes. -/

namespace CommonCenterGuardAssemblyTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter
open GuardAssembly

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def x : K := StoredField.ofPolynomial CPolynomial.X
private def y : CMvPolynomial 2 K := CMvPolynomial.X 0
private def z : CMvPolynomial 2 K := CMvPolynomial.X 1
private def curve : CMvPolynomial 2 K :=
  CMvPolynomial.C (x / (x - 1)) * (z ^ 2 - y ^ 2) - 1
private def ordinary : CPolynomial K := CPolynomial.X ^ 2 - CPolynomial.C (x - 3)
private def laterFactor : CPolynomial F := CPolynomial.X - 2

/-- The guard keeps challenge denominators separate from the projection-coordinate discriminant. -/
def runTests : IO Unit := do
  let some c := Projection.search 2 curve | throw (IO.userError "rational projection failed")
  unless c.slope == 0 && c.discriminant.natDegree == 2 do
    throw (IO.userError "projection-coordinate fixture changed")
  let later := [laterFactor, laterFactor]
  let h := run 7 id ordinary c later
  unless h != 0 && h.eval 0 == 0 && h.eval 1 == 0 && h.eval 2 == 0 && h.eval 3 == 0 &&
      h.eval 4 != 0 do
    throw (IO.userError "denominator, scalar, later-factor, or ordinary bad center was lost")
  unless decide (h.natDegree ≤ ((factors 7 id ordinary c later).map CPolynomial.natDegree).sum) do
    throw (IO.userError "factor-degree sum bound failed")
  unless (run 7 id ordinary c []).eval 2 != 0 do
    throw (IO.userError "empty later-factor list changed the product convention")
  unless run 7 id ordinary c [0] == 0 do
    throw (IO.userError "zero explicit later factor was silently removed")
  for i in List.range c.discriminant.val.size do
    unless (StoredField.denominator (c.discriminant.coeff i)).eval 4 != 0 do
      throw (IO.userError "guard failed to protect a stored discriminant coefficient")

/-- A downstream client uses the executed projection search and actual ordinary finalization. -/
example (raw : CPolynomial K) (hraw : raw ≠ 0)
    (hd : (ClearDenominators.clear raw).global.natDegree < 7)
    (B : ℕ) (Q : CMvPolynomial 2 K) (c : Projection.Candidate K)
    (hr : Projection.search B Q = some c) (later : List (CPolynomial F))
    (hlater : ∀ f ∈ later, f ≠ 0) : run 7 id raw c later ≠ 0 :=
  run_ne_zero_of_search 7 id raw hraw
    (fun h => False.elim (Nat.not_le_of_lt hd h)) B Q c hr later hlater

#print axioms run_ne_zero_of_search
#print axioms run_natDegree_le
#print axioms eval₂_run_ne_zero_iff
#print axioms coefficient_denominator_ne_zero
#print axioms run_specialization

end CommonCenterGuardAssemblyTests

def main : IO Unit := do
  CommonCenterGuardAssemblyTests.runTests
  IO.println "guard assembly: rational projection factors and good/bad centers passed"
