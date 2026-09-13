/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantMap
import Mathlib.Algebra.Field.ZMod

/-! Executed two-coordinate checks for Rojas Steps 4--5. -/

open CPoly
open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas ArkLib.Rojas.Producer.SubresultantMap

namespace RojasSubresultantMapTests

abbrev F := ZMod 11

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def perturbation : CMvPolynomial 3 F :=
  (CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.X 2) *
    (CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.X 1)

private def mutatedPerturbation : CMvPolynomial 3 F :=
  perturbation + 1

/-- This is an actual Step-0--3 candidate, rather than a hand-written shifted list. -/
private def candidate : SpecializationCandidate (F := F) :=
  candidateFromParameter perturbation 1 2

/-- Parameter roots `θ=7,9` encode `(0,1)` and `(1,0)`, exercising zero coordinates. -/
def run : IO Unit := do
  let output := produce 11 2 1 candidate
  unless output.modulus == (X + 4) * (X + 2) do
    throw (IO.userError "Rojas Steps 4--5: squarefree modulus mismatch")
  unless output.numerators.length == 2 do
    throw (IO.userError "Rojas Steps 4--5: coordinate width mismatch")
  unless output.denominator.eval 7 != 0 && output.denominator.eval 9 != 0 do
    throw (IO.userError "Rojas Steps 4--5: denominator vanished at a guarded root")
  let points : List (F × F × F) := [(7, 0, 1), (9, 1, 0)]
  for (theta, x₀, x₁) in points do
    let denominator := output.denominator.eval theta
    unless (output.numerators[0]?.getD 0).eval theta / denominator == x₀ do
      throw (IO.userError "Rojas Steps 4--5: first coordinate was not recovered")
    unless (output.numerators[1]?.getD 0).eval theta / denominator == x₁ do
      throw (IO.userError "Rojas Steps 4--5: second coordinate was not recovered")
  let x : CPolynomial F := X
  let zeroRoot := firstSubresultant (x * (x - 1)) (x * (x - 2))
  unless zeroRoot.1 != 0 && zeroRoot.2 == 0 do
    throw (IO.userError "Rojas first subresultant: zero common root was lost")
  let linear := firstSubresultant (x - 3) (x - 3)
  unless linear.1 != 0 && -linear.2 / linear.1 == 3 do
    throw (IO.userError "Rojas first subresultant: degree-one branch was incorrect")
  let mutated := produce 11 2 1 (candidateFromParameter mutatedPerturbation 1 2)
  unless mutated.modulus.eval 7 != 0 ||
      (mutated.numerators[0]?.getD 0).eval 7 / mutated.denominator.eval 7 != 0 ||
      (mutated.numerators[1]?.getD 0).eval 7 / mutated.denominator.eval 7 != 1 do
    throw (IO.userError "Rojas Steps 4--5: mutated system retained the spurious point")
  IO.println "Rojas first-subresultant coordinate map: checks passed"

#print axioms produce_numerators_length
#print axioms firstSubresultant_linear_denominator_ne_zero
#print axioms affineTransform_eval₂
#print axioms GcdLinearAtRoot.subresultant_ratio
#print axioms produce_representsPoint

end RojasSubresultantMapTests

def main : IO Unit := RojasSubresultantMapTests.run
