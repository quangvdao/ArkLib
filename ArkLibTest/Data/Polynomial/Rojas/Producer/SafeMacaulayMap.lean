/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.SafeMacaulayMap
import Mathlib.Algebra.Field.ZMod

/-! Executed end-to-end checks for the denominator-safe system producer. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer

namespace RojasSafeMacaulayMapTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private def mutated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 2
  | 1 => X 1 - X 0

/-- Execute the checked quotient, safe specialization scan, and final coordinate map directly
from two different square systems. -/
def run : IO Unit := do
  let parameters : List F := [0, 1, 2, 3, 4, 5, 6]
  match SafeMacaulayMap.run 7 twoRoots 1 2 parameters with
  | .error error =>
      throw (IO.userError s!"safe system producer found no specialization: {repr error}")
  | .ok output =>
      unless output.perturbation.perturbation != 0 &&
          output.candidate.shiftedEliminants.length == 4 &&
          output.map.numerators.length == 2 &&
          output.map.modulus.natDegree == 2 do
        throw (IO.userError "safe system producer returned inconsistent data")
      let recovered : List (F × F × F) := [(2, -1, -1), (5, 1, 1)]
      for (theta, x0, x1) in recovered do
        let denominator := output.map.denominator.eval theta
        unless denominator != 0 &&
            (output.map.numerators[0]?.getD 0).eval theta / denominator == x0 &&
            (output.map.numerators[1]?.getD 0).eval theta / denominator == x1 do
          throw (IO.userError "safe system producer failed to recover a root")
      match SafeMacaulayMap.run 7 mutated 1 2 parameters with
      | .error error =>
          throw (IO.userError s!"safe system producer rejected mutation: {repr error}")
      | .ok changed =>
          unless changed.perturbation.perturbation != output.perturbation.perturbation &&
              changed.map.modulus != output.map.modulus do
            throw (IO.userError "safe system producer ignored the input mutation")
  IO.println "Rojas denominator-safe system producer: checks passed"

#print axioms SafeMacaulayMap.run_eq_ok_perturbation
#print axioms SafeMacaulayMap.run_eq_ok_candidate
#print axioms SafeMacaulayMap.run_exists_iff
#print axioms SafeMacaulayMap.run_eq_ok_determinant_certificate
#print axioms SafeMacaulayMap.run_eq_ok_denominator_eval₂_ne_zero
#print axioms SafeMacaulayMap.run_eq_ok_representsPoint

end RojasSafeMacaulayMapTests

def main : IO Unit := RojasSafeMacaulayMapTests.run
