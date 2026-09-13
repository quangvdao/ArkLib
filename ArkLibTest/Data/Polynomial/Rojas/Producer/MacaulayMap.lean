/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayMap
import Mathlib.Algebra.Field.ZMod

/-! Executed end-to-end checks for the composed dense Rojas map producer. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer

namespace RojasMacaulayMapTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private def mutated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 2
  | 1 => X 1 - X 0

/-- Execute the checked quotient, specialization scan, and final coordinate-map construction. -/
def run : IO Unit := do
  let parameters : List F := [0, 1, 2, 3, 4, 5, 6]
  match MacaulayMap.run 7 twoRoots 1 2 parameters with
  | .error _ => throw (IO.userError "Rojas composed producer found no specialization")
  | .ok output =>
      unless output.perturbation.perturbation != 0 do
        throw (IO.userError "Rojas composed producer returned a zero perturbation")
      unless output.candidate.shiftedEliminants.length == 4 do
        throw (IO.userError "Rojas composed producer lost shifted candidates")
      unless output.map.numerators.length == 2 do
        throw (IO.userError "Rojas composed producer returned the wrong map width")
      unless output.map.modulus.natDegree == 2 do
        throw (IO.userError "Rojas composed producer lost the guarded degree")
      let recovered : List (F × F × F) := [(2, -1, -1), (5, 1, 1)]
      for (theta, x₀, x₁) in recovered do
        let denominator := output.map.denominator.eval theta
        unless denominator != 0 do
          throw (IO.userError "Rojas composed producer returned a zero denominator")
        unless (output.map.numerators[0]?.getD 0).eval theta / denominator == x₀ &&
            (output.map.numerators[1]?.getD 0).eval theta / denominator == x₁ do
          throw (IO.userError "Rojas composed producer failed to recover a system root")
      match MacaulayMap.run 7 mutated 1 2 parameters with
      | .error _ => throw (IO.userError "Rojas composed producer rejected the mutated system")
      | .ok changed =>
          unless changed.perturbation.perturbation != output.perturbation.perturbation &&
              changed.map.modulus != output.map.modulus do
            throw (IO.userError "Rojas composed producer ignored an input-equation mutation")
  IO.println "Rojas composed Macaulay-to-map producer: checks passed"

#print axioms MacaulayMap.run_eq_ok_perturbation
#print axioms MacaulayMap.run_eq_ok_candidate
#print axioms MacaulayMap.run_eq_ok_determinant_certificate

end RojasMacaulayMapTests

def rojasMacaulayMapStandaloneMain : IO Unit :=
  RojasMacaulayMapTests.run
