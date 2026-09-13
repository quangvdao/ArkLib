/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulay

/-! Runtime checks for the computed multivariate Macaulay producer. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay

namespace RojasDenseMacaulayTests

abbrev F := ZMod 7

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private def changed : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 2
  | 1 => X 1 - X 0

private def positiveDimensional : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - 1)
  | 1 => X 0 * X 1

private def degenerate : Fin 2 → CMvPolynomial 2 F
  | 0 => 0
  | 1 => X 0 - 3

def runChecks : IO Unit := do
  unless (sparseSupport (twoRoots 0)).length == 2 do
    throw (IO.userError "Rojas Macaulay: sparse support was not read from the equation")
  unless denseDegree (twoRoots 0) == 2 && denseDegree (twoRoots 1) == 1 do
    throw (IO.userError "Rojas Macaulay: dense degree envelope is wrong")
  unless macaulayDegree twoRoots == 2 do
    throw (IO.userError "Rojas Macaulay: critical matrix degree is wrong")
  let first := characteristic twoRoots
  let mutated := characteristic changed
  unless first != mutated do
    throw (IO.userError "Rojas Macaulay: changing an input equation did not change the determinant")
  match run twoRoots with
  | .error _ => throw (IO.userError "Rojas Macaulay: two-root bivariate system was rejected")
  | .ok output =>
      unless output.perturbation != 0 && output.matrixSize == (basis twoRoots).length do
        throw (IO.userError "Rojas Macaulay: successful output did not store computed data")
      unless output.perturbation.eval ![-2, 1, 1] == 0 do
        throw (IO.userError "Rojas Macaulay: first isolated-root factor was lost")
      unless output.perturbation.eval ![2, 1, 1] == 0 do
        throw (IO.userError "Rojas Macaulay: second isolated-root factor was lost")
  unless (matrixEntries positiveDimensional).size == (basis positiveDimensional).length &&
      (basis positiveDimensional).length == 10 do
    throw (IO.userError "Rojas Macaulay: mixed-dimensional matrix construction is wrong")
  match run degenerate with
  | .error _ => throw (IO.userError "Rojas Macaulay: explicit degenerate semantics regressed")
  | .ok _ => pure ()
  IO.println "Rojas dense Macaulay: support, mutation, roots, and degeneracy checks passed"

#print axioms characteristic_eq_det
#print axioms matrixEntries_size
#print axioms matrixEntries_row_size
#print axioms denseDegree_pos
#print axioms run_ok_computed

end RojasDenseMacaulayTests
