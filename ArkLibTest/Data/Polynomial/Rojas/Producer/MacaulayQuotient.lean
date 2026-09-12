/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotient
import Mathlib.Algebra.Field.ZMod

/-! Runtime checks for the computed Macaulay extraneous factor and quotient. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayQuotientTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private opaque twoRootsQuotient? : Option (CMvPolynomial 4 F) :=
  macaulayQuotient? (F := F) twoRoots

def runChecks : IO Unit := do
  unless (extraneousIndices twoRoots).length == 1 do
    throw (IO.userError "Rojas quotient: wrong non-reduced principal minor")
  let quotient? := twoRootsQuotient?
  if quotient?.isNone then
    throw (IO.userError "Rojas quotient: exact Macaulay division failed")
  let quotient := quotient?.getD 0
  unless quotient * extraneousFactor twoRoots = characteristic twoRoots do
    throw (IO.userError "Rojas quotient: product certificate failed")
  let degree? := lowestSExponent? quotient
  if degree?.isNone then
    throw (IO.userError "Rojas quotient: perturbation extraction failed")
  let perturbation := coefficientInS (degree?.getD 0) quotient
  unless perturbation.eval ![-2, 1, 1] == 0 &&
      perturbation.eval ![2, 1, 1] == 0 do
    throw (IO.userError "Rojas quotient: concrete isolated factors were lost")
  IO.println "Rojas Macaulay quotient: minor, exact division, and example factors passed"

#print axioms checkedExactQuotient?_sound
#print axioms extraneousFactor_eq_det
#print axioms macaulayQuotient?_sound
#print axioms macaulayQuotient?_extraneousFactor_ne_zero
#print axioms perturbation?_eq_some_iff

end RojasMacaulayQuotientTests
