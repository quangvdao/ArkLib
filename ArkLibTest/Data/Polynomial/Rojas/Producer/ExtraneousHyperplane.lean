/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.ExtraneousHyperplane
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and executable checks for extraneous-factor nonabsorption. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient
open ArkLib.Rojas.Producer.ExtraneousHyperplane
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.HyperplaneCoverage
open ArkLib.Rojas.Producer.HyperplaneFactor

namespace RojasExtraneousHyperplaneTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

private def torusPoint : Fin 2 → F
  | 0 => 1
  | 1 => 1

example (h : AuxiliaryAssignedExtraneous twoRoots) :
    parameterEvalHom (RingHom.id F) (Fin.cons 1 fun _ => 3) 0
    (extraneousFactor twoRoots) = 1 :=
  extraneousFactor_eval_auxiliaryConstant_eq_one twoRoots h _

example (h : AuxiliaryAssignedExtraneous twoRoots) :
    hyperplaneSubstitution torusPoint
    (fromCMvPolynomial (coefficientInS 0 (extraneousFactor twoRoots))) ≠ 0 :=
  hyperplaneSubstitution_constantExtraneousFactor_ne_zero twoRoots h torusPoint 0 (by decide)

example (h : AuxiliaryAssignedExtraneous twoRoots) : ¬ affineLinearForm torusPoint ∣
    fromCMvPolynomial (coefficientInS 0 (extraneousFactor twoRoots)) :=
  affineLinearForm_not_dvd_constantExtraneousFactor twoRoots h torusPoint 0 (by decide)

def main : IO Unit := do
  unless (extraneousIndices twoRoots).all fun i =>
      basisRowEquation twoRoots i == 0 do
    throw <| IO.userError "two-variable extraneous row was not auxiliary-assigned"
  unless parameterEvalHom (RingHom.id F) (Fin.cons 1 fun _ => 3) 0
      (extraneousFactor twoRoots) == 1 do
    throw <| IO.userError "auxiliary specialization was not unit triangular"
  unless coefficientInS 0 (extraneousFactor twoRoots) != 0 do
    throw <| IO.userError "constant coefficient of the extraneous factor vanished"
  IO.println "Rojas extraneous hyperplane: structural nonabsorption passed"

#print axioms extraneousFactor_eval_auxiliaryConstant_eq_one
#print axioms hyperplaneSubstitution_constantExtraneousFactor_ne_zero
#print axioms affineLinearForm_not_dvd_constantExtraneousFactor

end RojasExtraneousHyperplaneTests

def main : IO Unit := RojasExtraneousHyperplaneTests.main
