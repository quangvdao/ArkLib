/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayPerturbationCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and executable checks for bounded quotient perturbations. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient
open ArkLib.Rojas.Producer.MacaulayPerturbation

namespace RojasMacaulayPerturbationTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

example {output : Output 2 F}
    (hrun : ArkLib.Rojas.Producer.MacaulayPerturbation.run twoRoots = .ok output) :
    output.perturbation ≠ 0 ∧
      ∀ lower < output.exponent,
        coefficientInS lower output.quotient = 0 :=
  run_eq_ok_minimal hrun

example {output : Output 2 F}
    (hrun : ArkLib.Rojas.Producer.MacaulayPerturbation.run twoRoots = .ok output) :
    output.exponent ≤ (basis twoRoots).length ∧
      output.perturbation.totalDegree ≤ (basis twoRoots).length := by
  have hbounds := run_eq_ok_degree_bounds hrun
  exact ⟨hbounds.2.2.2.1, hbounds.2.2.2.2⟩

example : ArkLib.Rojas.Producer.MacaulayPerturbation.run twoRoots =
      .error .quotientUnavailable ↔
    macaulayQuotient? twoRoots = none :=
  run_eq_quotientUnavailable_iff

example : ArkLib.Rojas.Producer.MacaulayPerturbation.run twoRoots =
      .error .zeroQuotient ↔
    macaulayQuotient? twoRoots = some 0 :=
  run_eq_zeroQuotient_iff

/-- Exercise the successful checked quotient and both explicitly represented
selection failures. -/
def main : IO Unit := do
  match fromCheckedQuotient?
      (none : Option (Parameters 2 F)) with
  | .error .quotientUnavailable => pure ()
  | _ => throw <| IO.userError "missing quotient did not report quotientUnavailable"
  match fromCheckedQuotient? (some (0 : Parameters 2 F)) with
  | .error .zeroQuotient => pure ()
  | _ => throw <| IO.userError "zero quotient did not report zeroQuotient"
  match ArkLib.Rojas.Producer.MacaulayPerturbation.run twoRoots with
  | .error _ =>
      throw <| IO.userError "bounded perturbation rejected the two-root quotient"
  | .ok output =>
      unless output.perturbation != 0 do
        throw <| IO.userError "selected quotient perturbation is zero"
      unless output.quotient * extraneousFactor twoRoots = characteristic twoRoots do
        throw <| IO.userError "stored quotient lost its determinant certificate"
      unless output.exponent ≤ output.quotient.totalDegree &&
          output.perturbation.totalDegree ≤ output.quotient.totalDegree &&
          output.quotient.totalDegree ≤ (basis twoRoots).length do
        throw <| IO.userError "computed output violated its degree bounds"
      for lower in List.range output.exponent do
        unless coefficientInS lower output.quotient == 0 do
          throw <| IO.userError "selected exponent was not minimal"
  IO.println "Rojas Macaulay perturbation: success, minimality, bounds, and errors passed"

#print axioms run_eq_quotientUnavailable_iff
#print axioms run_eq_zeroQuotient_iff
#print axioms run_eq_ok_fields
#print axioms run_eq_ok_minimal
#print axioms coefficientInS_totalDegree_le
#print axioms exponent_le_totalDegree_of_coefficientInS_ne_zero
#print axioms run_eq_ok_degree_bounds
#print axioms run_eq_ok_determinant_certificate

end RojasMacaulayPerturbationTests

def main : IO Unit := RojasMacaulayPerturbationTests.main
