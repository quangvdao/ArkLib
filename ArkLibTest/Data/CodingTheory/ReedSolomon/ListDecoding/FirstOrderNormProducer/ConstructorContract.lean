/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ConstructorContract
import Mathlib.Algebra.Field.ZMod

/-! Acceptance checks for the actual first-order constructor contract. -/

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.ConstructorContractTests

open CompPoly CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A nonlinear first-order equation with nonconstant separant. -/
private def equation : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 ^ 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0

/-- Its initial equation at zero. -/
private def component : CMvPolynomial 2 (ZMod 5) :=
  CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 0

/-- The actual constructor reduces the fourth separant power to a different stored normal form.
Nevertheless every regular chart root witnesses the required evaluation identity and nonzero
denominator, and the converted fiber degree remains below the characteristic. -/
def run : IO Unit := do
  let some chart := construct? 5 1 2 2 0 equation component [0, 1, 2]
    | throw <| IO.userError "nonlinear first-order constructor fixture failed"
  if chart.denominator == chart.separant ^ 4 then
    throw <| IO.userError "fixture did not exercise nontrivial denominator reduction"
  if chart.denominator == 1 then
    throw <| IO.userError "fixture unexpectedly produced a unit denominator"
  let data := ChartPolynomials.ofChart chart
  unless data.equation.natDegree < 5 do
    throw <| IO.userError "constructor fiber degree is not below the characteristic"
  let mut regularRoots := 0
  for u in [0, 1, 2, 3, 4] do
    for v in [0, 1, 2, 3, 4] do
      let point : Fin 2 → ZMod 5 := ![u, v]
      if chart.equation.eval point == 0 && chart.separant.eval point != 0 then
        regularRoots := regularRoots + 1
        unless chart.denominator.eval point != 0 &&
            chart.denominator.eval point == chart.separant.eval point ^ 4 do
          throw <| IO.userError "reduced denominator lost its regular-locus identity"
  unless regularRoots > 0 do
    throw <| IO.userError "nonlinear fixture has no regular chart root"

#check DenominatorRegular
#check denominatorRegular_of_eq_pow
#check preparedBlock_modulus_dvd_equation
#check construct?_denominatorRegular
#check construct?_firstOrder_normalForms
#check construct?_firstOrder_equation_natDegree
#check construct?_firstOrderNormCandidates_point_complete
#check construct?_firstOrderNormCandidatesWithRecovery_complete
#check construct?_genericSquarefree
#check construct?_firstOrder_genericSquarefree
#check construct?_firstOrderRunNormCandidatesWithRecovery_complete

#print axioms preparedBlock_modulus_dvd_equation
#print axioms construct?_denominatorRegular
#print axioms construct?_firstOrder_normalForms
#print axioms construct?_firstOrder_equation_natDegree
#print axioms construct?_firstOrderNormCandidates_point_complete
#print axioms construct?_firstOrderNormCandidatesWithRecovery_complete
#print axioms construct?_genericSquarefree
#print axioms construct?_firstOrder_genericSquarefree
#print axioms construct?_firstOrderRunNormCandidatesWithRecovery_complete

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ConstructorContractTests
