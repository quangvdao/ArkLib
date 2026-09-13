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
open CPolynomial FullSquarefreeDecomposition.Driver
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer
open ArkLib.FiniteField.ExplicitConstruction

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

private abbrev Base := ZMod 5
private abbrev modulus : CPolynomial Base := CPolynomial.X

private instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, modulus, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

private instance : Fact (Irreducible modulus.toPoly) := ⟨by
  rw [modulus, CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

private abbrev F := Carrier modulus
private def M : MulContext F := MulContext.naive
private def D : ModContext F := ModContext.naive

private def actualEquation : CMvPolynomial 3 F :=
  CMvPolynomial.X 2 ^ 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0

private def domain : Fin 2 ↪ F where
  toFun := ![0, 1]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private def received (i : Fin 2) : F := domain i + 1

/-- Executable nested evaluation in the stored `[U][V]` coefficient order. -/
private def evalNestedRuntime (q : CPolynomial (CPolynomial F)) (u v : F) : F :=
  q.val.zipIdx.foldl (fun acc ⟨coefficient, degree⟩ =>
    acc + CPolynomial.eval u coefficient * v ^ degree) 0

/-- Compiled execution of the complete nonlinear path: the actual regular-part producer feeds the
actual constructor, whose reduced nonunit denominator is checked on the regular point carrying
`P(X)=1+X`; the combined norm/recovery producer must include a candidate specializing to `P`. -/
def runActual : IO Unit := do
  let .regularPart producerData :=
      ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.FirstOrder.run
        5 id 0 actualEquation
    | throw <| IO.userError "actual first-order producer did not return a regular component"
  let actualComponent :=
    ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.FirstOrder.component producerData
  let some chart := construct? 5 1 2 2 0 actualEquation actualComponent [0, 1, 2]
    | throw <| IO.userError "actual nonlinear component did not reach the constructor"
  if chart.denominator == chart.separant ^ 4 then
    throw <| IO.userError "actual path did not exercise nontrivial denominator reduction"
  if chart.denominator == 1 then
    throw <| IO.userError "actual path unexpectedly produced a unit denominator"
  let chartPolynomials := ChartPolynomials.ofChart chart
  unless chartPolynomials.equation.natDegree < 5 do
    throw <| IO.userError "actual component fiber degree is not below the characteristic"
  let candidates := firstOrderNormCandidatesWithRecovery
    5 modulus M D 2 chart domain received
  let mut retainedWantedPoint := false
  let mut wantedCandidate := false
  for u in [0, 1, 2, 3, 4] do
    for v in [0, 1, 2, 3, 4] do
      let point : Fin 2 → F := ![u, v]
      if chart.equation.eval point == 0 && chart.separant.eval point != 0 then
        let denominator := chart.denominator.eval point
        let reconstructed :=
          (List.ofFn chart.numerators).map fun numerator => numerator.eval point / denominator
        if reconstructed == [1, 1] then
          retainedWantedPoint := true
          unless denominator != 0 do
            throw <| IO.userError "wanted regular point has zero reduced denominator"
          if candidates.any fun candidate =>
              candidate.modulus.eval u == 0 &&
                evalNestedRuntime candidate.fiber u v == 0 &&
                candidate.coefficients.map
                  (fun coefficient => evalNestedRuntime coefficient u v) == [1, 1] then
            wantedCandidate := true
  unless retainedWantedPoint do
    throw <| IO.userError "actual chart lost the wanted regular Taylor point"
  unless wantedCandidate do
    throw <| IO.userError "actual combined producer omitted the wanted specialization"

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
#check firstOrder_component_dvd_initialEquation
#check construct?_firstOrder_component_totalDegree_lt
#check construct?_firstOrderRunNormCandidatesWithRecovery_complete

#print axioms preparedBlock_modulus_dvd_equation
#print axioms construct?_denominatorRegular
#print axioms construct?_firstOrder_normalForms
#print axioms construct?_firstOrder_equation_natDegree
#print axioms construct?_firstOrderNormCandidates_point_complete
#print axioms construct?_firstOrderNormCandidatesWithRecovery_complete
#print axioms construct?_genericSquarefree
#print axioms construct?_firstOrder_genericSquarefree
#print axioms firstOrder_component_dvd_initialEquation
#print axioms construct?_firstOrder_component_totalDegree_lt
#print axioms construct?_firstOrderRunNormCandidatesWithRecovery_complete

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ConstructorContractTests
