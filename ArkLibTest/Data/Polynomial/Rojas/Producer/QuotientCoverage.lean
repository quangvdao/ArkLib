/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.QuotientCoverage
import ArkLib.ToCompPoly.Multivariate.ClearedSubstitution
import Mathlib.Algebra.Field.ZMod

/-! Proof and runtime checks for checked-quotient affine-root coverage. -/

open CPoly CPoly.CMvPolynomial
open CompPoly
open ArkLib.Rojas
open ArkLib.Rojas.Producer
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.ExtraneousHyperplane
open ArkLib.Rojas.Producer.FactorizationCoverage
open ArkLib.Rojas.Producer.QuotientCoverage

namespace RojasQuotientCoverageTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- This system has the positive-dimensional component `x₀ = 0` and the
isolated nonsingular point `(1,0)`. -/
private def componentAndPoint : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 1)
  | 1 => X 0 * X 1

private theorem component_isolatedPoint :
    IsNonsingularAffineRoot componentAndPoint ![1, 0] := by
  constructor
  · intro i
    fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
      simp [componentAndPoint, CMvPolynomial.fromCMvPolynomial_sub',
        CMvPolynomial.fromCMvPolynomial_X,
        CMvPolynomial.fromCMvPolynomial_C]
  · simp [ArkLib.Rojas.Producer.AffineDeformation.jacobian, componentAndPoint,
      Matrix.det_fin_two, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

/-- The theorem covers a zero-coordinate isolated point even in the presence
of an unrelated positive-dimensional component. -/
example (output : MacaulayPerturbation.Output 2 F)
    (hrun : MacaulayPerturbation.run componentAndPoint = .ok output)
    (hauxiliary : AuxiliaryAssignedExtraneous componentAndPoint) :
    CPolynomial.X - CPolynomial.C
        (geometricProjection (RingHom.id F) ![3, 4] ![1, 0]) ∣
      specializePerturbation output.perturbation ![3, 4] :=
  run_specializedLinearFactor_dvd_of_auxiliaryAssigned
    componentAndPoint ![1, 0] ![3, 4] output hrun component_isolatedPoint
    hauxiliary 0 (by decide)

/-- A nonsingular-origin canary.  Its extraneous trailing coefficient absorbs
`u₀`, demonstrating why single-factor cancellation does not close the origin. -/
private def originSystem : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 + X 0
  | 1 => X 1

private def originPoint : Fin 2 → F := ![0, 0]

private theorem origin_nonsingular :
    IsNonsingularAffineRoot originSystem originPoint := by
  constructor
  · intro i
    fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
      simp [originSystem, originPoint, CMvPolynomial.fromCMvPolynomial_pow,
        CMvPolynomial.fromCMvPolynomial_X]
  · simp [ArkLib.Rojas.Producer.AffineDeformation.jacobian, originSystem, originPoint,
      Matrix.det_fin_two, CMvPolynomial.fromCMvPolynomial_pow,
      CMvPolynomial.fromCMvPolynomial_X]

/-- Execute one quotient construction and check both its origin root and its
nonzero root with a zero second coordinate. -/
def main : IO Unit := do
  match MacaulayPerturbation.run originSystem with
  | .error error =>
      throw <| IO.userError s!"Rojas quotient coverage: origin system failed: {repr error}"
  | .ok output =>
      unless output.exponent == 0 do
        throw <| IO.userError "Rojas quotient coverage: unexpected quotient exponent"
      let extraneous := extraneousFactor originSystem
      unless auxiliaryAssignedExtraneousB originSystem do
        throw <| IO.userError "Rojas quotient coverage: origin row assignment changed"
      unless lowestSExponent? extraneous == some 0 do
        throw <| IO.userError "Rojas quotient coverage: extraneous trailing degree changed"
      unless coefficientInS 0 extraneous == X 0 do
        throw <| IO.userError "Rojas quotient coverage: origin trailing factor changed"
      unless (checkedExactQuotient? output.perturbation (X 0)).isSome do
        throw <| IO.userError "Rojas quotient coverage: quotient lost its origin factor"
      unless (checkedExactQuotient?
          (coefficientInS 0 (characteristic originSystem)) (X 0 ^ 2)).isSome do
        throw <| IO.userError "Rojas quotient coverage: determinant lost origin multiplicity"
      let u : Fin 2 → F := ![3, 4]
      let specialized := specializePerturbation output.perturbation u
      unless specialized.eval 0 == 0 do
        throw <| IO.userError "Rojas quotient coverage: nonsingular origin was lost"
      let nonzeroPoint : Fin 2 → F := ![-1, 0]
      let projected := geometricProjection (RingHom.id F) u nonzeroPoint
      unless specialized.eval projected == 0 do
        throw <| IO.userError "Rojas quotient coverage: zero-coordinate root was lost"
      let parameters : Fin 3 → F := ![0, 1, 1]
      unless parameterEvalHom (RingHom.id F) parameters 1
          extraneous == 0 do
        throw <| IO.userError "Rojas quotient coverage: origin extraneous absorption changed"
      let parametersAtOne : Fin 3 → F := ![1, 1, 1]
      unless parameterEvalHom (RingHom.id F) parametersAtOne 1
          extraneous == 1 do
        throw <| IO.userError "Rojas quotient coverage: u0=1 extraneous canary changed"
  IO.println "Rojas quotient coverage: origin and zero-coordinate runtime passed"

#print axioms coefficientInS_add_eq_mul_of_lowestSExponents
#print axioms lowestSExponent?_mul
#print axioms affineLinearForm_dvd_left_of_mul_right
#print axioms run_perturbation_affineLinearForm_dvd_of_trailingExtraneous_not_dvd
#print axioms run_perturbation_affineLinearForm_dvd_of_characteristic_multiplicity
#print axioms run_specializedLinearFactor_dvd_of_trailingExtraneous_not_dvd
#print axioms run_perturbation_affineLinearForm_dvd_of_auxiliaryAssigned
#print axioms run_specializedLinearFactor_dvd_of_auxiliaryAssigned

end RojasQuotientCoverageTests

def rojasQuotientCoverageStandaloneMain : IO Unit :=
  RojasQuotientCoverageTests.main
