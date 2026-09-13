/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.RootMultiplicity
import ArkLib.ToCompPoly.Multivariate.ClearedSubstitution
import Mathlib.Algebra.Field.ZMod

/-! Checks for the residual Macaulay root-multiplicity reduction. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.FactorizationCoverage
open ArkLib.Rojas.Producer.HyperplaneFactor
open ArkLib.Rojas.Producer.MacaulayPerturbation
open ArkLib.Rojas.Producer.MacaulayQuotient
open ArkLib.Rojas.Producer.RootMultiplicity

namespace RojasRootMultiplicityTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

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

/-- The exact valuation reduction applies at the nonsingular affine origin;
it has no nonzero-coordinate or nonabsorption premise. -/
theorem origin_nonsingular_multiplicity_reduction
    (output : MacaulayPerturbation.Output 2 F)
    (hrun : MacaulayPerturbation.run originSystem = .ok output)
    (hextraneous : lowestSExponent? (extraneousFactor originSystem) = some 0) :
    IsNonsingularAffineRoot originSystem originPoint ∧
      (affineLinearForm originPoint *
            fromCMvPolynomial (coefficientInS 0 (extraneousFactor originSystem)) ∣
          fromCMvPolynomial
            (coefficientInS output.exponent (characteristic originSystem)) ↔
        multiplicity (affineLinearForm originPoint)
            (fromCMvPolynomial (coefficientInS 0 (extraneousFactor originSystem))) <
          multiplicity (affineLinearForm originPoint)
            (fromCMvPolynomial
              (coefficientInS output.exponent (characteristic originSystem)))) := by
  refine ⟨origin_nonsingular, ?_⟩
  simpa using run_characteristic_multiplicity_iff_valuation_gap
    originSystem originPoint output hrun hextraneous

section BareKernelCounterexample

abbrev P := Polynomial F

private noncomputable def counterexampleMatrix : Matrix (Fin 2) (Fin 2) P :=
  !![Polynomial.X, Polynomial.X;
    1, Polynomial.X]

private noncomputable def counterexampleVector : Fin 2 → P := ![0, 1]

/-- A unit-pivot kernel modulo `X` and an `X`-divisible principal minor do not
force two copies of `X` into the full determinant.  This rules out the bare
kernel/principal-minor argument as a proof of the residual theorem. -/
theorem bare_kernel_does_not_force_principal_multiplicity :
    (∀ i, Polynomial.X ∣
        counterexampleMatrix.mulVec counterexampleVector i) ∧
      IsUnit (counterexampleVector 1) ∧
      ¬Polynomial.X * Polynomial.X ∣ counterexampleMatrix.det := by
  constructor
  · intro i
    fin_cases i <;>
      simp [counterexampleMatrix, counterexampleVector, Matrix.mulVec]
  constructor
  · simp [counterexampleVector]
  · intro hdiv
    have hpow : Polynomial.X ^ 2 ∣ counterexampleMatrix.det := by
      simpa [pow_two] using hdiv
    have hcoeff := Polynomial.X_pow_dvd_iff.mp hpow 1 (by omega)
    simp [counterexampleMatrix, Matrix.det_fin_two] at hcoeff

end BareKernelCounterexample

/-- Execute the absorbed-origin case and check the exact coefficient product
whose universal proof is reduced to the valuation gap above. -/
def main : IO Unit := do
  match MacaulayPerturbation.run originSystem with
  | .error error =>
      throw <| IO.userError s!"Rojas root multiplicity: origin run failed: {repr error}"
  | .ok output =>
      unless output.exponent == 0 do
        throw <| IO.userError "Rojas root multiplicity: origin exponent changed"
      unless lowestSExponent? (extraneousFactor originSystem) == some 0 do
        throw <| IO.userError "Rojas root multiplicity: extraneous exponent changed"
      unless (checkedExactQuotient?
          (coefficientInS output.exponent (characteristic originSystem))
          (X 0 ^ 2)).isSome do
        throw <| IO.userError "Rojas root multiplicity: absorbed origin factor was lost"
  IO.println "Rojas root multiplicity: absorbed-origin coefficient canary passed"

#print axioms dvd_det_of_dvd_mulVec_of_isUnit
#print axioms factor_mul_principal_det_dvd_det_of_mulVec_certificate
#print axioms prime_mul_dvd_iff_multiplicity_lt
#print axioms affineLinearForm_prime
#print axioms run_characteristic_multiplicity_iff_perturbation_factor
#print axioms run_characteristic_multiplicity_iff_valuation_gap
#print axioms origin_nonsingular_multiplicity_reduction
#print axioms bare_kernel_does_not_force_principal_multiplicity

end RojasRootMultiplicityTests

def main : IO Unit := RojasRootMultiplicityTests.main
