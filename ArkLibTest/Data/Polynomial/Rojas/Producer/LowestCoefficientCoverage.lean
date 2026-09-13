/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.LowestCoefficientCoverage
import Mathlib.Algebra.Field.ZMod

/-! Checks for lowest-coefficient coverage from computed finite jets. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.AffineDeformation
open ArkLib.Rojas.Producer.HyperplaneFactor
open ArkLib.Rojas.Producer.LowestCoefficientCoverage

namespace RojasLowestCoefficientCoverageTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Two nonsingular isolated roots `(0,0)` and `(1,0)`, including coordinate
hyperplane roots. -/
private def twoIsolated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 1)
  | 1 => X 1

/-- A positive-dimensional component `x₀=0` unrelated to the nonsingular
isolated root `(1,0)`. -/
private def componentAndPoint : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 1)
  | 1 => X 0 * X 1

private def mutated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 2)
  | 1 => X 1

private theorem twoIsolated_root (point : Fin 2 → F)
    (hpoint : point = ![0, 0] ∨ point = ![1, 0]) :
    IsCommonAffineRoot (RingHom.id F) point twoIsolated := by
  rcases hpoint with rfl | rfl <;>
    intro i <;> fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [twoIsolated, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem twoIsolated_nonsingular (point : Fin 2 → F)
    (hpoint : point = ![0, 0] ∨ point = ![1, 0]) :
    (jacobian twoIsolated point).det ≠ 0 := by
  rcases hpoint with rfl | rfl <;>
    simp [jacobian, twoIsolated, Matrix.det_fin_two,
      CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem component_root :
    IsCommonAffineRoot (RingHom.id F) ![1, 0] componentAndPoint := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [componentAndPoint, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem component_nonsingular :
    (jacobian componentAndPoint ![1, 0]).det ≠ 0 := by
  simp [jacobian, componentAndPoint, Matrix.det_fin_two,
    CMvPolynomial.fromCMvPolynomial_sub',
    CMvPolynomial.fromCMvPolynomial_X,
    CMvPolynomial.fromCMvPolynomial_C]

example (output : Output 2 (F := F)) (hrun : run twoIsolated = .ok output) :
    affineLinearForm (![0, 0] : Fin 2 → F) ∣
      fromCMvPolynomial output.perturbation :=
  affineLinearForm_dvd_run_perturbation twoIsolated ![0, 0]
    (twoIsolated_root _ (Or.inl rfl))
    (twoIsolated_nonsingular _ (Or.inl rfl)) output hrun

example (output : Output 2 (F := F)) (hrun : run twoIsolated = .ok output) :
    affineLinearForm (![1, 0] : Fin 2 → F) ∣
      fromCMvPolynomial output.perturbation :=
  affineLinearForm_dvd_run_perturbation twoIsolated ![1, 0]
    (twoIsolated_root _ (Or.inr rfl))
    (twoIsolated_nonsingular _ (Or.inr rfl)) output hrun

/-- The unrelated positive-dimensional component does not obstruct coverage
of the isolated zero-coordinate root. -/
example (output : Output 2 (F := F))
    (hrun : run componentAndPoint = .ok output) :
    affineLinearForm (![1, 0] : Fin 2 → F) ∣
      fromCMvPolynomial output.perturbation :=
  affineLinearForm_dvd_run_perturbation componentAndPoint ![1, 0]
    component_root component_nonsingular output hrun

/-- Runtime checks both isolated-root hyperplanes on the executable lowest
coefficient and confirms that mutating an input changes the computed output. -/
def runChecks : IO Unit := do
  match run twoIsolated with
  | .error _ =>
      throw (IO.userError "Rojas lowest coefficient: two-root system was rejected")
  | .ok output =>
      unless output.perturbation.eval ![0, 1, 2] == 0 do
        throw (IO.userError "Rojas lowest coefficient: zero root hyperplane was lost")
      unless output.perturbation.eval ![6, 1, 2] == 0 do
        throw (IO.userError "Rojas lowest coefficient: second root hyperplane was lost")
      match run mutated with
      | .error _ =>
          throw (IO.userError "Rojas lowest coefficient: mutated system was rejected")
      | .ok changed =>
          unless changed.perturbation != output.perturbation do
            throw (IO.userError "Rojas lowest coefficient: mutation did not change output")
  IO.println "Rojas lowest coefficient: two roots, zero coordinates, and mutation passed"

#print axioms coeff_sView
#print axioms X_pow_succ_dvd_movingEvaluation_characteristic
#print axioms hyperplaneSubstitution_lowestCharacteristic_eq_zero
#print axioms affineLinearForm_dvd_lowestCharacteristic
#print axioms affineLinearForm_dvd_run_perturbation

end RojasLowestCoefficientCoverageTests

def main : IO Unit := RojasLowestCoefficientCoverageTests.runChecks
