/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.FactorizationCoverage
import Mathlib.Algebra.Field.ZMod

/-! Checks for input-derived nonsingular affine-root factor coverage. -/

open CPoly CPoly.CMvPolynomial
open CompPoly
open ArkLib.Rojas
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.AffineDeformation
open ArkLib.Rojas.Producer.FactorizationCoverage

namespace RojasFactorizationCoverageTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The component `x₀ = 0` is positive-dimensional, while `(1,0)` is a
nonsingular isolated root with a zero coordinate. -/
private def componentAndPoint : Fin 2 → CMvPolynomial 2 F
  | 0 => CMvPolynomial.X 0 * (CMvPolynomial.X 0 - CMvPolynomial.C 1)
  | 1 => CMvPolynomial.X 0 * CMvPolynomial.X 1

private theorem component_family_root (a : F) :
    IsCommonAffineRoot (RingHom.id F) ![0, a] componentAndPoint := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [componentAndPoint, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem isolated_root :
    IsCommonAffineRoot (RingHom.id F) ![1, 0] componentAndPoint := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [componentAndPoint, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem isolated_nonsingular :
    (jacobian componentAndPoint ![1, 0]).det ≠ 0 := by
  simp [jacobian, componentAndPoint, Matrix.det_fin_two,
    CMvPolynomial.fromCMvPolynomial_sub',
    CMvPolynomial.fromCMvPolynomial_X,
    CMvPolynomial.fromCMvPolynomial_C]

private theorem isolated_point :
    IsNonsingularAffineRoot componentAndPoint ![1, 0] :=
  ⟨isolated_root, isolated_nonsingular⟩

example :
    MvPolynomial.HasIsolatingPolynomial
      (fun i ↦ fromCMvPolynomial (componentAndPoint i)) ![1, 0] :=
  isolated_point.hasIsolatingPolynomial

example (output : Output 2 (F := F))
    (hrun : run componentAndPoint = .ok output) :
    CoversNonsingularAffineRoots componentAndPoint output.perturbation :=
  run_coversNonsingularAffineRoots componentAndPoint output hrun

example (output : Output 2 (F := F))
    (hrun : run componentAndPoint = .ok output) :
    CPolynomial.X - CPolynomial.C
        (geometricProjection (RingHom.id F) ![3, 4] ![1, 0]) ∣
      specializePerturbation output.perturbation ![3, 4] :=
  run_specializedLinearFactor_dvd componentAndPoint output hrun
    ![1, 0] ![3, 4] isolated_point

/-- Runtime evaluation checks the predicted specialized root in the actual
computed perturbation. -/
def runChecks : IO Unit := do
  match run componentAndPoint with
  | .error _ =>
      throw (IO.userError "Rojas factor coverage: component system was rejected")
  | .ok output =>
      let u : Fin 2 → F := ![3, 4]
      let root := geometricProjection (RingHom.id F) u ![1, 0]
      unless (specializePerturbation output.perturbation u).eval root == 0 do
        throw (IO.userError "Rojas factor coverage: specialized root was lost")
  IO.println "Rojas factor coverage: isolated root survived unrelated component"

#print axioms IsNonsingularAffineRoot.hasIsolatingPolynomial
#print axioms run_coversNonsingularAffineRoots
#print axioms specializedLinearFactor_dvd_of_coverage
#print axioms run_specializedLinearFactor_dvd

end RojasFactorizationCoverageTests

def main : IO Unit := RojasFactorizationCoverageTests.runChecks
