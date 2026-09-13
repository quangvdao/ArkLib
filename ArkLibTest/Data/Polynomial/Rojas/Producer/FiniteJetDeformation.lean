/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.FiniteJetDeformation
import ArkLib.ToCompPoly.Univariate.Basic
import Mathlib.Algebra.Field.ZMod

/-! Checks for recursive finite-jet deformation and determinant transport. -/

open CompPoly CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.AffineDeformation
open ArkLib.Rojas.Producer.FiniteJetDeformation

namespace RojasFiniteJetDeformationTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The line `x₀ = 0` and the unrelated nonsingular isolated root `(1,0)`. -/
private def componentAndPoint : Fin 2 → CMvPolynomial 2 F
  | 0 => CMvPolynomial.X 0 * (CMvPolynomial.X 0 - CMvPolynomial.C 1)
  | 1 => CMvPolynomial.X 0 * CMvPolynomial.X 1

private def point : Fin 2 → F := ![1, 0]

private theorem point_root :
    IsCommonAffineRoot (RingHom.id F) point componentAndPoint := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [componentAndPoint, point, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem point_nonsingular :
    (jacobian componentAndPoint point).det ≠ 0 := by
  simp [jacobian, componentAndPoint, point, Matrix.det_fin_two,
    CMvPolynomial.fromCMvPolynomial_sub', CMvPolynomial.fromCMvPolynomial_X,
    CMvPolynomial.fromCMvPolynomial_C]

example (steps : ℕ) (i : Fin 2) :
    (liftJet componentAndPoint point steps i).coeff 0 = point i :=
  coeff_zero_liftJet componentAndPoint point steps i

example (steps : ℕ) (i : Fin 2) :
    Polynomial.X ^ (steps + 1) ∣
      equationValue componentAndPoint (liftJet componentAndPoint point steps) i :=
  X_pow_succ_dvd_equationValue_liftJet componentAndPoint point
    point_root point_nonsingular steps i

example (steps : ℕ) :
    parameterEvalHom ((jetQuotientMap steps).comp Polynomial.C)
      (canonicalHyperplane (quotientLift componentAndPoint point steps))
      (jetQuotientMap steps Polynomial.X) (characteristic componentAndPoint) = 0 :=
  characteristic_eval_zero_at_quotientLift componentAndPoint point
    point_root point_nonsingular steps

/-- Executable precision-three canary.  The branch
`x₀ = 1/(1-s), x₁ = 0` begins `1+s+s²`; mutating the first equation changes
the residual below degree three. -/
def runChecks : IO Unit := do
  let coordinates : Fin 2 → CPolynomial F :=
    ![CPolynomial.C 1 + CPolynomial.X + CPolynomial.X ^ 2, 0]
  let values := fun i =>
    (componentAndPoint i).eval₂ CompPoly.CPolynomial.CHom coordinates -
      CPolynomial.X * coordinates i ^ denseDegree (componentAndPoint i)
  unless (List.range 3).all (fun degree =>
      (values 0).coeff degree == 0 && (values 1).coeff degree == 0) do
    throw (IO.userError "Rojas finite-jet deformation: residual did not vanish through degree two")
  let mutated : Fin 2 → CMvPolynomial 2 F
    | 0 => CMvPolynomial.X 0 * (CMvPolynomial.X 0 - CMvPolynomial.C 2)
    | 1 => CMvPolynomial.X 0 * CMvPolynomial.X 1
  let changed := (mutated 0).eval₂ CompPoly.CPolynomial.CHom coordinates -
    CPolynomial.X * coordinates 0 ^ denseDegree (mutated 0)
  unless (List.range 3).any (fun degree => changed.coeff degree != 0) do
    throw (IO.userError "Rojas finite-jet deformation: equation mutation was not detected")
  IO.println "Rojas finite-jet deformation: precision-three lift and mutation passed"

#print axioms X_pow_succ_dvd_equationValue_liftStep
#print axioms X_pow_succ_dvd_equationValue_liftJet
#print axioms mappedLift_is_deformedAffineRoot
#print axioms characteristic_eval_zero_at_mappedLift
#print axioms quotientLift_is_deformedAffineRoot
#print axioms characteristic_eval_zero_at_quotientLift

end RojasFiniteJetDeformationTests
