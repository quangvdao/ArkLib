/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.AffineDeformation
import Mathlib.Algebra.Field.ZMod

/-! Checks for the input-derived first-order Rojas deformation. -/

open scoped DualNumber
open CPoly CPoly.CMvPolynomial TrivSqZeroExt
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.ResultantSemantics
open ArkLib.Rojas.Producer.AffineDeformation

namespace RojasAffineDeformationTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The line `x₀ = 0` and the unrelated isolated root `(1,0)`. -/
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

example (i : Fin 2) :
    (dualPoint componentAndPoint point i).fst = point i :=
  fst_dualPoint componentAndPoint point i

example (i : Fin 2) :
    deformedEquationValue componentAndPoint DualNumber.eps
      (dualPoint componentAndPoint point) i = 0 :=
  deformedEquationValue_dualPoint_eq_zero componentAndPoint point
    point_root point_nonsingular i

example : parameterEvalHom (inlHom F F)
    (canonicalHyperplane (dualPoint componentAndPoint point)) DualNumber.eps
    (characteristic componentAndPoint) = 0 :=
  characteristic_eval_zero_at_canonicalDualLift componentAndPoint point
    point_root point_nonsingular

/-- Executable canary for the zero-coordinate isolated root: its computed
first-order point is `(1+ε,0)` and satisfies both deformed equations. -/
def runChecks : IO Unit := do
  let lifted : Fin 2 → DualNumber F := ![inl 1 + inr 1, 0]
  let values := fun i =>
    (componentAndPoint i).eval₂ (inlHom F F) lifted -
      DualNumber.eps * lifted i ^ denseDegree (componentAndPoint i)
  unless (values 0).fst == 0 && (values 0).snd == 0 &&
      (values 1).fst == 0 && (values 1).snd == 0 do
    throw (IO.userError "Rojas affine deformation: first-order equations did not vanish")
  let mutated : Fin 2 → CMvPolynomial 2 F
    | 0 => CMvPolynomial.X 0 * (CMvPolynomial.X 0 - CMvPolynomial.C 2)
    | 1 => CMvPolynomial.X 0 * CMvPolynomial.X 1
  let changed := (mutated 0).eval₂ (inlHom F F) lifted -
    DualNumber.eps * lifted 0 ^ denseDegree (mutated 0)
  unless changed.fst != 0 || changed.snd != 0 do
    throw (IO.userError "Rojas affine deformation: equation mutation was not detected")
  IO.println "Rojas affine deformation: lift, zero-coordinate root, and mutation passed"

#print axioms eval₂_dual_add
#print axioms deformedEquationValue_dualPoint_eq_zero
#print axioms characteristic_eval_eq_zero_of_commonAffineProjectiveRoot
#print axioms characteristic_eval_zero_at_canonicalDualLift

end RojasAffineDeformationTests
