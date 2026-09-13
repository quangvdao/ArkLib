/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.ResultantSemantics
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and runtime checks for input-derived Macaulay determinant semantics. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.ResultantSemantics

namespace RojasResultantSemanticsTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def original : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 - C 1
  | 1 => X 1 - C 2

private def mutated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 - C 3
  | 1 => X 1 - C 2

private def root : Fin 2 → F := ![1, 2]

private def hyperplane : Fin 3 → F := ![2, 1, 2]

private theorem original_root :
    IsCommonAffineRoot (RingHom.id F) root original := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [original, root, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem root_on_hyperplane : affineLinearValue hyperplane root = 0 := by
  decide

example : parameterEvalHom (RingHom.id F) hyperplane 0
    (characteristic original) = 0 :=
  characteristic_eval_zero_of_affineRoot (RingHom.id F) hyperplane root original
    root_on_hyperplane original_root

/-- A decisive mutation check: the same parameter specialization vanishes for
an input root and becomes nonzero after changing one input equation. -/
def runChecks : IO Unit := do
  let before := parameterEvalHom (RingHom.id F) hyperplane 0
    (characteristic original)
  let after := parameterEvalHom (RingHom.id F) hyperplane 0
    (characteristic mutated)
  unless before == 0 do
    throw (IO.userError "Rojas determinant semantics: affine-root specialization did not vanish")
  unless after == 2 do
    throw (IO.userError
      "Rojas determinant semantics: equation mutation did not change the determinant")
  IO.println "Rojas determinant semantics: affine vanishing and equation mutation passed"

#print axioms specializedMatrix_mulVec_apply
#print axioms specializedMatrix_mulVec_eq_zero
#print axioms characteristic_eval_eq_zero_of_commonProjectiveRoot
#print axioms commonProjectiveRoot_of_affineRoot
#print axioms characteristic_eval_zero_of_affineRoot

end RojasResultantSemanticsTests
