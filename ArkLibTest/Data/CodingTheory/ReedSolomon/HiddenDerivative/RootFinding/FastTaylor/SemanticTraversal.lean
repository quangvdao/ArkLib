/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.SemanticTraversal
import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.ActiveOrderAdapter
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance checks for concrete-to-semantic separant traversal -/

open CPoly PolynomialDifferential
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.FastTaylor

#check semanticEquation_partialDerivative
#check semanticEquation_eq_zero_iff
#check concreteDerivative_ne_zero_iff_dependsOnJet
#check highestConcreteActive?_eq_highestActiveJet
#check ConcreteStage.semantic_successor
#check mem_enumerateStagesFrom_semantic_contract
#check VaryingOrder.prefixEquation_represents
#check VaryingOrder.prefixEquation_exactOn_canonicalStages
#check jetDegreeMeasure_semantic_partialDerivative_lt
#check length_enumerateStages_le_jetDegreeMeasure
#check enumerateStages_regular_coverage

#print axioms semanticEquation_partialDerivative
#print axioms highestConcreteActive?_eq_highestActiveJet
#print axioms VaryingOrder.prefixEquation_exactOn_canonicalStages
#print axioms enumerateStages_regular_coverage

namespace FastTaylorSemanticTraversalTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable section

private def quadraticSemantic : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X (some 0) ^ 2

private def quadraticEquation : CMvPolynomial 2 (ZMod 5) :=
  ReedSolomon.HiddenDerivative.ActiveOrderAdapter.concrete quadraticSemantic

private def zeroSolution : BoundedSolution (semanticEquation quadraticEquation) 0 :=
  ⟨⟨0, by simp⟩, by
    rw [quadraticEquation,
      ReedSolomon.HiddenDerivative.ActiveOrderAdapter.semantic_concrete]
    simp [quadraticSemantic, differentialSpecialization]⟩

/-- The canonical fuel theorem carries the initially singular zero solution to the linear
derivative stage, where the next separant is nonzero. -/
example :
    ∃ stage ∈ enumerateStages
        (jetDegreeMeasure (semanticEquation quadraticEquation)) quadraticEquation,
      differentialSpecialization (semanticEquation stage.equation)
          zeroSolution.polynomial = 0 ∧
      differentialSpecialization
          (separant (semanticEquation stage.equation) stage.activeJet)
            zeroSolution.polynomial ≠ 0 ∧
      highestActiveJet (semanticEquation stage.equation) = some stage.activeJet := by
  apply enumerateStages_regular_coverage quadraticEquation
  · rw [quadraticEquation,
      ReedSolomon.HiddenDerivative.ActiveOrderAdapter.semantic_concrete]
    simp [quadraticSemantic]
  · constructor
    · norm_num [ZMod.ringChar_zmod_n]
    · intro j
      fin_cases j
      rw [quadraticEquation,
        ReedSolomon.HiddenDerivative.ActiveOrderAdapter.semantic_concrete]
      norm_num [quadraticSemantic, jetDegree, ZMod.ringChar_zmod_n]

/-- The canonical varying-order equation producer is proved exact on the actual bounded scan. -/
example :
    VaryingOrder.EquationProducer.ExactOn
  (VaryingOrder.prefixEquation (E := ZMod 5))
      (enumerateStages (jetDegreeMeasure (semanticEquation quadraticEquation))
        quadraticEquation) := by
  apply VaryingOrder.prefixEquation_exactOn_canonicalStages (D := 0)
  constructor
  · norm_num [ZMod.ringChar_zmod_n]
  · intro j
    fin_cases j
    rw [quadraticEquation,
      ReedSolomon.HiddenDerivative.ActiveOrderAdapter.semantic_concrete]
    norm_num [quadraticSemantic, jetDegree, ZMod.ringChar_zmod_n]

end

/-- A varying-order chain: the zero solution is singular at top order `Y₂`, then regular at the
lower-order `Y₁` stage. -/
private def varyingEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 * CMvPolynomial.X 2

def run : IO Unit := do
  let stages := enumerateStages 4 varyingEquation
  match stages with
  | [stage0, stage1] =>
      unless stage0.index == 0 && stage0.activeJet.val == 2 do
        throw (IO.userError "the first stage did not retain the actual top active order")
      unless stage1.index == 1 && stage1.activeJet.val == 1 do
        throw (IO.userError "the separant scan did not descend to the lower active order")
      unless stage1.equation == CMvPolynomial.X 2 do
        throw (IO.userError "the stored lower-order stage is not the literal first separant")
      unless VaryingOrder.prefixEquation stage1 == CMvPolynomial.X 2 do
        throw (IO.userError "the lower-order prefix equation changed its active coordinate")
      unless CMvPolynomial.partialDerivative stage1.activeJet.succ stage1.equation == 1 do
        throw (IO.userError "the lower-order stage did not have a nonzero terminal separant")
      let zeroJet : Fin 4 → ZMod 5 := fun _ => 0
      unless stage0.equation.eval zeroJet == 0 && stage1.equation.eval zeroJet == 0 do
        throw (IO.userError "the singular zero solution was not preserved across stages")
  | _ => throw (IO.userError "varying-order traversal did not emit exactly two active stages")

end FastTaylorSemanticTraversalTests
