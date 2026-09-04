/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.CharacteristicObstruction

/-!
# Concrete canary for the bounded-characteristic obstruction

The characteristic-two observation checks the sharp minimal prime boundary and ensures that the
Frobenius witness is genuinely quadratic.  The characteristic-three observations check that the
collision is not an artifact of `2 = 0`, that the jet uses its supplied center, and that the
separant is the nonzero constant one.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

local instance characteristicObstructionCanaryPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance characteristicObstructionCanaryPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Direct boundary observations: the characteristic-two witness has degree two, while the
characteristic-three Frobenius witness has jet `[0, 0]` at zero and `[1, 0]` at one. -/
example :
    (frobeniusFirstJetSolution 2 2 le_rfl).polynomial.natDegree = 2 ∧
      polynomialJet (d := 1) (0 : ZMod 3)
          (frobeniusFirstJetSolution 3 3 le_rfl).polynomial = ![0, 0] ∧
      polynomialJet (d := 1) (1 : ZMod 3)
          (frobeniusFirstJetSolution 3 3 le_rfl).polynomial = ![1, 0] ∧
      separant (characteristicFirstJetEquation 3) (1 : Fin 2) = 1 := by
  constructor
  · simp
  constructor
  · funext j
    fin_cases j <;> norm_num [polynomialJet, hasseDeriv_monomial]
  constructor
  · funext j
    fin_cases j
    · norm_num [polynomialJet, hasseDeriv_monomial]
    · norm_num [polynomialJet, hasseDeriv_monomial]
      exact ZMod.natCast_self 3
  · exact characteristicFirstJetEquation_separant 3

end

end ReedSolomon.HiddenDerivative
