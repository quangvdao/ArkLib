/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneCoverage
import Mathlib.Algebra.Field.ZMod

/-! Regression checks for affine-root factors of the constant `s` coefficient. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.HyperplaneFactor
open ArkLib.Rojas.Producer.HyperplaneCoverage
open ArkLib.Rojas.Producer.ResultantSemantics

namespace RojasHyperplaneCoverageTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Two isolated affine roots, `(0,0)` and `(1,0)`, both on a coordinate
hyperplane. -/
private def twoIsolated : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 1)
  | 1 => X 1

/-- The line `x₀ = 0` together with the unrelated isolated root `(1,0)`. -/
private def componentAndPoint : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 * (X 0 - C 1)
  | 1 => X 0 * X 1

private def linear : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 - C 1
  | 1 => X 1 - C 2

private def mutatedLinear : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 - C 3
  | 1 => X 1 - C 2

private theorem commonRoot_twoIsolated (point : Fin 2 → F)
    (hpoint : point = ![0, 0] ∨ point = ![1, 0]) :
    IsCommonAffineRoot (RingHom.id F) point twoIsolated := by
  rcases hpoint with rfl | rfl <;>
    intro i <;> fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [twoIsolated, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

private theorem commonRoot_componentAndPoint :
    IsCommonAffineRoot (RingHom.id F) ![1, 0] componentAndPoint := by
  intro i
  fin_cases i <;> rw [CPoly.eval₂_equiv] <;>
    simp [componentAndPoint, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X,
      CMvPolynomial.fromCMvPolynomial_C]

example : affineLinearForm (![0, 0] : Fin 2 → F) ∣
    fromCMvPolynomial (coefficientInS 0 (characteristic twoIsolated)) :=
  affineLinearForm_dvd_constantCharacteristic ![0, 0] twoIsolated
    (commonRoot_twoIsolated _ (Or.inl rfl))

example : affineLinearForm (![1, 0] : Fin 2 → F) ∣
    fromCMvPolynomial (coefficientInS 0 (characteristic twoIsolated)) :=
  affineLinearForm_dvd_constantCharacteristic ![1, 0] twoIsolated
    (commonRoot_twoIsolated _ (Or.inr rfl))

/-- Coverage of the isolated zero-coordinate root is unaffected by the
separate positive-dimensional component. -/
example : affineLinearForm (![1, 0] : Fin 2 → F) ∣
    fromCMvPolynomial
      (coefficientInS 0 (characteristic componentAndPoint)) :=
  affineLinearForm_dvd_constantCharacteristic ![1, 0] componentAndPoint
    commonRoot_componentAndPoint

/-- The compiled runtime checks the constant-coefficient specialization and
rejects an equation mutation at the same parameter point. -/
def runChecks : IO Unit := do
  let before := (coefficientInS 0 (characteristic linear)).eval ![2, 1, 2]
  let after := (coefficientInS 0 (characteristic mutatedLinear)).eval ![2, 1, 2]
  unless before == 0 do
    throw (IO.userError "Rojas hyperplane coverage: constant specialization did not vanish")
  unless after == 2 do
    throw (IO.userError "Rojas hyperplane coverage: equation mutation was not detected")
  IO.println "Rojas hyperplane coverage: constant specialization and mutation passed"

#print axioms eval₂_coefficientInS_zero
#print axioms hyperplaneSubstitution_constantCharacteristic_eq_zero
#print axioms affineLinearForm_dvd_constantCharacteristic

end RojasHyperplaneCoverageTests
