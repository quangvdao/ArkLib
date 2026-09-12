/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Substitution
import Mathlib.Tactic.FinCases

/-! # Boundary regression tests -/

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential MvPolynomial
open scoped BigOperators

/-! ### Boundary canaries -/

/-- At the rejected boundary `D=d`, the top jet's differential weight truncates to zero while
the `Y₀` image needs the larger cap `d+1`. -/
theorem differentialFormula_truncation_boundary_canary :
    2 - (Fin.last 2).val = 0 ∧
      ¬localSubstitutionSourceWeight 2 (some 0) ≤ 2 - (0 : Fin 3).val := by
  decide

/-- At order two, this checks both alternating signs and the distinct error factors `T` and
`T³`. -/
theorem substitution_order_two_canary :
    let source : DifferentialPolynomial ℤ 2 :=
      X (some 0) * X (some (Fin.succ (1 : Fin 2)))
    let t : LocalPolynomial ℤ 2 := X (localT 2)
    let e : LocalPolynomial ℤ 2 := X (localE 2)
    let y₁ : LocalPolynomial ℤ 2 := X (localY (0 : Fin 2))
    let y₂ : LocalPolynomial ℤ 2 := X (localY (1 : Fin 2))
    unscaledLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t * e) * y₂ ∧
      normalizedLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t ^ 3 * e) * y₂ := by
  dsimp only
  constructor
  · rw [map_mul, unscaledLocalSubstitution_Y_zero,
      unscaledLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring
  · rw [map_mul, normalizedLocalSubstitution_Y_zero,
      normalizedLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring

end ReedSolomon.HiddenDerivative
