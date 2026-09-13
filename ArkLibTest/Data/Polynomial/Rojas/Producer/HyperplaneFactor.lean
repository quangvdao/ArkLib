/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneFactor

/-! Compile-time checks for symbolic affine-hyperplane factorization. -/

namespace RojasHyperplaneFactorTests

open scoped BigOperators
open MvPolynomial
open ArkLib.Rojas.Producer.HyperplaneFactor

example : affineLinearForm (fun _ : Fin 2 => (3 : ℤ)) =
    X 0 + C 3 * X 1 + C 3 * X 2 := by
  rw [affineLinearForm_eq]
  simp [Fin.sum_univ_two]

example (point : Fin 2 → ℚ) (q : MvPolynomial (Fin 3) ℚ) :
    affineLinearForm point ∣ affineLinearForm point * q := by
  exact dvd_mul_right _ _

example (point : Fin 2 → ℚ) (q : MvPolynomial (Fin 3) ℚ) :
    hyperplaneSubstitution point (affineLinearForm point * q) = 0 := by
  exact (affineLinearForm_dvd_iff point _).1 (dvd_mul_right _ _)

#print axioms ArkLib.Rojas.Producer.HyperplaneFactor.affineLinearForm_dvd_iff
#print axioms ArkLib.Rojas.Producer.HyperplaneFactor.affineLinearForm_dvd_of_substitution_eq_zero

end RojasHyperplaneFactorTests
