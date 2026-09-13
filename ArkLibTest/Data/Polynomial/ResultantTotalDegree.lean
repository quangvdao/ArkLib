/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ResultantTotalDegree
import Mathlib.Algebra.Field.ZMod

/-! Theorem-level checks for multivariate coefficient bounds on Sylvester resultants. -/

open Polynomial

-- Unequal budgets expose accidental reversal of the two Sylvester column blocks.
example :
    (resultant
      (X - C ((MvPolynomial.X (0 : Fin 2)) ^ 5 : MvPolynomial (Fin 2) ℤ))
      (X ^ 3) 1 3).totalDegree = 15 := by
  rw [resultant_X_sub_C_left _ _ _ (by simp)]
  simp only [eval_pow, eval_X]
  rw [← pow_mul, MvPolynomial.totalDegree_X_pow]

-- The weighted padded bound needs only a commutative coefficient ring.
example (P Q : Polynomial (MvPolynomial (Fin 4) (ZMod 4))) (m n A B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ A)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q m n).totalDegree ≤ n * A + m * B :=
  totalDegree_resultant_le_of_coeff_totalDegree_le P Q m n A B hP hQ

-- The ready-to-use uniform envelope discharges from outer and coefficient budgets alone.
example (P Q : Polynomial (MvPolynomial (Fin 3) (ZMod 4))) (Bjet : ℕ)
    (hPdegree : P.natDegree ≤ Bjet) (hQdegree : Q.natDegree ≤ Bjet)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ Bjet - 1)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ Bjet - 1) :
    (resultant P Q).totalDegree ≤ 2 * Bjet * (Bjet - 1) :=
  totalDegree_resultant_le_two_mul_degreeBudget P Q Bjet hPdegree hQdegree hP hQ

-- Derivative coefficients inherit the original parameter budget in every characteristic.
example (P : Polynomial (MvPolynomial (Fin 2) (ZMod 3))) (B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ B) :
    (resultant P P.derivative).totalDegree ≤ (2 * P.natDegree - 1) * B :=
  totalDegree_resultant_derivative_le_of_coeff_totalDegree_le P B hP

-- The actual-degree API has the orientation needed by the chart obstruction bound.
example (P Q : Polynomial (MvPolynomial (Fin 3) (ZMod 5))) (A B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ A)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q).totalDegree ≤ Q.natDegree * A + P.natDegree * B :=
  totalDegree_resultant_le_of_coeff_totalDegree_le_actual P Q A B hP hQ

-- Equal coefficient budgets collapse to a sum of the two outer degrees.
example (P Q : Polynomial (MvPolynomial (Fin 1) ℤ)) (B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ B)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q).totalDegree ≤ (Q.natDegree + P.natDegree) * B :=
  totalDegree_resultant_le_of_coeff_totalDegree_le_common P Q B hP hQ
