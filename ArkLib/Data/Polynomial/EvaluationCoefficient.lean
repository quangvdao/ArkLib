/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Coefficient changes under polynomial evaluation

If two polynomial inputs agree below index `n` and have the same constant coefficient, their
evaluation coefficients at `n` differ by the specialized derivative times their coefficient
difference. This is the finite algebraic identity behind implicit-function coefficient recursion.

## References

Adapted from Jieyi Long's finite Hensel coefficient argument, building on Remco Bloemen's work:

* Repository: https://github.com/proximity-prize/proximity-prize
* Commit: `19bc7d3e21b2261257e1961acd720b2c395d87e1`
* File: `ProximityPrize/SubmissionLower/BCHKSFiniteHensel.lean`

Only polynomial algebra is used here; this module does not construct a second Hensel lift engine.
-/

namespace Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Polynomial divided difference, defined also when the two inputs coincide. -/
noncomputable def evalDividedDifference (P : A[X]) (u v : A) : A :=
  P.sum fun k c ↦ c * ∑ j ∈ Finset.range k, u ^ j * v ^ (k - 1 - j)

/-- Difference of evaluations factors through the divided difference. -/
theorem eval_sub_eval_eq_mul_evalDividedDifference (P : A[X]) (u v : A) :
    P.eval u - P.eval v = (u - v) * evalDividedDifference P u v := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [evalDividedDifference, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, ← (Commute.all u v).mul_geom_sum₂ k]
  ring

/-- On the diagonal the divided difference is the derivative. -/
theorem evalDividedDifference_self (P : A[X]) (y : A) :
    evalDividedDifference P y y = P.derivative.eval y := by
  rw [Polynomial.derivative_eval]
  simp only [evalDividedDifference, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _
  have hinner : (∑ j ∈ Finset.range k, y ^ j * y ^ (k - 1 - j)) =
      (k : A) * y ^ (k - 1) := by
    calc
      _ = ∑ _j ∈ Finset.range k, y ^ (k - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.mp hj
        omega
      _ = _ := by simp
  rw [hinner]
  ring

/-- Divided difference is additive in its polynomial argument. -/
theorem evalDividedDifference_add (P Q : A[X]) (u v : A) :
    evalDividedDifference (P + Q) u v =
      evalDividedDifference P u v + evalDividedDifference Q u v := by
  unfold evalDividedDifference
  apply Polynomial.sum_add_index
  · intro i; simp
  · intro i c d; rw [add_mul]

/-- Divided differences commute with coefficient specialization, including noninjective maps. -/
theorem map_evalDividedDifference (f : A →+* B) (P : A[X]) (u v : A) :
    f (evalDividedDifference P u v) =
      evalDividedDifference (P.map f) (f u) (f v) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
    rw [evalDividedDifference_add, map_add, ihP, ihQ, Polynomial.map_add,
      evalDividedDifference_add]
  | monomial n a => simp [evalDividedDifference, Polynomial.sum_monomial_index]

/-- If the left factor vanishes below `n`, only the right constant term contributes at `n`. -/
theorem coeff_mul_of_left_eq_zero_below (D Q : A[X]) (n : ℕ)
    (hD : ∀ i, i < n → D.coeff i = 0) :
    (D * Q).coeff n = D.coeff n * Q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  classical
  apply Finset.sum_eq_single (n, 0)
  · rintro ⟨a, b⟩ hp hne
    have hab : a + b = n := Finset.mem_antidiagonal.mp hp
    by_cases ha : a = n
    · have hb : b = 0 := by omega
      exact (hne (Prod.ext ha hb)).elim
    · rw [hD a (by omega), zero_mul]
  · intro hnot
    exact (hnot (by simp)).elim

/-- First differing input coefficient propagates through the derivative at the common constant. -/
theorem coeff_eval_sub_of_coeff_eq_below (R : Polynomial (Polynomial A)) (P Q : Polynomial A)
    (n : ℕ) (hzero : P.coeff 0 = Q.coeff 0)
    (hprev : ∀ i, i < n → P.coeff i = Q.coeff i) :
    (R.eval P).coeff n - (R.eval Q).coeff n =
      ((R.map (evalRingHom 0)).derivative.eval (P.coeff 0)) * (P.coeff n - Q.coeff n) := by
  have hD : ∀ i, i < n → (P - Q).coeff i = 0 := by
    intro i hi
    simp [hprev i hi]
  have hQ : (evalDividedDifference R P Q).coeff 0 =
      (R.map (evalRingHom 0)).derivative.eval (P.coeff 0) := by
    rw [coeff_zero_eq_eval_zero]
    change (evalRingHom 0) (evalDividedDifference R P Q) = _
    rw [map_evalDividedDifference]
    simp only [coe_evalRingHom, ← coeff_zero_eq_eval_zero, ← hzero,
      evalDividedDifference_self]
  rw [← coeff_sub, eval_sub_eval_eq_mul_evalDividedDifference,
    coeff_mul_of_left_eq_zero_below (P - Q) _ n hD, coeff_sub, hQ, mul_comm]

end Polynomial
