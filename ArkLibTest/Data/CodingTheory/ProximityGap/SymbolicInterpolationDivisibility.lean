/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.SymbolicInterpolationDivisibility
import ArkLib.Data.CodingTheory.ProximityGap.SymbolicCurveInterpolation
import Mathlib.Algebra.Field.ZMod

/-! A common factor is obtained both before and at a zero specialization. -/

open Polynomial

private noncomputable def interpolationPolynomial : Polynomial (Polynomial (Polynomial (ZMod 2))) :=
  Polynomial.monomial 1 (C Polynomial.X)

private def evaluationPoint : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem interpolationPolynomial_ne_zero : interpolationPolynomial ≠ 0 := by
  simp [interpolationPolynomial]

private theorem supportBound : ∀ i j h, ((interpolationPolynomial.coeff j).coeff i).coeff h ≠ 0 →
    ((i + 0 * j : ℕ) : ℝ) < 1 / 2 := by
    intro i j h hc
    by_cases hj : j = 1
    · subst j
      by_cases hi : i = 0
      · subst i
        norm_num
      · simp [interpolationPolynomial, coeff_C, hi] at hc
    · simp [interpolationPolynomial, coeff_monomial, Ne.symm hj] at hc

private theorem multiplicityBound : ∀ a, (some 1 : Option ℕ) ≤ Bivariate.rootMultiplicity
    interpolationPolynomial (C (evaluationPoint a)) 0 := by
    intro a
    apply (Bivariate.le_rootMultiplicity_iff_of_ne_zero _ interpolationPolynomial_ne_zero _ _ 1).mpr
    intro r s hrs
    have hr : r = 0 := by omega
    have hs : s = 0 := by omega
    subst r
    subst s
    simp [Bivariate.shift, interpolationPolynomial, evaluationPoint]

-- Q = Z*Y specializes to zero at z=0 and to Y at z=1. Both challenges are covered.
example (z : ZMod 2) : Polynomial.X ∣ Trivariate.evalAtZ z interpolationPolynomial := by
  have h : Polynomial.X - C (0 : Polynomial (ZMod 2)) ∣
      Trivariate.evalAtZ z interpolationPolynomial := by
    apply ProximityGap.linear_factor_dvd_specialization_of_agreement
      (k := 0) (m := 1) interpolationPolynomial interpolationPolynomial_ne_zero
      evaluationPoint (fun _ => 0) z Finset.univ 0 (1 / 2)
    · simp
    · exact supportBound
    · exact multiplicityBound
    · intro a ha
      simp
    · norm_num
  simpa using h

example : Trivariate.evalAtZ (0 : ZMod 2) interpolationPolynomial = 0 := by
  simp [Trivariate.evalAtZ, interpolationPolynomial]

example : Trivariate.evalAtZ (1 : ZMod 2) interpolationPolynomial = Polynomial.X := by
  simp [Trivariate.evalAtZ, interpolationPolynomial]
  rfl

-- The literal curve producer feeds the specialization consumer for all challenges.
-- The supplied agreement set contains four points, one more than the required three.
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (x : Fin 4 ↪ ZMod 5) :
    ∃ Q : Polynomial (Polynomial (Polynomial (ZMod 5))), Q ≠ 0 ∧
      ∀ z : ZMod 5, Polynomial.X - C (C (z ^ 2)) ∣ Trivariate.evalAtZ z Q := by
  obtain ⟨Q, hQ, hsupport, hmult⟩ := ProximityGap.exists_curve_interpolant
    2 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    x (fun _ => Polynomial.X ^ 2) (by intro a; simp)
  refine ⟨Q, hQ, fun z => ?_⟩
  apply ProximityGap.linear_factor_dvd_specialization_of_agreement
    (k := 1) (m := 3) Q hQ x (fun _ => Polynomial.X ^ 2) z Finset.univ
    (C (z ^ 2)) 7
  · simp
  · intro i j h hc
    have hbound := (hsupport i j h hc).2.1
    have hsqrt : Real.sqrt 4 = 2 := by
      norm_num [Real.sqrt_eq_iff_eq_sq]
    norm_num [hsqrt] at hbound ⊢
    exact hbound
  · exact hmult
  · intro a ha
    simp
  · norm_num
