/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.UniversalHenselRoot
import Mathlib.Tactic.NormNum

/-!
# Exact-root universal numerator client

The quadratic equation `(Y-(U⁵+U²+U))*(Y+2)` has root degree five but outer equation cap four.
Its second numerator is eight, its fifth is 512, and its sixth is zero. This checks the odd
clearing exponent and the fact that the equation cap does not constrain the supplied root.
-/

open Polynomial Polynomial.UniversalHenselNumerator

private noncomputable def root : Polynomial ℚ := X ^ 5 + X ^ 2 + X

private noncomputable def equation : Polynomial (Polynomial ℚ) := (X - C root) * (X + C 2)

private theorem representation (n : ℕ) (hn : 0 < n) :
    numerators equation 2 4 n = 2 ^ (2 * n - 1) * root.coeff n := by
  apply numerators_eq_slope_pow_mul_root_coeff equation root 2 (by norm_num) 4
  · simp [root]
  · apply natDegree_mul_le.trans
    have hleft : (X - C root).natDegree ≤ 1 := by simp
    have hright : (X + C (2 : Polynomial ℚ)).natDegree ≤ 1 := by
      apply (natDegree_add_le _ _).trans
      simp
    exact (Nat.add_le_add hleft hright).trans (by norm_num)
  · have hcoeff : equation.coeff 1 = 2 - root := by
      simp [equation, mul_coeff_one, sub_eq_add_neg, add_comm]
    rw [hcoeff]
    norm_num [root]
  · simp [equation]
  · exact hn

example : numerators equation 2 4 2 = 8 ∧
    numerators equation 2 4 5 = 512 ∧ numerators equation 2 4 6 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [representation 2 (by norm_num)]
    norm_num [root, coeff_X]
  · rw [representation 5 (by norm_num)]
    norm_num [root, coeff_X]
  · rw [representation 6 (by norm_num)]
    norm_num [root, coeff_X]

#print axioms Polynomial.coeff_eval_sub_of_coeff_eq_below
#print axioms Polynomial.UniversalHenselNumerator.numerators_eq_slope_pow_mul_root_coeff
