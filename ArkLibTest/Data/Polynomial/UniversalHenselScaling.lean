/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.UniversalHenselScaling
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Cleared residual acceptance client

A padded outer cap of four is used for the quadratic equation `V² + 2V - U`.
The true previous coefficient is `1/2`, its numerator is `1`, and the next residual is
`1/4`. The endpoint recovers the second numerator `-1` by clearing with `2²`.
-/

open Polynomial Polynomial.UniversalHenselNumerator

private noncomputable def shifted : Polynomial (Polynomial ℚ) := X ^ 2 + C 2 * X - C X

example : numeratorStep shifted 2 4 2 (fun _ ↦ 1) = -1 := by
  have hdeg : shifted.natDegree ≤ 4 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · norm_num
      · apply natDegree_mul_le.trans
        norm_num
    · simp
  have hrel : ∀ i : ℕ, 0 < i → i < 2 →
      (1 : ℚ) = 2 ^ (2 * i - 1) * (1 / 2) := by
    intro i hi hn
    have : i = 1 := by omega
    subst i
    norm_num
  rw [numeratorStep_eq_neg_slope_pow_mul_eval_coeff shifted 2 (by norm_num)
    4 2 (fun _ ↦ 1) (fun _ ↦ 1 / 2) (by norm_num) hdeg hrel]
  norm_num [shifted, positivePrefix, Finset.sum_Ico_succ_top,
    coeff_X, coeff_one, coeff_monomial]

-- Below the number of factors the coefficient vanishes even over a ring with zero divisors.
example : ((positivePrefix (fun _ ↦ (3 : ZMod 6)) 4) ^ 3).coeff 2 = 0 := by
  exact positivePrefix_pow_coeff_eq_zero_of_lt _ 4 3 2 (by norm_num)
