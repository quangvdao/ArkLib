/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/

import ArkLib.Data.Polynomial.UniversalHenselScaling
import ArkLib.Data.Polynomial.EvaluationCoefficient

/-!
# Universal numerators of an exact polynomial root

For an exact root with zero constant coefficient and nonzero slope at the origin, the universal
numerator at positive index `n` is exactly the root coefficient times `s^(2*n-1)`.
This is an algebraic identity for a supplied polynomial root, not a root-existence theorem.

## References

Adapted from Jieyi Long's universal numerator specialization, building on Remco Bloemen's BCHKS
formalization:

* Repository: https://github.com/proximity-prize/proximity-prize
* Commit: `19bc7d3e21b2261257e1961acd720b2c395d87e1`
* File: `ProximityPrize/SubmissionLower/BCHKSUniversalNumerator.lean`
-/

namespace Polynomial.UniversalHenselNumerator

variable {L : Type*} [Field L]

/-- The exact-root equation determines the omitted coefficient through the slope at the origin. -/
theorem slope_mul_root_coeff_eq_neg_prefix (R : Polynomial (Polynomial L)) (V : Polynomial L)
    (n : ℕ) (hV0 : V.coeff 0 = 0) (hroot : R.eval V = 0) :
    (R.coeff 1).coeff 0 * V.coeff n =
      -(R.eval (positivePrefix V.coeff n)).coeff n := by
  have hzero : V.coeff 0 = (positivePrefix V.coeff n).coeff 0 := by
    simp [hV0, positivePrefix_coeff]
  have hprev : ∀ i, i < n → V.coeff i = (positivePrefix V.coeff n).coeff i := by
    intro i hi
    rw [positivePrefix_coeff]
    by_cases hi0 : i = 0
    · subst i; simp [hV0]
    · simp [hi, Nat.pos_of_ne_zero hi0]
  have h := coeff_eval_sub_of_coeff_eq_below R V (positivePrefix V.coeff n) n hzero hprev
  simpa [hroot, hV0, ← coeff_zero_eq_eval_zero, coeff_derivative] using h.symm

/-- Every positive universal numerator is the exact polynomial-root coefficient with its
denominator cleared. The degree cap bounds the equation, not the root. -/
theorem numerators_eq_slope_pow_mul_root_coeff (R : Polynomial (Polynomial L))
    (V : Polynomial L) (s : L) (hs : s ≠ 0) (d : ℕ) (hV0 : V.coeff 0 = 0)
    (hdeg : R.natDegree ≤ d) (hslope : (R.coeff 1).coeff 0 = s) (hroot : R.eval V = 0)
    (n : ℕ) (hn : 0 < n) :
    numerators R s d n = s ^ (2 * n - 1) * V.coeff n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [numerators_succ]
    have hrel : ∀ i, 0 < i → i < t + 1 →
        (if i ≤ t then numerators R s d i else 0) = s ^ (2 * i - 1) * V.coeff i := by
      intro i hi hit
      rw [if_pos (by omega)]
      exact ih i hit hi
    rw [numeratorStep_eq_neg_slope_pow_mul_eval_coeff R s hs d (t + 1)
      _ V.coeff (by omega) hdeg hrel]
    have hcoeff := slope_mul_root_coeff_eq_neg_prefix R V (t + 1) hV0 hroot
    rw [hslope] at hcoeff
    have hexp : 2 * (t + 1) - 1 = (2 * (t + 1) - 2) + 1 := by omega
    calc
      _ = s ^ (2 * (t + 1) - 2) *
          (-(R.eval (positivePrefix V.coeff (t + 1))).coeff (t + 1)) := by ring
      _ = s ^ (2 * (t + 1) - 2) * (s * V.coeff (t + 1)) := by rw [hcoeff]
      _ = _ := by rw [hexp, pow_add, pow_one]; ring

end Polynomial.UniversalHenselNumerator
