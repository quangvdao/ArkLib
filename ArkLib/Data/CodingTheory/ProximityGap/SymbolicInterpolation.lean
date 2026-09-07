/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolation
import ArkLib.Data.Polynomial.SymbolicInterpolationSurplus
import ArkLib.Data.Polynomial.BivariateMultiplicity
import Mathlib.Analysis.Real.Sqrt

/-!
# Improved affine symbolic interpolation

This is the interpolation conclusion of [BCHKS25, Lemma 3.1] in the regime `0 < k ≤ n`.
The polynomial is nested as `F[Z][X][Y]`: its coefficient indices are Y, X, Z.
The normalized rate parameter is `r = sqrt (k/n)`, so the X budget is
`k * (m + 1/2) / r`, the Y budget is `(m + 1/2) / r`, and the YZ budget is
`(m + 1/2)^2 / (3*r^2)`. Every scalar coefficient obeys these strict real bounds.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Lemma 3.1.
-/

namespace ProximityGap

open Polynomial Polynomial.SymbolicInterpolation

variable {F : Type} [Field F] [DecidableEq F]

/-- The improved symbolic affine interpolant, with the rate identity exposed explicitly.
There is no unproved dimension-surplus premise and no restriction on the field characteristic. -/
theorem exists_affine_interpolant_of_rate (n k m : ℕ) (r : ℝ)
    (hn : 0 < n) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ) = n * r ^ 2) (x u₀ u₁ : Fin n → F) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        (j : ℝ) < ((m : ℝ) + 1 / 2) / r ∧
        ((i + k * j : ℕ) : ℝ) < (k : ℝ) * (((m : ℝ) + 1 / 2) / r) ∧
        ((j + h : ℕ) : ℝ) < ((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)) ∧
      ∀ a, (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C (x a))
        (C (u₀ a) + Polynomial.X * C (u₁ a)) := by
  let dy : ℝ := ((m : ℝ) + 1 / 2) / r
  let dz : ℝ := ((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)
  let y : Fin n → Polynomial F := fun a => C (u₀ a) + Polynomial.X * C (u₁ a)
  have hy : ∀ a, (y a).natDegree ≤ 1 := by
    intro a
    dsimp [y]
    rw [show C (u₀ a) + Polynomial.X * C (u₁ a) =
      C (u₁ a) * Polynomial.X + C (u₀ a) by ring]
    exact natDegree_linear_le
  obtain ⟨Q, hQ, hsupport, hvan⟩ := exists_polynomial_of_card_surplus k
    ⌈(k : ℝ) * dy⌉₊ ⌈dy⌉₊ ⌈dz⌉₊ n m x y hy
    (card_constraints_lt_monomials n k m r hn hm hr hr1 hkr)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro i j h hc
    obtain ⟨hj, hij, hjh⟩ := hsupport i j h hc
    exact ⟨Nat.lt_ceil.mp hj, Nat.lt_ceil.mp hij, Nat.lt_ceil.mp hjh⟩
  · intro a
    exact (Bivariate.le_rootMultiplicity_iff_of_ne_zero Q hQ _ _ m).mpr (hvan a)

/-- The rate-normalized X budget equals the square-root budget printed in the paper. -/
theorem affine_x_budget_eq_sqrt (n k : ℕ) (m r : ℝ)
    (hr : 0 < r) (hkr : (k : ℝ) = n * r ^ 2) :
    (k : ℝ) * ((m + 1 / 2) / r) = (m + 1 / 2) * Real.sqrt ((n : ℝ) * k) := by
  have hsqrt : Real.sqrt ((n : ℝ) * k) = n * r := by
    rw [hkr, show (n : ℝ) * (n * r ^ 2) = ((n : ℝ) * r) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsqrt, hkr]
  field_simp

/-- The improved affine interpolant with `r = sqrt (k/n)` determined by the code parameters. -/
theorem exists_affine_interpolant (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) (hm : 3 ≤ m)
    (x u₀ u₁ : Fin n → F) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        (j : ℝ) < ((m : ℝ) + 1 / 2) / Real.sqrt ((k : ℝ) / n) ∧
        ((i + k * j : ℕ) : ℝ) <
          ((m : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) * k) ∧
        ((j + h : ℕ) : ℝ) <
          ((m : ℝ) + 1 / 2) ^ 2 / (3 * (Real.sqrt ((k : ℝ) / n)) ^ 2)) ∧
      ∀ a, (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C (x a))
        (C (u₀ a) + Polynomial.X * C (u₁ a)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : 0 < Real.sqrt ((k : ℝ) / n) := Real.sqrt_pos.mpr (div_pos hkR hnR)
  have hr1 : Real.sqrt ((k : ℝ) / n) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one hnR).mpr (by exact_mod_cast hkn)
  have hkr : (k : ℝ) = n * (Real.sqrt ((k : ℝ) / n)) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg hkR.le hnR.le)]
    field_simp
  obtain ⟨Q, hQ, hsupport, hmult⟩ :=
    exists_affine_interpolant_of_rate n k m _ hn hm hr hr1 hkr x u₀ u₁
  refine ⟨Q, hQ, ?_, hmult⟩
  intro i j h hc
  obtain ⟨hj, hij, hjh⟩ := hsupport i j h hc
  rw [affine_x_budget_eq_sqrt n k m _ hr hkr] at hij
  exact ⟨hj, hij, hjh⟩

end ProximityGap
