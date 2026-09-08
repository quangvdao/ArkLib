/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.SymbolicInterpolation
import ArkLib.Data.Polynomial.SymbolicCurveSurplus

/-!
# Improved interpolation for symbolic polynomial curves

For a curve of degree at most `M`, the YZ weight is `(M, 1)` and the strict real budget
is `M * D_Z`. The construction rounds this product itself, so no extra rounding factor
enters the degree bound. The nesting and normalized X/Y budgets agree with the affine endpoint.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Lemma 3.1 and Section 4.1.
-/

namespace ProximityGap

open Polynomial Polynomial.SymbolicInterpolation

variable {F : Type} [Field F] [DecidableEq F]

/-- The improved symbolic curve interpolant with an explicit normalized rate.
The scalar count is proved for `ceil (M*D_Z)`, with no surplus premise left to the caller. -/
theorem exists_curve_interpolant_of_rate (M n k m : ℕ) (r : ℝ)
    (hM : 0 < M) (hn : 0 < n) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ) = n * r ^ 2) (x : Fin n → F) (y : Fin n → Polynomial F)
    (hy : ∀ a, (y a).natDegree ≤ M) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        (j : ℝ) < ((m : ℝ) + 1 / 2) / r ∧
        ((i + k * j : ℕ) : ℝ) < (k : ℝ) * (((m : ℝ) + 1 / 2) / r) ∧
        ((M * j + h : ℕ) : ℝ) < (M : ℝ) * (((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2))) ∧
      ∀ a, (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C (x a)) (y a) := by
  let dy : ℝ := ((m : ℝ) + 1 / 2) / r
  let dz : ℝ := ((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)
  obtain ⟨Q, hQ, hsupport, hvan⟩ := exists_curve_polynomial_of_card_surplus M k
    ⌈(k : ℝ) * dy⌉₊ ⌈dy⌉₊ ⌈(M : ℝ) * dz⌉₊ n m x y hy
    (card_curve_constraints_lt_monomials M n k m r hM hn hm hr hr1 hkr)
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro i j h hc
    obtain ⟨hj, hij, hjh⟩ := hsupport i j h hc
    exact ⟨Nat.lt_ceil.mp hj, Nat.lt_ceil.mp hij, Nat.lt_ceil.mp hjh⟩
  · intro a
    exact (Bivariate.le_rootMultiplicity_iff_of_ne_zero Q hQ _ _ m).mpr (hvan a)

/-- The improved curve interpolant with rate fixed by the code parameters and the printed
square-root X budget. The polynomial curve may be inseparable. -/
theorem exists_curve_interpolant (M n k m : ℕ)
    (hM : 0 < M) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) (hm : 3 ≤ m)
    (x : Fin n → F) (y : Fin n → Polynomial F) (hy : ∀ a, (y a).natDegree ≤ M) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        (j : ℝ) < ((m : ℝ) + 1 / 2) / Real.sqrt ((k : ℝ) / n) ∧
        ((i + k * j : ℕ) : ℝ) <
          ((m : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) * k) ∧
        ((M * j + h : ℕ) : ℝ) < (M : ℝ) *
          (((m : ℝ) + 1 / 2) ^ 2 / (3 * (Real.sqrt ((k : ℝ) / n)) ^ 2))) ∧
      ∀ a, (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C (x a)) (y a) := by
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
    exists_curve_interpolant_of_rate M n k m _ hM hn hm hr hr1 hkr x y hy
  refine ⟨Q, hQ, ?_, hmult⟩
  intro i j h hc
  obtain ⟨hj, hij, hjh⟩ := hsupport i j h hc
  rw [affine_x_budget_eq_sqrt n k m _ hr hkr] at hij
  exact ⟨hj, hij, hjh⟩

end ProximityGap
