/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationSurplus
import ArkLib.Data.Polynomial.SymbolicCurveInterpolation

/-!
# Rounded surplus for polynomial curves

Normalize an integer curve budget by its positive curve degree before counting. This preserves
the source budget `ceil (M * D_Z)`, without replacing it by the larger `M * ceil D_Z`.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
    *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Sections 3.1 and 4.1.
-/

namespace Polynomial.SymbolicInterpolation

open Finset

/-- Exact curve count at a real normalized budget, when no row truncates. -/
theorem card_curveMonomialSupport_eq_polynomial (M k dx d b : ℕ) (z : ℝ)
    (hb : (b : ℝ) = M * z) (hx : ∀ j < d, k * j ≤ dx)
    (hz : ∀ j < d, M * j ≤ b) :
    ((curveMonomialSupport M k dx d b).card : ℝ) =
      M * variableCountPolynomial k dx d z := by
  rw [card_curveMonomialSupport_sum, Nat.cast_sum, ← sum_untruncated_monomial_rows,
    mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Nat.cast_mul, Nat.cast_sub (hx j (mem_range.mp hj)),
    Nat.cast_sub (hz j (mem_range.mp hj)), Nat.cast_mul, Nat.cast_mul, hb]
  ring

/-- Exact scalar constraint count at the same real normalized budget. -/
theorem card_curveConstraintSupport_eq_polynomial (M m b : ℕ) (z : ℝ)
    (hb : (b : ℝ) = M * z) (hz : ∀ s < m, M * s ≤ b) :
    ((curveConstraintSupport M m b).card : ℝ) =
      M * (z * m * (m + 1) / 2 - ((m : ℝ) ^ 3 - m) / 6) := by
  have heq : ((curveConstraintSupport M m b).card : ℝ) =
      M * variableCountPolynomial 1 m m z := by
    rw [card_curveConstraintSupport_sum, Nat.cast_sum,
      ← sum_untruncated_monomial_rows, mul_sum]
    apply sum_congr rfl
    intro s hs
    rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt (mem_range.mp hs)),
      Nat.cast_sub (hz s (mem_range.mp hs)), Nat.cast_mul, hb]
    ring
  rw [heq]
  unfold variableCountPolynomial
  ring

/-- The prescribed coefficient budget covers even the rounded Y budget. -/
theorem ceil_y_le_coefficient_budget (m r : ℝ) (hm : 3 ≤ m)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (⌈(m + 1 / 2) / r⌉₊ : ℝ) ≤ (m + 1 / 2) ^ 2 / (3 * r ^ 2) := by
  let y := (m + 1 / 2) / r
  have hy : (7 / 2 : ℝ) ≤ y := by
    apply (le_div_iff₀ hr).mpr
    linarith
  have hid : (m + 1 / 2) ^ 2 / (3 * r ^ 2) = y ^ 2 / 3 := by
    dsimp [y]
    field_simp
  rw [hid]
  change (⌈y⌉₊ : ℝ) ≤ y ^ 2 / 3
  by_cases hy4 : y ≤ 4
  · have hc : ⌈y⌉₊ ≤ 4 := Nat.ceil_le.mpr hy4
    have hcR : (⌈y⌉₊ : ℝ) ≤ 4 := by exact_mod_cast hc
    nlinarith
  · have hc := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
    nlinarith [sq_nonneg (y - 4)]

/-- Actual curve surplus for any integer coefficient budget above the prescribed real budget. -/
theorem card_curve_constraints_lt_monomials_of_budget (M n k m b : ℕ) (r : ℝ)
    (hM : 0 < M) (hn : 0 < n) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ) = n * r ^ 2)
    (hb : (M : ℝ) * (((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2)) ≤ b) :
    n * (curveConstraintSupport M m b).card <
      (curveMonomialSupport M k ⌈(k : ℝ) * (((m : ℝ) + 1 / 2) / r)⌉₊
        ⌈((m : ℝ) + 1 / 2) / r⌉₊ b).card := by
  let y : ℝ := ((m : ℝ) + 1 / 2) / r
  let z : ℝ := (b : ℝ) / M
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hbz : (b : ℝ) = M * z := by dsimp [z]; field_simp
  have hbudget : ((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2) ≤ z := by
    apply (le_div_iff₀ hMR).mpr
    simpa [mul_comm] using hb
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hdz : (⌈y⌉₊ : ℝ) ≤ z :=
    (ceil_y_le_coefficient_budget m r hmR hr hr1).trans hbudget
  have hyz : y ≤ z := (Nat.le_ceil y).trans hdz
  have hmy : (m : ℝ) ≤ y := by
    apply (le_div_iff₀ hr).mpr
    have := mul_le_mul_of_nonneg_left hr1 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hx : ∀ j < ⌈y⌉₊, k * j ≤ ⌈(k : ℝ) * y⌉₊ := by
    intro j hj
    have hjy : (j : ℝ) < y := Nat.lt_ceil.mp hj
    have h := (mul_le_mul_of_nonneg_left hjy.le (Nat.cast_nonneg k)).trans
      (Nat.le_ceil ((k : ℝ) * y))
    exact_mod_cast h
  have hz : ∀ j < ⌈y⌉₊, M * j ≤ b := by
    intro j hj
    have hjy : (j : ℝ) < y := Nat.lt_ceil.mp hj
    have h := mul_le_mul_of_nonneg_left (hjy.le.trans hyz) hMR.le
    rw [← hbz] at h
    exact_mod_cast h
  have hzm : ∀ s < m, M * s ≤ b := by
    intro s hs
    have hsR : (s : ℝ) ≤ m := by exact_mod_cast hs.le
    have h := mul_le_mul_of_nonneg_left (hsR.trans (hmy.trans hyz)) hMR.le
    rw [← hbz] at h
    exact_mod_cast h
  have hcount := card_curveMonomialSupport_eq_polynomial M k ⌈(k : ℝ) * y⌉₊
    ⌈y⌉₊ b z hbz hx hz
  have heq := card_curveConstraintSupport_eq_polynomial M m b z hbz hzm
  have hlow := variableCountPolynomial_lower_bound k ⌈(k : ℝ) * y⌉₊ y ⌈y⌉₊ z
    (Nat.cast_nonneg k) hy (Nat.le_ceil y) (Nat.ceil_lt_add_one hy).le hdz (Nat.le_ceil _)
  have hstrict := strict_surplus_of_coefficient_budget m r z (by linarith) hr hbudget
  change (r ^ 2 * y * (y + 1) - (m : ℝ) * (m + 1)) * z >
    (r ^ 2 * (y ^ 3 - y) - ((m : ℝ) ^ 3 - m)) / 3 at hstrict
  have hscaled := mul_lt_mul_of_pos_left hstrict hnR
  have hbase : (n : ℝ) * (z * m * (m + 1) / 2 - ((m : ℝ) ^ 3 - m) / 6) <
      variableCountPolynomial k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ z := by
    have hlow' : (n : ℝ) * r ^ 2 * (y * (y + 1) * z / 2 - (y ^ 3 - y) / 6) ≤
        variableCountPolynomial k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ z := by
      rw [← hkr]
      exact hlow
    nlinarith [hlow', hscaled]
  have htotal := mul_lt_mul_of_pos_left hbase hMR
  have hout : (n : ℝ) * (curveConstraintSupport M m b).card <
      (curveMonomialSupport M k ⌈(k : ℝ) * y⌉₊ ⌈y⌉₊ b).card := by
    rw [hcount, heq]
    nlinarith [htotal]
  exact_mod_cast hout

/-- Rounding the product `M * D_Z` itself suffices; rounding before multiplying is unnecessary. -/
theorem card_curve_constraints_lt_monomials (M n k m : ℕ) (r : ℝ)
    (hM : 0 < M) (hn : 0 < n) (hm : 3 ≤ m) (hr : 0 < r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ) = n * r ^ 2) :
    n * (curveConstraintSupport M m
      ⌈(M : ℝ) * (((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2))⌉₊).card <
      (curveMonomialSupport M k ⌈(k : ℝ) * (((m : ℝ) + 1 / 2) / r)⌉₊
        ⌈((m : ℝ) + 1 / 2) / r⌉₊
        ⌈(M : ℝ) * (((m : ℝ) + 1 / 2) ^ 2 / (3 * r ^ 2))⌉₊).card :=
  card_curve_constraints_lt_monomials_of_budget M n k m _ r hM hn hm hr hr1 hkr
    (Nat.le_ceil _)

end Polynomial.SymbolicInterpolation
