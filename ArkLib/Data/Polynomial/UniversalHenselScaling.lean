/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/

import ArkLib.Data.Polynomial.UniversalHenselNumerator
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-!
# Clearing the universal numerator residual

If prior numerators are the prior coefficients multiplied by the odd powers of a nonzero
slope, the next universal step is the omitted-current residual multiplied by `s^(2*n-2)`.
This identifies the algebraic clearing factor; a root equation is still needed to identify
the residual with the next Taylor coefficient.

## References

Adapted from Jieyi Long's `BCHKSUniversalNumerator.lean`, building on Remco Bloemen's BCHKS work:

* Repository: https://github.com/proximity-prize/proximity-prize
* Commit: `19bc7d3e21b2261257e1961acd720b2c395d87e1`
* File: `ProximityPrize/SubmissionLower/BCHKSUniversalNumerator.lean`
-/

namespace Polynomial.UniversalHenselNumerator

variable {A : Type*} [CommRing A]

/-- Positive prefixes have no power coefficient below the number of factors. -/
theorem positivePrefix_pow_coeff_eq_zero_of_lt (c : ℕ → A) (n b u : ℕ) (hu : u < b) :
    ((positivePrefix c n) ^ b).coeff u = 0 := by
  have hx : (X : Polynomial A) ∣ positivePrefix c n := by
    rw [X_dvd_iff, positivePrefix_coeff]
    simp
  exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hx b) u hu

/-- Multiplying an odd-scaled prefix by its slope is ordinary variable scaling. -/
theorem positivePrefix_odd_scaled (s : A) (N c : ℕ → A) (n : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    C s * positivePrefix N n =
      (positivePrefix c n).comp (C (s ^ 2) * X) := by
  ext i
  rw [coeff_C_mul, comp_C_mul_X_coeff, positivePrefix_coeff, positivePrefix_coeff]
  by_cases hi : 0 < i ∧ i < n
  · rw [if_pos hi, if_pos hi, hrel i hi.1 hi.2]
    calc
      s * (s ^ (2 * i - 1) * c i) = s ^ (1 + (2 * i - 1)) * c i := by
        rw [pow_add]
        ring
      _ = s ^ (2 * i) * c i := by congr 2; omega
      _ = c i * (s ^ 2) ^ i := by rw [pow_mul]; ring
  · rw [if_neg hi, if_neg hi]
    simp

/-- Cross-multiplied coefficient scaling needs no inverse and holds over any commutative ring. -/
theorem positivePrefix_pow_cross_scaled (s : A) (N c : ℕ → A) (n b u : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    s ^ b * ((positivePrefix N n) ^ b).coeff u =
      s ^ (2 * u) * ((positivePrefix c n) ^ b).coeff u := by
  have hp := congrArg (fun p : Polynomial A ↦ p ^ b)
    (positivePrefix_odd_scaled s N c n hrel)
  have hpoly : C (s ^ b) * (positivePrefix N n) ^ b =
      ((positivePrefix c n) ^ b).comp (C (s ^ 2) * X) := by
    simpa only [mul_pow, ← C_pow, Polynomial.pow_comp] using hp
  have hc := congrArg (fun p : Polynomial A ↦ p.coeff u) hpoly
  simp only [coeff_C_mul, comp_C_mul_X_coeff] at hc
  rw [pow_mul]
  simpa [mul_comm] using hc

variable {L : Type*} [Field L]

/-- Cancelling the nonzero slope gives the exact power-coefficient clearing factor. -/
theorem positivePrefix_pow_coeff_scaled (s : L) (hs : s ≠ 0) (N c : ℕ → L) (n b u : ℕ)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    ((positivePrefix N n) ^ b).coeff u =
      s ^ (2 * u - b) * ((positivePrefix c n) ^ b).coeff u := by
  by_cases hub : u < b
  · rw [positivePrefix_pow_coeff_eq_zero_of_lt N n b u hub,
      positivePrefix_pow_coeff_eq_zero_of_lt c n b u hub]
    simp
  · apply mul_left_cancel₀ (pow_ne_zero b hs)
    rw [positivePrefix_pow_cross_scaled s N c n b u hrel, ← mul_assoc, ← pow_add]
    congr 2
    omega

/-- Each contributing residual summand has the same clearing exponent. -/
theorem residualTerm_scaled (Rshift : Polynomial (Polynomial L)) (s : L) (hs : s ≠ 0)
    (n a b : ℕ) (N c : ℕ → L) (hn : 1 ≤ n) (ha : a ≤ n)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    residualTerm Rshift s n a b N = s ^ (2 * n - 2) *
      (((Rshift.coeff b).coeff a) * ((positivePrefix c n) ^ b).coeff (n - a)) := by
  unfold residualTerm
  rw [positivePrefix_pow_coeff_scaled s hs N c n b (n - a) hrel]
  by_cases hbu : b ≤ n - a
  · by_cases hweight : 2 ≤ 2 * a + b
    · have hexp : (2 * a + b - 2) + (2 * (n - a) - b) = 2 * n - 2 := by omega
      calc
        _ = s ^ ((2 * a + b - 2) + (2 * (n - a) - b)) *
            ((Rshift.coeff b).coeff a * ((positivePrefix c n) ^ b).coeff (n - a)) := by
          rw [pow_add]
          ring
        _ = _ := by rw [hexp]
    · have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [coeff_one, Nat.ne_of_gt hn]
      · simp
  · rw [positivePrefix_pow_coeff_eq_zero_of_lt c n b (n - a) (by omega)]
    simp

/-- The next coefficient of evaluation at the prefix, with its current coefficient omitted. -/
noncomputable def prefixResidualCoeff (Rshift : Polynomial (Polynomial L)) (d n : ℕ)
    (c : ℕ → L) : L :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (d + 1),
    ((Rshift.coeff b).coeff a) * ((positivePrefix c n) ^ b).coeff (n - a)

/-- The finite residual is the actual evaluation coefficient, for any valid outer-degree cap. -/
theorem coeff_eval_eq_prefixResidualCoeff (Rshift : Polynomial (Polynomial L))
    (d n : ℕ) (c : ℕ → L) (hdeg : Rshift.natDegree ≤ d) :
    (Rshift.eval (positivePrefix c n)).coeff n = prefixResidualCoeff Rshift d n c := by
  classical
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) (positivePrefix c n)]
  simp_rw [finsetSum_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold prefixResidualCoeff
  rw [Finset.sum_comm]

/-- The universal step is the negative prefix residual cleared by the common slope power. -/
theorem numeratorStep_scaled (Rshift : Polynomial (Polynomial L)) (s : L) (hs : s ≠ 0)
    (d n : ℕ) (N c : ℕ → L) (hn : 1 ≤ n)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    numeratorStep Rshift s d n N = -(s ^ (2 * n - 2) * prefixResidualCoeff Rshift d n c) := by
  classical
  unfold numeratorStep prefixResidualCoeff
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact residualTerm_scaled Rshift s hs n a b N c hn (by simpa using ha) hrel

/-- Evaluation form of the cleared residual identity, exposing the actual polynomial consumer. -/
theorem numeratorStep_eq_neg_slope_pow_mul_eval_coeff
    (Rshift : Polynomial (Polynomial L)) (s : L) (hs : s ≠ 0) (d n : ℕ)
    (N c : ℕ → L) (hn : 1 ≤ n) (hdeg : Rshift.natDegree ≤ d)
    (hrel : ∀ i, 0 < i → i < n → N i = s ^ (2 * i - 1) * c i) :
    numeratorStep Rshift s d n N =
      -(s ^ (2 * n - 2) * (Rshift.eval (positivePrefix c n)).coeff n) := by
  rw [numeratorStep_scaled Rshift s hs d n N c hn hrel,
    coeff_eval_eq_prefixResidualCoeff Rshift d n c hdeg]

end Polynomial.UniversalHenselNumerator
