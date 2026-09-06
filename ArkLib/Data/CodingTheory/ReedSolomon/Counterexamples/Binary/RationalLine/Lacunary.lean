/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BinaryLacunary

/-!
# Agreement rigidity for binary lacunary polynomials

An agreement set of half the field determines a low-degree polynomial uniquely for words whose
off-zero values become lacunary after multiplication by the input.
-/

open scoped Polynomial

namespace ReedSolomon.Binary

open Polynomial

variable {F : Type*} [Field F]

private lemma natDegree_X_pow_add_X_mul_add_C
    (Q : F[X]) (T J : ℕ) (hT : 0 < T) (hJT : 1 + J ≤ T) (hQ : Q.natDegree < J)
    (z : F) :
    (X ^ T + X * Q + C z).natDegree = T := by
  have hXQ : (X * Q).natDegree < T := by
    calc
      (X * Q).natDegree ≤ X.natDegree + Q.natDegree := natDegree_mul_le
      _ < 1 + J := by simpa using Nat.add_lt_add_left hQ 1
      _ ≤ T := hJT
  have hlow : (X * Q + C z).natDegree < T := by
    apply (natDegree_add_le _ _).trans_lt
    rw [max_lt_iff]
    exact ⟨hXQ, (natDegree_C z).trans_lt hT⟩
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow T
  · simpa only [natDegree_X_pow] using hlow

private lemma lacunary_roots_of_agreement
    [CharP F 2] [DecidableEq F] (Q : F[X]) (T : ℕ) (f g : F → F) (z : F)
    (S : Finset F)
    (hSf : ∀ x ∈ S, Q.eval x = f x + z * g x)
    (hf : ∀ x, x ≠ 0 → x * f x = x ^ T)
    (hg : ∀ x, x ≠ 0 → x * g x = 1) :
    ∀ x ∈ S.erase 0, (X ^ T + X * Q + C z).eval x = 0 := by
  intro x hx
  have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
  have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  rw [hSf x hxS]
  calc
    x ^ T + x * (f x + z * g x) + z =
        (x ^ T + x * f x) + z * (x * g x + 1) := by ring
    _ = 0 := by rw [hf x hx0, hg x hx0, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, mul_zero, zero_add]

private lemma binaryLacunary_factorization_of_agreement
    [CharP F 2] [Fintype F] [DecidableEq F]
    (T J : ℕ) (hcard : Fintype.card F = 2 * T) (hT : 4 ≤ T) (hTeven : Even T)
    (hJ : 2 * J ≤ T) (f g : F → F) (hf0 : f 0 = 1)
    (hf : ∀ x, x ≠ 0 → x * f x = x ^ T) (hg : ∀ x, x ≠ 0 → x * g x = 1)
    (z : F) (Q : F[X]) (hQ : Q.natDegree < J) (S : Finset F) (hScard : T ≤ S.card)
    (hS : ∀ x ∈ S, Q.eval x = f x + z * g x) :
    let R := X ^ T + X * Q + C z
    R.natDegree = T ∧ R.coeff 0 = z ∧
      X ^ Fintype.card F - X = R ^ 2 + C (if z = 0 then 1 else z) * R := by
  classical
  let R := X ^ T + X * Q + C z
  have hJplus : 1 + J ≤ T := by omega
  have hRdeg : R.natDegree = T := by
    exact natDegree_X_pow_add_X_mul_add_C Q T J (by omega) hJplus hQ z
  have hRdecomp : R = X ^ T + (X * Q + C z) := by simp [R, add_assoc]
  have hHdeg : (X * Q + C z).natDegree ≤ J := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · calc
        (X * Q).natDegree ≤ X.natDegree + Q.natDegree := natDegree_mul_le
        _ ≤ J := by simp only [natDegree_X]; omega
    · rw [natDegree_C]
      exact Nat.zero_le J
  have hroot := lacunary_roots_of_agreement Q T f g z S hS hf hg
  have hcardErase : T - 1 ≤ (S.erase 0).card := by
    by_cases h0 : 0 ∈ S
    · rw [Finset.card_erase_of_mem h0]
      omega
    · rw [Finset.erase_eq_self.mpr h0]
      omega
  obtain ⟨c, _, hid⟩ := binaryLacunary_rigidity R (X * Q + C z) T J
    hcard hT hTeven hJ hRdecomp hHdeg (S.erase 0) hroot hcardErase
  have hzeroT : 0 ≠ T := by omega
  have hRconst : R.coeff 0 = z := by
    dsimp [R]
    rw [coeff_add, coeff_add, coeff_X_pow, if_neg hzeroT, coeff_X_mul_zero,
      coeff_C_zero]
    simp
  refine ⟨hRdeg, hRconst, ?_⟩
  change X ^ Fintype.card F - X = R ^ 2 + C (if z = 0 then 1 else z) * R
  by_cases hz : z = 0
  · rw [hz] at hRconst hS ⊢
    have hQzero : Q.coeff 0 = 1 := by
      by_contra hQzero
      have hzeroNotMem : 0 ∉ S := by
        intro hzeroMem
        have hagree := hS 0 hzeroMem
        have hcoeff : Q.coeff 0 = 1 := by
          calc
            Q.coeff 0 = Q.eval 0 := coeff_zero_eq_eval_zero Q
            _ = f 0 + 0 * g 0 := hagree
            _ = 1 := by rw [hf0]; simp
        exact hQzero hcoeff
      have hrootZero : R.eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, hRconst]
      have hrootInsert : ∀ x ∈ insert 0 S, R.eval x = 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact hrootZero
        · have hx0 : x ≠ 0 := by
            intro hx
            subst x
            exact hzeroNotMem hxS
          exact hroot x (Finset.mem_erase.mpr ⟨hx0, hxS⟩)
      have hRzero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R (insert 0 S)
        hrootInsert (by rw [hRdeg, Finset.card_insert_of_notMem hzeroNotMem]; omega)
      rw [hRzero, natDegree_zero] at hRdeg
      omega
    have honeT : 1 ≠ T := by omega
    have hRcoeff : R.coeff 1 = 1 := by
      dsimp [R]
      rw [coeff_add, coeff_add, coeff_X_pow, if_neg honeT, coeff_X_mul Q 0, hQzero]
      simp
    have hcone := parameter_eq_one_of_factorization R (Fintype.card F)
      (by rw [hcard]; omega) c hRcoeff hid
    rw [hcone] at hid
    simpa only [if_true] using hid
  · have hcz := parameter_eq_constantCoeff_of_factorization R (Fintype.card F)
      Fintype.card_pos c z hz hRconst hid
    rw [hcz] at hid
    simpa only [if_neg hz] using hid

/-- For a fixed `z`, agreement on half of a binary field uniquely determines the low-degree
polynomial. The hypotheses on `f` and `g` abstract the concrete word with off-zero values
`x ^ (T - 1)` and `x⁻¹`, while `f 0 = 1` supplies the distinguished origin value. -/
theorem eq_of_binaryLacunary_agreement
    [CharP F 2] [Fintype F]
    (T J : ℕ) (hcard : Fintype.card F = 2 * T) (hT : 4 ≤ T) (hTeven : Even T)
    (hJ : 2 * J ≤ T) (f g : F → F) (hf0 : f 0 = 1)
    (hf : ∀ x, x ≠ 0 → x * f x = x ^ T) (hg : ∀ x, x ≠ 0 → x * g x = 1)
    (z : F) (Q₁ Q₂ : F[X]) (hQ₁ : Q₁.natDegree < J) (hQ₂ : Q₂.natDegree < J)
    (S₁ S₂ : Finset F) (hS₁card : T ≤ S₁.card) (hS₂card : T ≤ S₂.card)
    (hS₁ : ∀ x ∈ S₁, Q₁.eval x = f x + z * g x)
    (hS₂ : ∀ x ∈ S₂, Q₂.eval x = f x + z * g x) :
    Q₁ = Q₂ := by
  classical
  obtain ⟨_, hR₁const, hid₁⟩ := binaryLacunary_factorization_of_agreement
    T J hcard hT hTeven hJ f g hf0 hf hg z Q₁ hQ₁ S₁ hS₁card hS₁
  obtain ⟨_, hR₂const, hid₂⟩ := binaryLacunary_factorization_of_agreement
    T J hcard hT hTeven hJ f g hf0 hf hg z Q₂ hQ₂ S₂ hS₂card hS₂
  have hc : (if z = 0 then 1 else z) ≠ 0 := by
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz]
  have hR := eq_of_sq_add_C_mul_eq_sq_add_C_mul
    (X ^ T + X * Q₁ + C z) (X ^ T + X * Q₂ + C z) (if z = 0 then 1 else z) hc
    (by rw [hR₁const, hR₂const]) (by rw [← hid₁, ← hid₂])
  have hXQ : X * Q₁ = X * Q₂ := by
    exact add_left_cancel (add_right_cancel hR)
  exact mul_left_cancel₀ X_ne_zero hXQ

end ReedSolomon.Binary
