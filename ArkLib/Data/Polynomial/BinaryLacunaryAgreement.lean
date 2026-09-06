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

namespace Polynomial

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
  let R₁ := X ^ T + X * Q₁ + C z
  let R₂ := X ^ T + X * Q₂ + C z
  have hJplus : 1 + J ≤ T := by omega
  have hR₁deg : R₁.natDegree = T := by
    exact natDegree_X_pow_add_X_mul_add_C Q₁ T J (by omega) hJplus hQ₁ z
  have hR₂deg : R₂.natDegree = T := by
    exact natDegree_X_pow_add_X_mul_add_C Q₂ T J (by omega) hJplus hQ₂ z
  have hR₁decomp : R₁ = X ^ T + (X * Q₁ + C z) := by simp [R₁, add_assoc]
  have hR₂decomp : R₂ = X ^ T + (X * Q₂ + C z) := by simp [R₂, add_assoc]
  have hH₁deg : (X * Q₁ + C z).natDegree ≤ J := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · calc
        (X * Q₁).natDegree ≤ X.natDegree + Q₁.natDegree := natDegree_mul_le
        _ ≤ J := by simp only [natDegree_X]; omega
    · rw [natDegree_C]
      exact Nat.zero_le J
  have hH₂deg : (X * Q₂ + C z).natDegree ≤ J := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · calc
        (X * Q₂).natDegree ≤ X.natDegree + Q₂.natDegree := natDegree_mul_le
        _ ≤ J := by simp only [natDegree_X]; omega
    · rw [natDegree_C]
      exact Nat.zero_le J
  have hroot₁ := lacunary_roots_of_agreement Q₁ T f g z S₁ hS₁ hf hg
  have hroot₂ := lacunary_roots_of_agreement Q₂ T f g z S₂ hS₂ hf hg
  have hcardErase₁ : T - 1 ≤ (S₁.erase 0).card := by
    by_cases h0 : 0 ∈ S₁
    · rw [Finset.card_erase_of_mem h0]
      omega
    · rw [Finset.erase_eq_self.mpr h0]
      omega
  have hcardErase₂ : T - 1 ≤ (S₂.erase 0).card := by
    by_cases h0 : 0 ∈ S₂
    · rw [Finset.card_erase_of_mem h0]
      omega
    · rw [Finset.erase_eq_self.mpr h0]
      omega
  obtain ⟨c₁, _, hid₁⟩ := binaryLacunary_rigidity R₁ (X * Q₁ + C z) T J
    hcard hT hTeven hJ hR₁decomp hH₁deg (S₁.erase 0) hroot₁ hcardErase₁
  obtain ⟨c₂, _, hid₂⟩ := binaryLacunary_rigidity R₂ (X * Q₂ + C z) T J
    hcard hT hTeven hJ hR₂decomp hH₂deg (S₂.erase 0) hroot₂ hcardErase₂
  have hzeroT : 0 ≠ T := by omega
  have honeT : 1 ≠ T := by omega
  have hR₁const : R₁.coeff 0 = z := by
    dsimp [R₁]
    rw [coeff_add, coeff_add, coeff_X_pow, if_neg hzeroT, coeff_X_mul_zero,
      coeff_C_zero]
    simp
  have hR₂const : R₂.coeff 0 = z := by
    dsimp [R₂]
    rw [coeff_add, coeff_add, coeff_X_pow, if_neg hzeroT, coeff_X_mul_zero,
      coeff_C_zero]
    simp
  by_cases hz : z = 0
  · rw [hz] at hR₁const hR₂const hS₁ hS₂
    have hQ₁zero : Q₁.coeff 0 = 1 := by
      by_contra hQ₁zero
      have hzeroNotMem : 0 ∉ S₁ := by
        intro hzeroMem
        have hagree := hS₁ 0 hzeroMem
        have hcoeff : Q₁.coeff 0 = 1 := by
          calc
            Q₁.coeff 0 = Q₁.eval 0 := coeff_zero_eq_eval_zero Q₁
            _ = f 0 + 0 * g 0 := hagree
            _ = 1 := by rw [hf0]; simp
        exact hQ₁zero hcoeff
      have hrootZero : R₁.eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, hR₁const]
      have hrootInsert : ∀ x ∈ insert 0 S₁, R₁.eval x = 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact hrootZero
        · have hx0 : x ≠ 0 := by
            intro hx
            subst x
            exact hzeroNotMem hxS
          exact hroot₁ x (Finset.mem_erase.mpr ⟨hx0, hxS⟩)
      have hR₁zero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R₁ (insert 0 S₁)
        hrootInsert (by rw [hR₁deg, Finset.card_insert_of_notMem hzeroNotMem]; omega)
      rw [hR₁zero, natDegree_zero] at hR₁deg
      omega
    have hQ₂zero : Q₂.coeff 0 = 1 := by
      by_contra hQ₂zero
      have hzeroNotMem : 0 ∉ S₂ := by
        intro hzeroMem
        have hagree := hS₂ 0 hzeroMem
        have hcoeff : Q₂.coeff 0 = 1 := by
          calc
            Q₂.coeff 0 = Q₂.eval 0 := coeff_zero_eq_eval_zero Q₂
            _ = f 0 + 0 * g 0 := hagree
            _ = 1 := by rw [hf0]; simp
        exact hQ₂zero hcoeff
      have hrootZero : R₂.eval 0 = 0 := by
        rw [← coeff_zero_eq_eval_zero, hR₂const]
      have hrootInsert : ∀ x ∈ insert 0 S₂, R₂.eval x = 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact hrootZero
        · have hx0 : x ≠ 0 := by
            intro hx
            subst x
            exact hzeroNotMem hxS
          exact hroot₂ x (Finset.mem_erase.mpr ⟨hx0, hxS⟩)
      have hR₂zero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R₂ (insert 0 S₂)
        hrootInsert (by rw [hR₂deg, Finset.card_insert_of_notMem hzeroNotMem]; omega)
      rw [hR₂zero, natDegree_zero] at hR₂deg
      omega
    have hR₁coeff : R₁.coeff 1 = 1 := by
      dsimp [R₁]
      rw [coeff_add, coeff_add, coeff_X_pow, if_neg honeT, coeff_X_mul Q₁ 0,
        hQ₁zero]
      simp
    have hR₂coeff : R₂.coeff 1 = 1 := by
      dsimp [R₂]
      rw [coeff_add, coeff_add, coeff_X_pow, if_neg honeT, coeff_X_mul Q₂ 0,
        hQ₂zero]
      simp
    have hc₁one := parameter_eq_one_of_factorization R₁ (Fintype.card F)
      (by rw [hcard]; omega) c₁ hR₁coeff hid₁
    have hc₂one := parameter_eq_one_of_factorization R₂ (Fintype.card F)
      (by rw [hcard]; omega) c₂ hR₂coeff hid₂
    rw [hc₁one] at hid₁
    rw [hc₂one] at hid₂
    have hR : R₁ = R₂ := eq_of_sq_add_C_mul_eq_sq_add_C_mul R₁ R₂ 1 one_ne_zero
      (by rw [hR₁const, hR₂const]) (by rw [← hid₁, ← hid₂])
    dsimp [R₁, R₂] at hR
    have hXQ : X * Q₁ = X * Q₂ := by
      exact add_left_cancel (add_right_cancel hR)
    exact (mul_left_cancel₀ X_ne_zero hXQ)
  · have hc₁z := parameter_eq_constantCoeff_of_factorization R₁ (Fintype.card F)
      Fintype.card_pos c₁ z hz hR₁const hid₁
    have hc₂z := parameter_eq_constantCoeff_of_factorization R₂ (Fintype.card F)
      Fintype.card_pos c₂ z hz hR₂const hid₂
    rw [hc₁z] at hid₁
    rw [hc₂z] at hid₂
    have hR : R₁ = R₂ := eq_of_sq_add_C_mul_eq_sq_add_C_mul R₁ R₂ z hz
      (by rw [hR₁const, hR₂const]) (by rw [← hid₁, ← hid₂])
    dsimp [R₁, R₂] at hR
    have hXQ : X * Q₁ = X * Q₂ := by
      exact add_left_cancel (add_right_cancel hR)
    exact mul_left_cancel₀ X_ne_zero hXQ

end Polynomial
