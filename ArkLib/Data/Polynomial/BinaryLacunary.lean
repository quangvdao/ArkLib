/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Binary lacunary polynomials

Rigidity results for polynomials over a finite field of characteristic two whose terms between
one quarter and one half of the field size vanish.
-/

open scoped Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

private lemma natDegree_sq_sub_coeff_mul_X_pow_le
    [CharP F 2] (H : F[X]) (T : ℕ) (hT : 2 ≤ T) (hTeven : Even T)
    (hdeg : (H ^ 2).natDegree ≤ T) :
    (H ^ 2 + C ((H ^ 2).coeff T) * X ^ T).natDegree ≤ T - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn_cases : n = T - 1 ∨ n = T ∨ T < n := by omega
  rcases hn_cases with rfl | rfl | hnT
  · have hodd : ((T - 1 : ℕ) : F) = 1 := by
      have hcastT : (T : F) = 0 := by
        rcases hTeven with ⟨k, rfl⟩
        simpa only [Nat.cast_add] using CharTwo.add_self_eq_zero (k : F)
      rw [Nat.cast_sub (by omega), hcastT]
      simp [CharTwo.neg_eq]
    have hderiv : derivative (H ^ 2) = 0 := by
      simp [derivative_sq, CharTwo.two_eq_zero]
    have hc : (H ^ 2).coeff (T - 1) = 0 := by
      have := congrArg (fun p : F[X] => p.coeff (T - 2)) hderiv
      simp only [coeff_derivative, coeff_zero] at this
      have hidx : T - 2 + 1 = T - 1 := by omega
      have hfac : ((T - 2 : ℕ) : F) + 1 = 1 := by
        rw [← Nat.cast_one, ← Nat.cast_add, hidx, hodd]
        norm_num
      rw [hfac, mul_one] at this
      simpa only [hidx] using this
    simp [hc, show T - 1 ≠ T by omega]
  · simp [CharTwo.add_self_eq_zero]
  · have hsquare : (H ^ 2).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hnT)
    simp [hsquare, ne_of_gt hnT]

/-- A polynomial with a gap between one quarter and one half of the field size is forced to be
one factor in a two-factor decomposition of the finite-field vanishing polynomial. -/
theorem binaryLacunary_rigidity
    [CharP F 2] [Fintype F] (P H : F[X]) (T J : ℕ)
    (hcard : Fintype.card F = 2 * T) (hT : 4 ≤ T)
    (hTeven : Even T) (hJ : 2 * J ≤ T) (hP : P = X ^ T + H)
    (hH : H.natDegree ≤ J) (S : Finset F) (hS : ∀ x ∈ S, P.eval x = 0)
    (hScard : T - 1 ≤ S.card) :
    ∃ c : F, c ≠ 0 ∧ X ^ Fintype.card F - X = P ^ 2 + C c * P := by
  classical
  let b := (H ^ 2).coeff T
  let R := X ^ Fintype.card F - X + P ^ 2 + C b * P
  have hHsq : (H ^ 2).natDegree ≤ T := by
    calc
      (H ^ 2).natDegree ≤ 2 * H.natDegree := natDegree_pow_le
      _ ≤ 2 * J := Nat.mul_le_mul_left 2 hH
      _ ≤ T := hJ
  have hJsmall : J ≤ T - 2 := by omega
  have hRform : R = (H ^ 2 + C b * X ^ T) + (C b * H - X) := by
    dsimp [R, b]
    rw [hcard, hP, CharTwo.sub_eq_add]
    have hpow : (X : F[X]) ^ (2 * T) = (X ^ T) ^ 2 := by
      rw [show 2 * T = T * 2 by omega, pow_mul]
    rw [hpow]
    ring_nf
    simp [CharTwo.two_eq_zero, CharTwo.neg_eq]
  have hRdeg : R.natDegree ≤ T - 2 := by
    rw [hRform]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_sq_sub_coeff_mul_X_pow_le H T (by omega) hTeven hHsq
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le b H).trans (hH.trans hJsmall)
      · rw [natDegree_X]
        omega
  have hReval : ∀ x ∈ S, R.eval x = 0 := by
    intro x hx
    simp [R, hS x hx, FiniteField.pow_card]
  have hRzero : R = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S hReval
    omega
  have hidentity : X ^ Fintype.card F - X = P ^ 2 + C b * P := by
    have := hRzero
    dsimp [R] at this
    rw [CharTwo.sub_eq_add] at this ⊢
    rw [add_assoc] at this
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left this
  refine ⟨b, ?_, hidentity⟩
  intro hb
  have hd := congrArg derivative hidentity
  rw [hb] at hd
  simp [derivative_X_pow, derivative_sq, CharTwo.two_eq_zero,
    Nat.cast_card_eq_zero F, CharTwo.neg_eq] at hd

/-- In characteristic two, two solutions of `Y² + cY = A` with the same constant term agree
when `c` is nonzero. -/
theorem eq_of_sq_add_C_mul_eq_sq_add_C_mul
    [CharP F 2] (A B : F[X]) (c : F) (hc : c ≠ 0)
    (hconst : A.coeff 0 = B.coeff 0)
    (h : A ^ 2 + C c * A = B ^ 2 + C c * B) :
    A = B := by
  have hfactor : (A - B) * (A - B + C c) = 0 := by
    rw [CharTwo.sub_eq_add]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add]
    have h' : A * C c + A ^ 2 = B * C c + B ^ 2 := by
      simpa only [add_comm, mul_comm] using h
    rw [h']
    calc
      B * C c + B ^ 2 + B * C c + B ^ 2 =
          (B * C c + B * C c) + (B ^ 2 + B ^ 2) := by ac_rfl
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
  rcases mul_eq_zero.mp hfactor with hAB | hABc
  · exact sub_eq_zero.mp hAB
  · have hcoeff := congrArg (fun p : F[X] => p.coeff 0) hABc
    simp only [coeff_add, coeff_sub, coeff_C_zero, coeff_zero] at hcoeff
    rw [hconst, sub_self, zero_add] at hcoeff
    exact (hc hcoeff).elim

/-- Away from the origin, the linear coefficient in the factorization is the constant term of
the lacunary polynomial. -/
theorem parameter_eq_constantCoeff_of_factorization
    [CharP F 2] (P : F[X]) (N : ℕ) (hN : 0 < N) (c z : F) (hz : z ≠ 0)
    (hconst : P.coeff 0 = z)
    (hidentity : X ^ N - X = P ^ 2 + C c * P) :
    c = z := by
  have heval := congrArg (eval (0 : F)) hidentity
  have heval' : 0 = z ^ 2 + c * z := by
    simpa [hN.ne', ← coeff_zero_eq_eval_zero, hconst] using heval
  have hprod : z * (z + c) = 0 := by
    calc
      z * (z + c) = z ^ 2 + c * z := by ring
      _ = 0 := heval'.symm
  have hzadd : z + c = 0 := (mul_eq_zero.mp hprod).resolve_left hz
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzadd

/-- At the origin, a unit coefficient of `X` forces the linear coefficient in the factorization
to be one. -/
theorem parameter_eq_one_of_factorization
    [CharP F 2] (P : F[X]) (N : ℕ) (hN : 2 ≤ N) (c : F) (hcoeff : P.coeff 1 = 1)
    (hidentity : X ^ N - X = P ^ 2 + C c * P) :
    c = 1 := by
  have hd := congrArg (fun Q : F[X] => (derivative Q).eval 0) hidentity
  have hNpred : N - 1 ≠ 0 := by omega
  have hd' : 1 = c * (derivative P).eval 0 := by
    simpa [derivative_X_pow, derivative_sq, CharTwo.two_eq_zero, hNpred,
      CharTwo.neg_eq] using hd
  rw [← coeff_zero_eq_eval_zero (derivative P), coeff_derivative, hcoeff] at hd'
  simpa using hd'.symm

/-- Each factor in a degree-balanced decomposition of the finite-field vanishing polynomial has
exactly half of the field elements as distinct roots. -/
theorem roots_card_eq_and_nodup_of_binary_factorization
    [Fintype F] (P : F[X]) (T : ℕ)
    (hcard : Fintype.card F = 2 * T) (hT : 0 < T)
    (hPdeg : P.natDegree = T) (c : F)
    (hidentity : X ^ Fintype.card F - X = P ^ 2 + C c * P) :
    P.roots.card = T ∧ P.roots.Nodup := by
  classical
  let Q := P + C c
  have hQdeg : Q.natDegree = T := by
    dsimp [Q]
    calc
      (P + C c).natDegree = P.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C, hPdeg]; exact hT)
      _ = T := hPdeg
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero, natDegree_zero] at hPdeg
    omega
  have hQne : Q ≠ 0 := by
    intro hQzero
    rw [hQzero, natDegree_zero] at hQdeg
    omega
  have hfactor : P ^ 2 + C c * P = P * Q := by
    dsimp [Q]
    ring
  have hroots : P.roots + Q.roots = Finset.univ.val := by
    calc
      P.roots + Q.roots = (P * Q).roots :=
        (roots_mul (mul_ne_zero hPne hQne)).symm
      _ = ((X : F[X]) ^ Fintype.card F - X).roots := by rw [← hfactor, ← hidentity]
      _ = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X F
  have hcardRoots := congrArg Multiset.card hroots
  simp only [Multiset.card_add, Finset.card_val, Finset.card_univ] at hcardRoots
  have hPbound : P.roots.card ≤ T := by simpa only [hPdeg] using card_roots' P
  have hQbound : Q.roots.card ≤ T := by simpa only [hQdeg] using card_roots' Q
  have hProots : P.roots.card = T := by omega
  have hnodup : (P.roots + Q.roots).Nodup := by
    rw [hroots]
    exact Finset.univ.nodup
  exact ⟨hProots, (Multiset.nodup_add.mp hnodup).1⟩

/-- Set-valued version of `roots_card_eq_and_nodup_of_binary_factorization`. -/
theorem rootSet_ncard_eq_of_binary_factorization
    [Fintype F] (P : F[X]) (T : ℕ)
    (hcard : Fintype.card F = 2 * T) (hT : 0 < T)
    (hPdeg : P.natDegree = T) (c : F)
    (hidentity : X ^ Fintype.card F - X = P ^ 2 + C c * P) :
    Set.ncard (P.rootSet F) = T := by
  classical
  obtain ⟨hroots, hnodup⟩ :=
    roots_card_eq_and_nodup_of_binary_factorization P T hcard hT hPdeg c hidentity
  rw [rootSet, aroots_def, Algebra.algebraMap_self, map_id, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup hnodup, hroots]

/-- Set-valued version of `binaryLacunary_rigidity`. -/
theorem binaryLacunary_rootSet_ncard_eq
    [CharP F 2] [Fintype F] (P H : F[X]) (T J : ℕ)
    (hcard : Fintype.card F = 2 * T) (hT : 4 ≤ T)
    (hTeven : Even T) (hJ : 2 * J ≤ T) (hP : P = X ^ T + H)
    (hH : H.natDegree ≤ J) (S : Finset F) (hS : ∀ x ∈ S, P.eval x = 0)
    (hScard : T - 1 ≤ S.card) :
    Set.ncard (P.rootSet F) = T := by
  obtain ⟨c, _, hidentity⟩ :=
    binaryLacunary_rigidity P H T J hcard hT hTeven hJ hP hH S hS hScard
  have hHlt : H.natDegree < ((X : F[X]) ^ T).natDegree := by
    rw [natDegree_X_pow]
    omega
  have hPdeg : P.natDegree = T := by
    rw [hP, natDegree_add_eq_left_of_natDegree_lt hHlt, natDegree_X_pow]
  exact rootSet_ncard_eq_of_binary_factorization P T hcard (by omega) hPdeg c hidentity

end Polynomial
