/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BinaryTraceWitness
import ArkLib.Data.CodingTheory.ReedSolomon.ReciprocalWord

/-!
# An affine line with binary trace agreement witnesses

This file packages the normalized trace quotients as explicit low-degree agreement witnesses for
an affine line of words over a finite binary field.
-/

open scoped BigOperators

namespace ReedSolomon

namespace Binary

open Polynomial

section Definitions

/-- The power word, repaired to have value one at the origin. -/
def rationalPowerWord {F : Type*} [Field F] [DecidableEq F] (m : ℕ) (x : F) : F :=
  if x = 0 then 1 else x ^ (binaryTraceTopDegree m - 1)

/-- The explicit explaining polynomial. The origin challenge uses parameter one;
every other challenge uses its inverse. No existence theorem or choice is involved. -/
noncomputable def rationalLinePolynomial {F : Type*} [Field F] [DecidableEq F]
    (m : ℕ) (z : F) : F[X] :=
  binaryTraceQuotient m (if z = 0 then 1 else z⁻¹)

end Definitions

section FiniteBinaryField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
private lemma rationalLineWord_zero (m : ℕ) (τ z : F) :
    rationalPowerWord m 0 + z * reciprocalWord τ 0 = 1 + z * τ := by
  simp [rationalPowerWord, reciprocalWord]

omit [Fintype F] [CharP F 2] in
private lemma rationalLineWord_ne_zero (m : ℕ) (τ z : F) {x : F} (hx : x ≠ 0) :
    rationalPowerWord m x + z * reciprocalWord τ x =
      x ^ (binaryTraceTopDegree m - 1) + z * x⁻¹ := by
  simp [rationalPowerWord, reciprocalWord, hx]

omit [Fintype F] [CharP F 2] in
/-- The explicit explanation lies below the quarter-field degree threshold. -/
theorem rationalLinePolynomial_degree_lt {m : ℕ} (hm : 3 ≤ m) (z : F) :
    (rationalLinePolynomial m z).degree < binaryTraceQuarterDegree m :=
  degree_le_natDegree.trans_lt (by
    exact_mod_cast binaryTraceQuotient_natDegree_lt hm (if z = 0 then 1 else z⁻¹))

/-- The explicit explanation agrees with the received mixture on exactly half the field. -/
theorem rationalLinePolynomial_agree_eq {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1) (z : F) :
    Code.agree (fun x : F ↦ rationalPowerWord m x + z * reciprocalWord τ x)
      (fun x ↦ (rationalLinePolynomial m z).eval x) = binaryTraceTopDegree m := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [rationalLinePolynomial]
    let nonzeroAgreements := Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x = x ^ (binaryTraceTopDegree m - 1)
    have hnonzero : nonzeroAgreements.card = Fintype.card F / 2 - 1 := by
      simpa [nonzeroAgreements] using
        binaryTraceQuotient_one_nonzero_agreement_card (F := F) hm hcard
    have hsets :
        Finset.univ.filter (fun x : F ↦
          rationalPowerWord m x + 0 * reciprocalWord τ x =
            (binaryTraceQuotient m 1).eval x) =
          insert 0 nonzeroAgreements := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hx : x = 0
      · subst x
        rw [binaryTraceQuotient_eval_zero (by omega)]
        simp [rationalPowerWord, reciprocalWord]
      · simp only [hx, false_or, nonzeroAgreements]
        rw [rationalLineWord_ne_zero m τ 0 hx]
        simp [hx, eq_comm]
    change (Finset.univ.filter fun x : F ↦
      rationalPowerWord m x + 0 * reciprocalWord τ x =
        (binaryTraceQuotient m 1).eval x).card = binaryTraceTopDegree m
    rw [hsets, Finset.card_insert_of_notMem]
    · rw [hnonzero, binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard]
      have hhalf_pos : 0 < Fintype.card F / 2 := by
        rw [← binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard]
        simp only [binaryTraceTopDegree]
        exact pow_pos Nat.zero_lt_two _
      omega
    · simp [nonzeroAgreements]
  · let s : F := z⁻¹
    have hs : s ≠ 0 := inv_ne_zero hz
    simp only [rationalLinePolynomial, if_neg hz]
    have horigin :
        ¬rationalPowerWord m 0 + z * reciprocalWord τ 0 =
          (binaryTraceQuotient m s).eval 0 := by
      rw [binaryTraceQuotient_eval_zero (by omega) s, rationalLineWord_zero]
      intro heq
      have hscaled := congrArg (fun w : F ↦ z * w) heq.symm
      have hzs : z * s = 1 := by simp [s, hz]
      rw [hzs, mul_add, mul_one] at hscaled
      apply trace_one_ne_quadratic_zero hcard hτ
      calc
        τ * z ^ 2 + z + 1 = z * (z * τ) + z + 1 := by
          simp only [pow_two]
          ac_rfl
        _ = (z + z * (z * τ)) + 1 := by ac_rfl
        _ = 1 + 1 := by rw [← hscaled]
        _ = 0 := CharTwo.add_self_eq_zero 1
    have hsets :
        Finset.univ.filter (fun x : F ↦
          rationalPowerWord m x + z * reciprocalWord τ x =
            (binaryTraceQuotient m s).eval x) =
        Finset.univ.filter (fun x : F ↦
          (binaryTraceQuotient m s).eval x =
            x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hx : x = 0
      · subst x
        apply iff_of_false horigin
        rw [binaryTraceQuotient_eval_zero (by omega) s]
        have hpow : binaryTraceTopDegree m - 1 ≠ 0 := by
          simp only [binaryTraceTopDegree]
          have hle : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          norm_num at hle
          omega
        simp [zero_pow hpow, hs]
      · rw [rationalLineWord_ne_zero m τ z hx]
        simp [s, eq_comm]
    change (Finset.univ.filter fun x : F ↦
      rationalPowerWord m x + z * reciprocalWord τ x =
        (binaryTraceQuotient m s).eval x).card = binaryTraceTopDegree m
    rw [hsets, binaryTraceQuotient_agreement_card hm hcard hs]
    exact (binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard).symm

end FiniteBinaryField

end Binary

end ReedSolomon
