/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.BinaryTrace

/-!
# Low-degree quotients of normalized binary trace polynomials

The construction here is written explicitly as a polynomial.  This makes its constant term,
degree, and evaluation identities available without appealing to polynomial division.
-/

open scoped BigOperators

namespace Polynomial

section Definitions

/-- The leading exponent in an `m`-term binary trace. -/
abbrev binaryTraceTopDegree (m : ℕ) : ℕ := 2 ^ (m - 1)

/-- The quarter-field degree threshold used by the quotient polynomial. -/
abbrev binaryTraceQuarterDegree (m : ℕ) : ℕ := 2 ^ (m - 2)

/-- The explicit quotient obtained after the leading trace monomial cancels and `X` is removed. -/
noncomputable def binaryTraceQuotient {F : Type*} [Field F] (m : ℕ) (s : F) : F[X] :=
  ∑ i ∈ Finset.range (m - 1),
    C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)

private noncomputable def binaryNormalizedTracePoly {F : Type*} [Field F]
    (m : ℕ) (s : F) : F[X] :=
  X ^ binaryTraceTopDegree m + X * binaryTraceQuotient m s

end Definitions

section Field

variable {F : Type*} [Field F]

lemma binaryTraceQuotient_natDegree_lt {m : ℕ} (hm : 3 ≤ m) (s : F) :
    (binaryTraceQuotient m s).natDegree < binaryTraceQuarterDegree m := by
  classical
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le (Finset.range (m - 1)) _ ?_)
  · simp only [binaryTraceQuarterDegree]
    apply Nat.sub_lt_self Nat.one_pos
    have hp : 0 < 2 ^ (m - 2) := pow_pos Nat.zero_lt_two _
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    calc
      (C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)).natDegree
          ≤ (C (s ^ (2 ^ (i + 1) - 1))).natDegree +
            (X ^ (2 ^ i - 1) : F[X]).natDegree := natDegree_mul_le
      _ ≤ 2 ^ i - 1 := by simp
      _ ≤ 2 ^ (m - 2) - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by omega)) 1

lemma binaryTraceQuotient_eval_zero {m : ℕ} (hm : 2 ≤ m) (s : F) :
    (binaryTraceQuotient m s).eval 0 = s := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, m - 1 = n + 1 := by
    exact ⟨m - 2, by omega⟩
  rw [binaryTraceQuotient, hn, eval_finsetSum, Finset.sum_range_succ']
  simp only [eval_mul, eval_C, eval_X_pow]
  have hzero : ∀ i ∈ Finset.range n,
      s ^ (2 ^ (i + 1 + 1) - 1) * 0 ^ (2 ^ (i + 1) - 1) = 0 := by
    intro i hi
    rw [zero_pow (Nat.sub_ne_zero_of_lt (by
      exact one_lt_pow₀ (by omega) (by omega))), mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add]
  norm_num

end Field

section FiniteBinaryField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Field F] [DecidableEq F] [CharP F 2] in
lemma binaryTraceTopDegree_eq_card_div_two {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    binaryTraceTopDegree m = Fintype.card F / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [hcard, binaryTraceTopDegree]
  simp [pow_succ]

omit [Field F] [DecidableEq F] [CharP F 2] in
lemma binaryTraceQuarterDegree_eq_card_div_four {m : ℕ} (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    binaryTraceQuarterDegree m = Fintype.card F / 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [hcard, binaryTraceQuarterDegree]
  simp [pow_succ]
  omega

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma inv_mul_trace_term (s x : F) (hs : s ≠ 0) (i : ℕ) :
    s⁻¹ * (s ^ 2 * x) ^ (2 ^ i) =
      s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i) := by
  rw [mul_pow]
  have hexp : 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; omega
  rw [show (s ^ 2) ^ (2 ^ i) = s ^ (2 ^ (i + 1)) by rw [← pow_mul, hexp]]
  have hpos : 0 < 2 ^ (i + 1) := by positivity
  have hcoeff : s⁻¹ * s ^ (2 ^ (i + 1)) = s ^ (2 ^ (i + 1) - 1) := by
    calc
      s⁻¹ * s ^ (2 ^ (i + 1)) =
          s⁻¹ * (s ^ (2 ^ (i + 1) - 1) * s) := by
            congr 2
            rw [← pow_succ]
            congr 1
            omega
      _ =
          (s⁻¹ * s) * s ^ (2 ^ (i + 1) - 1) := by ac_rfl
      _ = s ^ (2 ^ (i + 1) - 1) := by rw [inv_mul_cancel₀ hs, one_mul]
  rw [show s⁻¹ * (s ^ (2 ^ (i + 1)) * x ^ (2 ^ i)) =
      (s⁻¹ * s ^ (2 ^ (i + 1))) * x ^ (2 ^ i) by ac_rfl, hcoeff]

omit [DecidableEq F] [CharP F 2] in
private lemma binaryNormalizedTracePoly_eval {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s : F} (hs : s ≠ 0) (x : F) :
    (binaryNormalizedTracePoly m s).eval x = s⁻¹ * binaryTrace m (s ^ 2 * x) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X,
    binaryTrace, hn, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  simp only [binaryTraceTopDegree, Nat.add_sub_cancel]
  have htop : s ^ (2 ^ (n + 1) - 1) = 1 := by
    rw [← hn, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one s hs
  have htopterm : s⁻¹ * (s ^ 2 * x) ^ (2 ^ n) = x ^ (2 ^ n) := by
    rw [inv_mul_trace_term s x hs n, htop, one_mul]
  have hlower : x * (binaryTraceQuotient (n + 1) s).eval x =
      ∑ i ∈ Finset.range n, s⁻¹ * (s ^ 2 * x) ^ (2 ^ i) := by
    rw [binaryTraceQuotient, Nat.add_sub_cancel, eval_finsetSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eval_mul, eval_C, eval_X_pow]
    have hexp : 2 ^ i - 1 + 1 = 2 ^ i := by
      exact Nat.sub_add_cancel (by
        have hp : 0 < 2 ^ i := pow_pos Nat.zero_lt_two _
        omega)
    rw [show x * (s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i - 1)) =
        s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i) by
      rw [mul_left_comm, ← pow_succ', hexp]]
    exact (inv_mul_trace_term s x hs i).symm
  rw [hlower, htopterm]
  ac_rfl

omit [DecidableEq F] in
private lemma mul_binaryTraceQuotient_eval {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s : F} (hs : s ≠ 0) (x : F) :
    x * (binaryTraceQuotient m s).eval x =
      x ^ binaryTraceTopDegree m + s⁻¹ * binaryTrace m (s ^ 2 * x) := by
  have hnorm := binaryNormalizedTracePoly_eval hm hcard hs x
  rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X] at hnorm
  calc
    x * (binaryTraceQuotient m s).eval x =
        (x ^ binaryTraceTopDegree m + x ^ binaryTraceTopDegree m) +
          x * (binaryTraceQuotient m s).eval x := by
            rw [CharTwo.add_self_eq_zero, zero_add]
    _ = x ^ binaryTraceTopDegree m +
        (x ^ binaryTraceTopDegree m + x * (binaryTraceQuotient m s).eval x) := by
          rw [add_assoc]
    _ = x ^ binaryTraceTopDegree m + s⁻¹ * binaryTrace m (s ^ 2 * x) := by rw [hnorm]

omit [DecidableEq F] in
/-- For a nonzero evaluation point, the quotient agrees with the power-plus-reciprocal word
exactly on a trace-one fiber after the reciprocal coefficient is normalized as `s⁻¹`. -/
lemma binaryTraceQuotient_agreement_iff {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s x : F} (hs : s ≠ 0) (hx : x ≠ 0) :
    (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹ ↔
      binaryTrace m (s ^ 2 * x) = 1 := by
  have hmul := mul_binaryTraceQuotient_eval hm hcard hs x
  have htop : binaryTraceTopDegree m ≠ 0 := pow_ne_zero _ (by omega)
  have hxrecip : x * (s⁻¹ * x⁻¹) = s⁻¹ := by field_simp
  constructor
  · intro hagree
    rw [hagree, mul_add, mul_pow_sub_one htop, hxrecip] at hmul
    apply (mul_left_cancel₀ (inv_ne_zero hs))
    simpa only [mul_one] using (add_left_cancel hmul).symm
  · intro htrace
    apply (mul_left_cancel₀ hx)
    rw [mul_add, mul_pow_sub_one htop, hxrecip, hmul, htrace, mul_one]

lemma binaryTraceQuotient_agreement_card {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s : F} (hs : s ≠ 0) :
    (Finset.univ.filter fun x : F ↦
      (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹).card =
      Fintype.card F / 2 := by
  classical
  have hzero_not_agree :
      ¬(binaryTraceQuotient m s).eval 0 =
        (0 : F) ^ (binaryTraceTopDegree m - 1) + s⁻¹ * (0 : F)⁻¹ := by
    rw [binaryTraceQuotient_eval_zero (by omega) s]
    simp only [inv_zero, mul_zero, add_zero]
    rw [zero_pow (by
      simp [binaryTraceTopDegree]
      have : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at this
      omega)]
    exact hs
  have himage : Function.Bijective (fun x : F ↦ s ^ 2 * x) := by
    exact (Equiv.mulLeft₀ (s ^ 2) (pow_ne_zero 2 hs)).bijective
  let traceSet := Finset.univ.filter fun y : F ↦ binaryTrace m y = 1
  have hcard_trace : traceSet.card = Fintype.card F / 2 := by
    simpa [traceSet, binaryTraceFiber] using binaryTraceFiber_one_card (F := F) (by omega) hcard
  calc
    (Finset.univ.filter fun x : F ↦
      (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹).card
        = (Finset.univ.filter fun x : F ↦ binaryTrace m (s ^ 2 * x) = 1).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hx : x = 0
          · subst x
            exact iff_of_false hzero_not_agree (by simp)
          · exact binaryTraceQuotient_agreement_iff hm hcard hs hx
    _ = traceSet.card := by
      apply Finset.card_bij (fun x _ ↦ s ^ 2 * x)
      · intro x hx
        simpa [traceSet] using hx
      · intro x₁ _ x₂ _ h
        exact himage.1 h
      · intro y hy
        obtain ⟨x, rfl⟩ := himage.2 y
        refine ⟨x, ?_, rfl⟩
        simpa [traceSet] using hy
    _ = Fintype.card F / 2 := hcard_trace

/-- At `s = 1`, the quotient agrees with the pure power at the nonzero trace-zero points. -/
lemma binaryTraceQuotient_one_nonzero_agreement_card {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    (Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x =
        x ^ (binaryTraceTopDegree m - 1)).card =
      Fintype.card F / 2 - 1 := by
  classical
  let traceSet := Finset.univ.filter fun x : F ↦ binaryTrace m x = 0
  have hcard_trace : traceSet.card = Fintype.card F / 2 := by
    simpa [traceSet, binaryTraceFiber] using binaryTraceFiber_zero_card (F := F) (by omega) hcard
  have hzero_trace : (0 : F) ∈ traceSet := by simp [traceSet]
  calc
    (Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x =
        x ^ (binaryTraceTopDegree m - 1)).card
        = (traceSet.erase 0).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            traceSet]
          constructor
          · rintro ⟨hx, hagree⟩
            refine ⟨hx, ?_⟩
            have hmul := mul_binaryTraceQuotient_eval hm hcard one_ne_zero x
            rw [hagree, mul_pow_sub_one (pow_ne_zero _ (by omega)), one_pow, one_mul,
              inv_one] at hmul
            have hmul' : x ^ (2 ^ (m - 1)) =
                x ^ (2 ^ (m - 1)) + binaryTrace m x := by
              simpa only [one_mul] using hmul
            calc
              binaryTrace m x = 0 + binaryTrace m x := (zero_add _).symm
              _ = (x ^ (2 ^ (m - 1)) + x ^ (2 ^ (m - 1))) + binaryTrace m x := by
                rw [CharTwo.add_self_eq_zero]
              _ = x ^ (2 ^ (m - 1)) +
                  (x ^ (2 ^ (m - 1)) + binaryTrace m x) := by rw [add_assoc]
              _ = x ^ (2 ^ (m - 1)) + x ^ (2 ^ (m - 1)) := by rw [← hmul']
              _ = 0 := CharTwo.add_self_eq_zero _
          · rintro ⟨hx, htrace⟩
            refine ⟨hx, ?_⟩
            apply (mul_left_cancel₀ hx)
            rw [mul_pow_sub_one (pow_ne_zero _ (by omega)),
              mul_binaryTraceQuotient_eval hm hcard one_ne_zero x, one_pow, one_mul, inv_one,
              htrace, mul_zero, add_zero]
    _ = traceSet.card - 1 := Finset.card_erase_of_mem hzero_trace
    _ = Fintype.card F / 2 - 1 := by rw [hcard_trace]

end FiniteBinaryField

end Polynomial
