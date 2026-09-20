/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.Finset.PairwiseIntersection

/-!
# Pairwise Johnson bound for Reed–Solomon agreement lists

Distinct degree-at-most-`D` polynomials agree on at most `D` evaluation points. Combining this
fact with the elementary pairwise-intersection count gives the exact integral bound

`⌊n(A - D) / (A² - nD)⌋`

for the complete degree-`< D + 1` agreement list whenever the denominator is positive. This is
the pairwise component of the Johnson argument. It does not use a weighted certificate, mutual
correlated agreement, or the independent jet-count component.

The proof is extracted from
`MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean` at immutable source commit
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

noncomputable section

/-- The natural-number quotient in the pairwise Johnson expression. The list theorem below
requires `n * D < A * A`, so its application always has a positive denominator. -/
def pairwiseJohnsonListBound (n D A : ℕ) : ℕ :=
  n * (A - D) / (A * A - n * D)

open Classical in
/-- Exact integral pairwise Johnson bound for complete Reed–Solomon agreement lists.

The statement is field-independent and includes the zero polynomial. Its hypotheses force the
positive Johnson denominator, so the natural-number quotient is the literal floor used in finite
tables. This is the pairwise component `⌊n(A - D)/(A² - nD)⌋`; it does not supply an independent
jet-count component. -/
theorem closePolynomialSet_finite_and_ncard_le_pairwiseJohnson
    -- The field is arbitrary; `D` is the maximum degree and `A` the agreement threshold.
    {F : Type*} [Field F] {n D A : ℕ}
    -- The embedding gives `n` distinct evaluation points over a possibly infinite field.
    (domain : Fin n ↪ F) (received : Fin n → F)
    -- These hypotheses make the agreement surplus and Johnson denominator positive.
    (hDA : D + 1 ≤ A) (hpositive : n * D < A * A) :
    -- Finiteness is explicit because `Set.ncard` alone is zero for an infinite set.
    (closePolynomialSet domain received (D + 1) A).Finite ∧
      -- The quotient is the exact integral pairwise-Johnson component.
      (closePolynomialSet domain received (D + 1) A).ncard ≤
        pairwiseJohnsonListBound n D A := by
  let candidates := closePolynomialSet domain received (D + 1) A
  have hfinite : candidates.Finite := closePolynomialSet_finite domain received hDA
  let T := hfinite.toFinset
  let S : F[X] → Finset (Fin n) := polynomialAgreementSet domain received
  have hclose : ∀ P ∈ T, A ≤ (S P).card := by
    intro P hP
    exact (hfinite.mem_toFinset.mp hP).2
  have hpair : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → ((S P) ∩ (S Q)).card ≤ D := by
    intro P hP Q hQ hne
    by_contra hcard
    have hDcard : D + 1 ≤ ((S P) ∩ (S Q)).card := by omega
    apply hne
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      ((S P) ∩ (S Q)) domain.injective.injOn
    · exact (hfinite.mem_toFinset.mp hP).1.trans_le (by exact_mod_cast hDcard)
    · exact (hfinite.mem_toFinset.mp hQ).1.trans_le (by exact_mod_cast hDcard)
    · intro i hi
      have hiP := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
      have hiQ := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
      exact hiP.trans hiQ.symm
  have hmul := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le
    T S A D (by omega) (by simpa using hpositive) hclose hpair
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  rw [pairwiseJohnsonListBound]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < A * A - n * D)).2
  simpa [T] using hmul

end

end ReedSolomon
