/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Powerset
/-!
# Finiteness and an incidence bound for Reed--Solomon agreement lists

Over an arbitrary field, the degree-`< k` polynomials agreeing with a received
word in at least `A ≥ k` positions form a finite set.  Double-counting their
`k`-element agreement samples gives the elementary bound
`list.card * A.choose k ≤ n.choose k`.

This is a supporting field-independent incidence estimate, not the all-rate list
size bound.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The complete Reed--Solomon agreement list over an arbitrary field.

`domain` embeds the `n` coordinate indices as distinct evaluation points, `received` is the word
being decoded, `k` is the message dimension, and `A` is an integer agreement threshold. Membership
means ordinary polynomial degree strictly below `k` together with agreement on at least `A`
coordinates. This is a `Set`, so a theorem that bounds `Set.ncard` must also prove `.Finite` when
the field is not assumed finite. -/
def closePolynomialSet {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    -- Fix the evaluation domain, received word, message dimension, and integral threshold.
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Set F[X] :=
  {P |
    -- Candidate messages use degree `< k`, equivalently degree at most `k - 1` when `k > 0`.
    P.degree < k ∧
      -- The candidate agrees with the received word at at least `A` of the `n` coordinates.
      A ≤ (polynomialAgreementSet domain received P).card}

private lemma polynomial_eq_of_agrees_on
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (T : Finset (Fin n))
    (hTCard : T.card = k) (P Q : F[X]) (hPDegree : P.degree < k)
    (hQDegree : Q.degree < k)
    (hPAgreement : T ⊆ polynomialAgreementSet domain received P)
    (hQAgreement : T ⊆ polynomialAgreementSet domain received Q) : P = Q := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq T domain.injective.injOn
  · simpa [hTCard] using hPDegree
  · simpa [hTCard] using hQDegree
  · intro i hi
    rw [(Finset.mem_filter.mp (hPAgreement hi)).2,
      (Finset.mem_filter.mp (hQAgreement hi)).2]

/-- The close polynomials can be collected in a finite list satisfying the sharp
sample-incidence inequality.  No finiteness assumption on the field is used. -/
theorem exists_closePolynomial_finset_with_incidence_bound
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card * A.choose k ≤ n.choose k := by
  classical
  let samples := (Finset.univ : Finset (Fin n)).powersetCard k
  let candidates : Finset F[X] :=
    samples.image fun T ↦ Lagrange.interpolate T domain received
  let list := candidates.filter fun P ↦ P ∈ closePolynomialSet domain received k A
  have hlist : ∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A := by
    intro P
    constructor
    · intro hP
      exact (Finset.mem_filter.mp hP).2
    · intro hP
      obtain ⟨T, hTSubset, hTCard⟩ := Finset.exists_subset_card_eq
        (hAk.trans hP.2)
      have hTMem : T ∈ samples := by
        exact Finset.mem_powersetCard.mpr
          ⟨hTSubset.trans (Finset.subset_univ _), hTCard⟩
      have hinterpDegree : (Lagrange.interpolate T domain received).degree < k := by
        simpa [hTCard] using Lagrange.degree_interpolate_lt
          (s := T) (v := domain) (r := received) domain.injective.injOn
      have hinterpAgreement :
          T ⊆ polynomialAgreementSet domain received
            (Lagrange.interpolate T domain received) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
          Lagrange.eval_interpolate_at_node received domain.injective.injOn hi⟩
      have hPEq : P = Lagrange.interpolate T domain received :=
        polynomial_eq_of_agrees_on domain received T hTCard P _ hP.1
          hinterpDegree hTSubset hinterpAgreement
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨T, hTMem, hPEq.symm⟩, hP⟩
  let incidence :=
    list.sigma fun P ↦ (polynomialAgreementSet domain received P).powersetCard k
  have hincidenceLower : list.card * A.choose k ≤ incidence.card := by
    simp only [incidence, Finset.card_sigma]
    calc
      list.card * A.choose k = ∑ _P ∈ list, A.choose k := by simp
      _ ≤ ∑ P ∈ list,
          (polynomialAgreementSet domain received P).card.choose k := by
        apply Finset.sum_le_sum
        intro P hP
        exact Nat.choose_le_choose k (hlist P |>.mp hP).2
      _ = ∑ P ∈ list,
          ((polynomialAgreementSet domain received P).powersetCard k).card := by
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.card_powersetCard]
  have hincidenceUpper : incidence.card ≤ samples.card := by
    apply Finset.card_le_card_of_injOn Sigma.snd
    · intro x hx
      simp only [incidence] at hx
      obtain ⟨_, hxsample⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hxsample).1.trans (Finset.subset_univ _),
          (Finset.mem_powersetCard.mp hxsample).2⟩
    · intro x hx y hy hxy
      simp only [incidence] at hx hy
      obtain ⟨hxlist, hxsample⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hylist, hysample⟩ := Finset.mem_sigma.mp hy
      have hxset := Finset.mem_powersetCard.mp hxsample
      have hyset := Finset.mem_powersetCard.mp hysample
      have hpoly : x.1 = y.1 := by
        apply polynomial_eq_of_agrees_on domain received x.2 hxset.2
        · exact (hlist x.1 |>.mp hxlist).1
        · exact (hlist y.1 |>.mp hylist).1
        · exact hxset.1
        · rw [hxy]
          exact hyset.1
      cases x with
      | mk xP xT =>
          cases y with
          | mk yP yT =>
              change xP = yP at hpoly
              change xT = yT at hxy
              subst yP
              subst yT
              rfl
  refine ⟨list, hlist, hincidenceLower.trans ?_⟩
  calc
    incidence.card ≤ samples.card := hincidenceUpper
    _ = n.choose k := by simp [samples]

/-- The incidence inequality stated directly for the cardinality of the complete agreement set. -/
theorem closePolynomialSet_ncard_mul_choose_le
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).ncard * A.choose k ≤ n.choose k := by
  obtain ⟨list, hlist, hbound⟩ :=
    exists_closePolynomial_finset_with_incidence_bound domain received hAk
  rw [show closePolynomialSet domain received k A = (list : Set F[X]) by
    ext P
    exact (hlist P).symm]
  simpa only [Set.ncard_coe_finset] using hbound

/-- The close degree-`< k` polynomial set is finite over an arbitrary field when
the agreement threshold is at least `k`. -/
theorem closePolynomialSet_finite
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (hAk : k ≤ A) :
    (closePolynomialSet domain received k A).Finite := by
  obtain ⟨list, hlist, _⟩ :=
    exists_closePolynomial_finset_with_incidence_bound domain received hAk
  rw [show closePolynomialSet domain received k A = (list : Set F[X]) by
    ext P
    exact (hlist P).symm]
  exact list.finite_toSet

end

end ReedSolomon
