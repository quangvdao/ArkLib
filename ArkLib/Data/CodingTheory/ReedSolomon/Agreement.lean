/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Finset.Filter

/-!
# Polynomial agreement sets

The full coordinate sets on which one polynomial, or a pair of polynomials,
agrees with received words. No decoding-radius or correlated-agreement theorem is required.
-/

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The full set of positions where `P` agrees with a received word. -/
def polynomialAgreementSet {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) : Finset (ι) :=
  Finset.univ.filter fun i ↦ P.eval (domain i) = received i

/-- The positions where two message polynomials simultaneously agree with two received words. -/
def commonPolynomialAgreementSet {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) : Finset (ι) :=
  Finset.univ.filter fun i ↦ F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i

/-- Any two words have degree-bounded explanations on a common set of `k` coordinates. -/
theorem exists_commonPolynomialAgreementSet_card_ge
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ∃ P Q : F[X], P.degree < k ∧ Q.degree < k ∧
      k ≤ (commonPolynomialAgreementSet domain f g P Q).card := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (by simpa using hk)
  let P := Lagrange.interpolate S domain f
  let Q := Lagrange.interpolate S domain g
  have hinj : Set.InjOn domain S := domain.injective.injOn
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · simpa [P, hS] using Lagrange.degree_interpolate_lt f hinj
  · simpa [Q, hS] using Lagrange.degree_interpolate_lt g hinj
  · rw [← hS]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Lagrange.eval_interpolate_at_node f hinj hi,
      Lagrange.eval_interpolate_at_node g hinj hi⟩

end
end ReedSolomon
