/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import Mathlib.LinearAlgebra.Lagrange

/-!
# Common polynomial explanations by interpolation

Any pair of words admits a common explanation on any prescribed number of distinct
coordinates up to the message dimension.
-/

namespace ReedSolomon

open Polynomial

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


end ReedSolomon
