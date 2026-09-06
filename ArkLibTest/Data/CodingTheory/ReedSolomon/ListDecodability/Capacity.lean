/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity

/-!
# Capacity-property consumer tests

The central import exposes the bound projections and a way to retain just one estimate.
Consumers need not unfold the geometric proof or reconstruct the exact polynomial list.
-/

open ReedSolomon

example (δ : ℝ) (hδ : 0 < δ) (hδ_one : δ < 1) :
    HasCapacityLists δ (capacityLengthThreshold δ)
      (fun n _ _ _ ℓ ↦ (ℓ : ℝ) ≤ capacityListBound δ n) := by
  exact (exists_capacity_list δ hδ hδ_one).mono
    (fun _ _ _ _ _ hb ↦ hb.fieldIndependent)

example {δ : ℝ} {n k q A ℓ : ℕ} (hb : CapacityListBounds δ n k q A ℓ)
    (hδ : (1 / 2 : ℝ) ≤ δ) : ℓ ≤ 1 :=
  hb.halfGap hδ

example {δ : ℝ} (hδ : δ < (1 / 4 : ℝ)) :
    capacityDerivativeOrder δ = Nat.ceil (Real.exp (((27 : ℝ) / 10) / δ)) :=
  capacityDerivativeOrder_eq_ceil hδ

example : WeightedSupportConstruction :=
  exists_weightedSupport_hiddenDerivativeConstruction

/-- At the tight ambient value K=2, the separant budget uses natural subtraction. -/
example : (1 * 1 + 1 - 2 : ℕ) = 0 := by norm_num

/-- The boundary alphabet `q=n` retains exactness, the empty case, and all three estimates
on one and the same list. -/
example (δ : ℝ) (hδ : 0 < δ) (hsmall : δ < (1 / 4 : ℝ))
    (n k A : ℕ) (hn : capacityLengthThreshold δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hp : n.Prime) (hgap : (k : ℝ) + δ * n ≤ A) (hA : A ≤ 2 * n)
    (α : Fin n ↪ ZMod n) (y : Fin n → ZMod n) :
    ∃ list : Finset (Polynomial (ZMod n)),
      (∀ P, P ∈ list ↔ P.degree < k ∧ A ≤ Code.agree (fun i ↦ P.eval (α i)) y) ∧
      (n < A → list = ∅) ∧
      (list.card : ℝ) ≤ capacityListBound δ n ∧
      list.card ≤ 4 * weightedSupportMultiplicity δ * n ^ (2 * capacityDerivativeOrder δ) ∧
      (2 * (weightedSupportMultiplicity δ * A + capacityDerivativeOrder δ -
        max k ⌊δ * (n : ℝ) / 2⌋₊) ≤ n →
        list.card ≤ 4 * weightedSupportMultiplicity δ * n ^ capacityDerivativeOrder δ) := by
  obtain ⟨list, hexact, hempty, hb⟩ :=
    exists_capacity_list δ hδ (by linarith) n k n A hn hk hkn hp le_rfl hgap hA α y
  exact ⟨list, hexact, hempty, hb.fieldIndependent, hb.finiteField hsmall,
    hb.largeField hsmall⟩
