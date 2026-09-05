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
