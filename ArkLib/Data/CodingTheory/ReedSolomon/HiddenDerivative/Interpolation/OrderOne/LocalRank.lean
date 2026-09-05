/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.LocalRank

/-! # The actual order-one local rank for the intermediate-gap certificate -/

noncomputable section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- With derivative order one there are no higher-jet coordinates. -/
theorem weightedHigherJetCount_one (W : ℕ) : weightedHigherJetCount 1 W = 1 := by
  let z : HigherJetTuple 1 := fun i ↦ Fin.elim0 i
  have hz : ∀ c : HigherJetTuple 1, c = z := by
    intro c
    funext i
    exact Fin.elim0 i
  have h : weightedHigherJetTuples 1 W = {z} := by
    ext c
    rw [Finset.mem_singleton]
    constructor
    · exact fun _ ↦ hz c
    · rintro rfl
      simp only [weightedHigherJetTuples, Finset.mem_filter, higherJetTupleBox,
        Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun i ↦ Fin.elim0 i, by simp [higherJetTupleWeight]⟩
  rw [weightedHigherJetCount, h]
  simp

/-- The exact exhibited-kernel budget at `d=1`, multiplicity `64`, and
first-jet cap `16` is the manuscript constant `28152`. -/
theorem certifiedEnlargedRankBound_one_64_16 :
    certifiedEnlargedRankBound 1 64 16 0 = 28152 := by
  simp only [certifiedEnlargedRankBound]
  simp_rw [weightedHigherJetCount_one]
  norm_num [certifiedContactRankBudget, exhibitedKernelResidualCount, ambientContactCount,
    exhibitedKernelContactCount, contactThreshold, Finset.sum_range_succ]

/-- Actual, point-dependent local rank bound for the intermediate-gap exact
interpolation space. This is not a numerical rank assumption. -/
theorem finrank_exactLocalConstraintAt_orderOne_le
    {F : Type*} [Field F] {D A : ℕ} (hD : 1 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (exactLocalConstraintAt (D := D) (A := A) (M := 16) (W := 0)
        hD 64 center received)) ≤ 28152 :=
  (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
    (F := F) (d := 1) (D := D) (A := A) (m := 64) (M := 16) (W := 0)
    (by omega) hD center received).trans_eq certifiedEnlargedRankBound_one_64_16

end ReedSolomon.HiddenDerivative
