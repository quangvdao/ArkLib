/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine.Construction
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Correlated-agreement failure on the rational line

The deterministic contract gives a half-close explanation at every challenge, but
no joint half-close explanation for the sources. The generic CA endpoint then gives
error one. MCA follows from the existing comparison `CA ≤ MCA ≤ 1`.
-/

namespace ReedSolomon.Binary

open Polynomial CoreDefinitions
open scoped NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A rational-line contract at half agreement, with smaller common agreement,
forces CA error one. -/
theorem RationalLineBounds.epsCa_eq_one {k A : ℕ} {f g : F → F} {p : F → F[X]}
    (h : RationalLineBounds k A f g p) (hcard : Fintype.card F = 2 * A)
    (hgap : k + 1 < A) :
    ProximityGap.epsCa (F := F) (code (Function.Embedding.refl F) k : Set (F → F))
      (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 := by
  classical
  let U : Code.WordStack F (Fin 2) F := ![f, g]
  apply ProximityGap.epsCa_eq_one_of_all_folds_close_not_joint _ (1 / 2) U
  · intro hjoint
    rw [← Code.jointAgreement_iff_jointProximity] at hjoint
    obtain ⟨S, hS, v, hv⟩ := hjoint
    have hhalf : (1 - (1 / 2 : ℝ≥0)) * (Fintype.card F : ℝ≥0) = A := by
      rw [hcard]
      apply NNReal.eq
      norm_num [NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
      ring
    rw [hhalf] at hS
    have hScard : A ≤ S.card := by exact_mod_cast hS
    obtain ⟨P, hP, hevalP⟩ := mem_code_iff_eval.mp (hv 0).1
    obtain ⟨Q, hQ, hevalQ⟩ := mem_code_iff_eval.mp (hv 1).1
    have hsub : S ⊆ commonPolynomialAgreementSet (Function.Embedding.refl F) f g P Q := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · simpa [U] using (hevalP x).trans (Finset.mem_filter.mp ((hv 0).2 hx)).2
      · simpa [U] using (hevalQ x).trans (Finset.mem_filter.mp ((hv 1).2 hx)).2
    exact (Nat.not_le_of_gt hgap)
      (hScard.trans ((Finset.card_le_card hsub).trans (h.commonUpper P Q hP hQ)))
  · intro z
    rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
    refine ⟨evalOnPoints (Function.Embedding.refl F) (p z),
      evalOnPoints_mem_code_of_degree_lt (h.degree_lt z), ?_⟩
    rw [Code.pairRelDist_le_iff_pairDist_le]
    have hfloor : ⌊(1 / 2 : ℝ≥0) * (Fintype.card F : ℝ≥0)⌋₊ = A := by simp [hcard]
    rw [hfloor]
    have hsum := Code.agree_add_hammingDist
      (u := U 0 + z • U 1) (v := evalOnPoints (Function.Embedding.refl F) (p z))
    have hagree : Code.agree (U 0 + z • U 1)
        (evalOnPoints (Function.Embedding.refl F) (p z)) = A := h.exactAgreement z
    rw [hagree, hcard] at hsum
    omega

/-- The quarter-rate full-domain binary RS code has ordinary CA error one at half distance. -/
theorem rationalLine_epsCa_eq_one [CharP F 2] {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    ProximityGap.epsCa (F := F)
      (code (Function.Embedding.refl F) (Fintype.card F / 4) : Set (F → F))
      (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 := by
  obtain ⟨τ, _, h⟩ := exists_rationalLine hm hcard
  have hq : 8 ≤ Fintype.card F := by
    rw [hcard]
    exact Nat.le_trans (by norm_num : 8 ≤ 2 ^ 3)
      (Nat.pow_le_pow_right (by omega) hm)
  have hhalf : Fintype.card F = 2 * (Fintype.card F / 2) := by
    calc
      Fintype.card F = 2 ^ ((m - 1) + 1) := by rw [hcard]; congr 1; omega
      _ = 2 * (2 ^ (m - 1)) := by rw [pow_succ]; omega
      _ = 2 * (Fintype.card F / 2) := by
        rw [← binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard]
  exact h.epsCa_eq_one hhalf (by omega)

omit [DecidableEq F] in
/-- The quarter-rate full-domain binary RS code also has MCA error one at half distance. -/
theorem rationalLine_mcaError_eq_one [CharP F 2] {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    mcaError (AffineLineGenerator F)
      (code (Function.Embedding.refl F) (Fintype.card F / 4)) (1 / 2) = 1 := by
  classical
  apply le_antisymm (mcaError_le_one _ _ _)
  have h := ProximityGap.epsCa_le_mcaError_affineLine
    (code (Function.Embedding.refl F) (Fintype.card F / 4)) (1 / 2 : ℝ≥0)
  rw [rationalLine_epsCa_eq_one hm hcard] at h
  exact h

end ReedSolomon.Binary
