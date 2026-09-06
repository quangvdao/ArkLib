/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Agreement witnesses giving maximal correlated-agreement errors

If every affine combination has a sufficiently large polynomial agreement set, but the
second word has no such agreement set, the affine-line MCA bad event holds at every seed.
At half agreement this also gives ordinary correlated-agreement error one.
-/

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode Probability
open scoped ProbabilityTheory NNReal

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]

/-- Sufficiently large agreement witnesses for every mixture, together with a strict
agreement bound for the direction, force affine-line MCA error one. -/
theorem mcaError_affineLine_eq_one_of_agreement_witnesses
    (domain : ι ↪ F) (k T : ℕ) (δ : ℝ) (f g : ι → F)
    (hthreshold : (Fintype.card ι : ℝ) * (1 - δ) ≤ T)
    (hclose : ∀ z : F, ∃ P : F[X], P.degree < k ∧
      T ≤ Code.agree (fun i ↦ f i + z * g i) (fun i ↦ P.eval (domain i)))
    (hfar : ∀ P : F[X], P.degree < k →
      Code.agree g (fun i ↦ P.eval (domain i)) < T) :
    mcaError (AffineLineGenerator F) (code domain k) δ = 1 := by
  classical
  let U : Fin 2 → ι → F := ![f, g]
  have hbad : ∀ z : F, IsMCA (AffineLineGenerator F) (code domain k) z U δ := by
    intro z
    obtain ⟨P, hp, ha⟩ := hclose z
    let S : Finset ι := Finset.univ.filter fun i ↦ f i + z * g i = P.eval (domain i)
    have hScard : T ≤ S.card := ha
    refine ⟨S, hthreshold.trans (by exact_mod_cast hScard), ?_, 1, ?_⟩
    · apply (mem_projectedCodeSubmod_iff _ _ _).mpr
      refine ⟨evalOnPoints domain P, evalOnPoints_mem_code_of_degree_lt hp, ?_⟩
      funext i
      have hi := (Finset.mem_filter.mp i.property).2
      simpa [projectedWord, U, AffineLineGenerator, Fin.sum_univ_two, evalOnPoints] using hi
    · intro h
      obtain ⟨c, hc, heq⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp h
      obtain ⟨Q, hQ, hQeval⟩ := mem_code_iff_eval.mp hc
      have hsubset : S ⊆ Finset.univ.filter (fun i ↦ g i = Q.eval (domain i)) := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have h := congrFun heq ⟨i, hi⟩
        have hQi := hQeval i
        simpa [projectedWord, U] using h.trans hQi.symm
      have hcount : T ≤ Code.agree g (fun i ↦ Q.eval (domain i)) :=
        hScard.trans (Finset.card_le_card hsubset)
      exact (Nat.not_le_of_gt (hfar Q hQ)) hcount
  apply le_antisymm (mcaError_le_one _ _ _)
  have hle := le_iSup
    (fun V ↦ Pr_{let z ←$ᵖ F}[IsMCA (AffineLineGenerator F) (code domain k) z V δ]) U
  have hprob : Pr_{let z ←$ᵖ F}[IsMCA (AffineLineGenerator F) (code domain k) z U δ] = 1 := by
    rw [prob_uniform_eq_ofReal]
    simp [hbad]
  simpa only [mcaError, hprob] using hle

/-- Half-agreement witnesses and a direction with strictly fewer than half agreements
also force ordinary correlated-agreement error one. -/
theorem epsCa_half_eq_one_of_agreement_witnesses [Nonempty ι]
    (domain : ι ↪ F) (k T : ℕ) (hcard : Fintype.card ι = 2 * T) (f g : ι → F)
    (hclose : ∀ z : F, ∃ P : F[X], P.degree < k ∧
      T ≤ Code.agree (fun i ↦ f i + z * g i) (fun i ↦ P.eval (domain i)))
    (hfar : ∀ P : F[X], P.degree < k →
      Code.agree g (fun i ↦ P.eval (domain i)) < T) :
    ProximityGap.epsCa (F := F) (code domain k : Set (ι → F))
      (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 := by
  classical
  let U : Code.WordStack F (Fin 2) ι := ![f, g]
  have hnot : ¬ Code.jointProximity (code domain k : Set (ι → F)) (u := U)
      (1 / 2 : ℝ≥0) := by
    intro h
    rw [← Code.jointAgreement_iff_jointProximity] at h
    obtain ⟨S, hS, v, hv⟩ := h
    have hScard : T ≤ S.card := by
      have hh : (1 - (1 / 2 : ℝ≥0)) * (Fintype.card ι : ℝ≥0) = T := by
        rw [hcard]
        apply NNReal.eq
        norm_num [NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
        ring
      rw [hh] at hS
      exact_mod_cast hS
    obtain ⟨Q, hQ, heval⟩ := mem_code_iff_eval.mp (hv 1).1
    have hsubset : S ⊆ Finset.univ.filter (fun i ↦ g i = Q.eval (domain i)) := by
      intro i hi
      have hv' := (Finset.mem_filter.mp ((hv 1).2 hi)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [U] using hv'.symm.trans (heval i).symm⟩
    exact (Nat.not_le_of_gt (hfar Q hQ)) (hScard.trans (Finset.card_le_card hsubset))
  have hfold : ∀ z : F,
      Code.relDistFromCode (U 0 + z • U 1) (code domain k : Set (ι → F)) ≤
        (1 / 2 : ℝ≥0) := by
    intro z
    obtain ⟨P, hp, ha⟩ := hclose z
    rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
    refine ⟨evalOnPoints domain P, evalOnPoints_mem_code_of_degree_lt hp, ?_⟩
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    let S : Finset ι := Finset.univ.filter fun i ↦ f i + z * g i = P.eval (domain i)
    refine ⟨S, ?_, ?_⟩
    · have hfloor : ⌊(1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ = T := by
        simp [hcard]
      rw [hfloor, hcard]
      change T ≤ S.card at ha
      omega
    · intro i
      simp [S, U, evalOnPoints]
  refine le_antisymm ?_ ?_
  · unfold ProximityGap.epsCa
    apply iSup_le
    intro V
    split_ifs
    · exact zero_le
    · exact PMF.coe_le_one _ True
  have hle := le_iSup
    (fun V : Code.WordStack F (Fin 2) ι ↦
      if Code.jointProximity (code domain k : Set (ι → F)) (u := V) (1 / 2 : ℝ≥0)
      then (0 : ENNReal) else
        Pr_{let z ←$ᵖ F}[Code.relDistFromCode (V 0 + z • V 1)
          (code domain k : Set (ι → F)) ≤ (1 / 2 : ℝ≥0)]) U
  have hprob : Pr_{let z ←$ᵖ F}[Code.relDistFromCode (U 0 + z • U 1)
      (code domain k : Set (ι → F)) ≤ (1 / 2 : ℝ≥0)] = 1 := by
    rw [prob_uniform_eq_ofReal]
    simp only [hfold]
    simp
  rw [if_neg hnot, hprob] at hle
  exact hle

end ReedSolomon
