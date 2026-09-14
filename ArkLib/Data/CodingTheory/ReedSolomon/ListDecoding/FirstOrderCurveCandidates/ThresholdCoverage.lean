/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentFilter
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.FilterCore

/-! # Threshold coverage from componentwise universal-agreement bounds -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ThresholdCoverage

open CompPoly Polynomial.FunctionFieldAlgorithms
open CPolynomial.PolynomialThreshold

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- A geometric point with `A` distinct agreeing positions supplies at least `A-k+1`
vanishing coefficient rows once each global component has at most `k-1` universal rows. -/
theorem coefficient_positions_bound {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (h : CBivariate E) (gs : List (CBivariate E)) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (hpoint : ComponentDescent.evalAt phi u v h = 0)
    (A k : ℕ) (hk : 0 < k) (hkA : k ≤ A) (S : Finset ℕ) (hcard : A ≤ S.card)
    (hagree : ∀ i ∈ S, ∃ g, gs[i]? = some g ∧ ComponentDescent.evalAt phi u v g = 0)
    (huniversal : ∀ a ∈ (ComponentDescent.run h gs).blocks, a.universal.length ≤ k - 1)
    (cs : List (CPolynomial E)) (hcs : FilterCore.coefficients? h gs = some cs) :
    A - k + 1 ≤ (vanishingPositions phi u cs.toArray).card := by
  classical
  obtain ⟨a, ha, hav⟩ := ComponentDescent.run_allFiber_coverage phi u v h gs hh hpoint
  have hlabel : a.universal.toFinset.card ≤ k - 1 := by
    rw [List.toFinset_card_of_nodup (ComponentDescent.run_labels_nodup h gs a ha)]
    exact huniversal a ha
  have hsub : S \ a.universal.toFinset ⊆ vanishingPositions phi u cs.toArray := by
    intro i hi
    obtain ⟨hiS, hiU⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨g, hig, hgv⟩ := hagree i hiS
    obtain ⟨c, hic, hfilter⟩ := FilterCore.coefficients?_getElem? h gs cs hcs i g hig
    have hzero := residualFilter?_vanishes_of_scan_point phi u v h gs hh hs a ha
      i g hig (by simpa using hiU) hav hgv c hfilter
    have hil : i < cs.length := by
      by_contra hn
      have hz : cs[i]? = none := List.getElem?_eq_none (by omega)
      rw [hic] at hz
      contradiction
    simp only [vanishingPositions, Finset.mem_filter, Finset.mem_range, List.size_toArray]
    refine ⟨hil, ?_⟩
    simpa only [List.getElem?_toArray, hic, Option.getD_some] using hzero
  have hcount := Finset.card_le_card_sdiff_add_card (s := S) (t := a.universal.toFinset)
  have hdetected := Finset.card_le_card hsub
  omega

/-- The executed threshold vanishes at every sufficiently agreeing geometric point. -/
theorem run_threshold_vanishes {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CBivariate E) (gs : List (CBivariate E)) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (hpoint : ComponentDescent.evalAt phi u v h = 0)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ gs.length)
    (S : Finset ℕ) (hcard : A ≤ S.card)
    (hagree : ∀ i ∈ S, ∃ g, gs[i]? = some g ∧ ComponentDescent.evalAt phi u v g = 0)
    (huniversal : ∀ a ∈ (ComponentDescent.run h gs).blocks, a.universal.length ≤ k - 1)
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out) :
    out.thresholdPolynomial.toPoly.eval₂ phi u = 0 := by
  obtain ⟨cs, H, hcs, hH, rfl⟩ := FilterCore.run_provenance p inverse A k h gs out hout
  obtain ⟨hlen, hm⟩ := FilterCore.coefficients?_properties h gs cs hcs
  have hbound := coefficient_positions_bound phi u v h gs hh hs hpoint A k hk hkA
    S hcard hagree huniversal cs hcs
  apply (threshold_root_positions_iff phi u cs.toArray _ (A - k + 1)
    (by omega) (by simp only [List.size_toArray]; omega) H hH).mpr hbound
  intro c hc
  exact (CPolynomial.toPoly_eq_zero_iff c).not.mp
    ((CPolynomial.monic_toPoly_iff c).mp (hm c (by simpa using hc))).ne_zero

/-- Fin-indexed form for received positions; taking the image of `Fin.val` preserves their count. -/
theorem run_threshold_vanishes_fin {K : Type*} [Field K] (phi : E →+* K) (u v : K)
    (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CBivariate E) (gs : List (CBivariate E)) (hh : h.monic)
    (hs : Squarefree (ClearDenominators.valueGlobal h))
    (hpoint : ComponentDescent.evalAt phi u v h = 0)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ gs.length)
    (S : Finset (Fin gs.length)) (hcard : A ≤ S.card)
    (hagree : ∀ i ∈ S, ComponentDescent.evalAt phi u v gs[i] = 0)
    (huniversal : ∀ a ∈ (ComponentDescent.run h gs).blocks, a.universal.length ≤ k - 1)
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out) :
    out.thresholdPolynomial.toPoly.eval₂ phi u = 0 := by
  classical
  apply run_threshold_vanishes phi u v p inverse A k h gs hh hs hpoint hk hkA hAn
    (S.image Fin.val) _ _ huniversal out hout
  · simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hcard
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨gs[j], by simp, hagree j hj⟩

/-- A detected point rules out the empty/unit-threshold branch. -/
theorem run_base_ne_none {K : Type*} [Field K] (phi : E →+* K) (u : K)
    (p : ℕ) [Fact p.Prime] (inverse : E → E) (A k : ℕ)
    (h : CBivariate E) (gs : List (CBivariate E))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (hz : out.thresholdPolynomial.toPoly.eval₂ phi u = 0) : out.base ≠ none := by
  intro hn
  have hunit := (FilterCore.run_base_none_iff p inverse A k h gs out hout).mp hn
  rw [hunit, CPolynomial.toPoly_one, Polynomial.eval₂_one] at hz
  exact one_ne_zero hz

/-- The actual radical base exists and contains the detected parameter. -/
theorem run_base_exists_vanishes {K : Type*} [Field K] (phi : E →+* K) (u : K)
    (p : ℕ) [Fact p.Prime] [CharP E p] (inverse : E → E)
    (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CBivariate E) (gs : List (CBivariate E))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (hz : out.thresholdPolynomial.toPoly.eval₂ phi u = 0) :
    ∃ G, out.base = some G ∧ G.toPoly.eval₂ phi u = 0 := by
  cases heq : out.base with
  | none => exact False.elim (run_base_ne_none phi u p inverse A k h gs out hout hz heq)
  | some G =>
    exact ⟨G, rfl, (FilterCore.run_base_eval₂_eq_zero_iff
      p inverse hinverse A k h gs out hout G heq phi u).mpr hz⟩

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ThresholdCoverage
