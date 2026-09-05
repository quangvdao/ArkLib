/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.HalfGap.Line
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FullAgreement

/-!
# Half-gap mutual correlated agreement

This module translates the characteristic-free half-gap correlated-agreement endpoint into
ArkLib's canonical `mcaError` API.  The affine-line error is at most `min 1 (2n / |F|)`.  The
line-to-affine reduction then bounds every positive-dimensional affine family by
`2n / (|F| - 1)`, independently of its dimension, and the complement of the actual MCA bad set
retains the exact full-agreement-set conclusion.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], Section 10.
* [Bordage, Chiesa, Guan, and Manzur, *All Polynomial Generators Preserve Distance with Mutual
  Correlated Agreement*][BCGM25], Lemma 7.1.
-/

namespace ReedSolomon

noncomputable section

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators ProbabilityTheory ENNReal

open Classical in
private theorem affineLine_bad_set_card_le_two_mul
    {F : Type} [Field F] [Fintype F] {n k A : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta))
    (U : Fin 2 → Fin n → F) :
    (Finset.univ.filter fun z : F ↦
      IsMCA (AffineLineGenerator F) (code domain k) z U delta).card ≤ 2 * n := by
  classical
  obtain ⟨exceptional, hExceptionalCard, hExceptional⟩ :=
    exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le
      domain (U 0) (U 1) hk hAn hhalf
  apply (Finset.card_le_card ?_).trans hExceptionalCard
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  obtain ⟨T, hTCard, hCombination, j, hj⟩ := hz
  have hAT : A ≤ T.card := by
    have hTCard' : (n : ℝ) * (1 - delta) ≤ T.card := by
      simpa only [Fintype.card_fin] using hTCard
    exact_mod_cast hthreshold.trans hTCard'
  have hCombination' :
      projectedWord (fun i ↦ U 0 i + z * U 1 i) T ∈
        projectedCodeSubmod (code domain k) T := by
    simpa [AffineLineGenerator, Fin.sum_univ_two, smul_eq_mul] using hCombination
  obtain ⟨P, hPDegree, hPOnT⟩ :=
    (projectedWord_mem_code_iff_exists_polynomial
      domain k (fun i ↦ U 0 i + z * U 1 i) T).mp hCombination'
  have hTSubset :
      T ⊆ polynomialAgreementSet domain (fun i ↦ U 0 i + z * U 1 i) P := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPOnT i hi⟩
  have hAgreement :
      A ≤ (polynomialAgreementSet domain (fun i ↦ U 0 i + z * U 1 i) P).card :=
    hAT.trans (Finset.card_le_card hTSubset)
  by_contra hzExceptional
  obtain ⟨F₀, G₀, hF₀Degree, hG₀Degree, _hPFormula, hExact⟩ :=
    hExceptional z hzExceptional P hPDegree hAgreement
  apply hj
  apply (projectedWord_mem_code_iff_exists_polynomial domain k (U j) T).mpr
  fin_cases j
  · refine ⟨F₀, hF₀Degree, fun i hi ↦ ?_⟩
    have hiCommon :
        i ∈ commonPolynomialAgreementSet domain (U 0) (U 1) F₀ G₀ := by
      rw [← hExact]
      exact hTSubset hi
    exact (Finset.mem_filter.mp hiCommon).2.1
  · refine ⟨G₀, hG₀Degree, fun i hi ↦ ?_⟩
    have hiCommon :
        i ∈ commonPolynomialAgreementSet domain (U 0) (U 1) F₀ G₀ := by
      rw [← hExact]
      exact hTSubset hi
    exact (Finset.mem_filter.mp hiCommon).2.2

open Classical in
/-- At a half-gap agreement threshold, the affine-line MCA error is at most `2n / |F|`. -/
theorem mcaError_affineLine_le_two_mul_div_card
    {F : Type} [Field F] [Fintype F] {n k A : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta)) :
    mcaError (AffineLineGenerator F) (code domain k) delta ≤
      (2 * n : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold mcaError
  refine iSup_le fun U ↦ ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast
    affineLine_bad_set_card_le_two_mul domain hk hAn hhalf delta hthreshold U

open Classical in
/-- The canonical probability-valued half-gap line bound, including its trivial upper bound. -/
theorem mcaError_affineLine_le_min_one_two_mul_div_card
    {F : Type} [Field F] [Fintype F] {n k A : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta)) :
    mcaError (AffineLineGenerator F) (code domain k) delta ≤
      min 1 ((2 * n : ENNReal) / (Fintype.card F : ENNReal)) := by
  exact le_min (mcaError_le_one _ _ _) <|
    mcaError_affineLine_le_two_mul_div_card domain hk hAn hhalf delta hthreshold

open Classical in
private theorem affineSpace_bad_density_le_two_mul_div_card_sub_one
    {F : Type} [Field F] [Fintype F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (hs : 1 ≤ s) (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta))
    (U : Fin (s + 1) → Fin n → F) :
    ((Finset.univ.filter fun x : Fin s → F ↦
      IsMCA (AffineSpaceGenerator F s) (code domain k) x U delta).card : ℝ) /
        (Fintype.card F : ℝ) ^ s ≤
      (2 * n : ℝ) / ((Fintype.card F : ℝ) - 1) := by
  classical
  obtain ⟨W, hLineTransfer⟩ :=
    AffineMCALemmas.exists_line_bound hs (code domain k) U delta
  have hLineCard :
      (Finset.univ.filter fun z : F ↦
        IsMCA (AffineLineGenerator F) (code domain k) z W delta).card ≤ 2 * n :=
    affineLine_bad_set_card_le_two_mul domain hk hAn hhalf delta hthreshold W
  have hq : (1 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card (α := F)
  have hLineDensity :
      ((Finset.univ.filter fun z : F ↦
        IsMCA (AffineLineGenerator F) (code domain k) z W delta).card : ℝ) /
          (Fintype.card F : ℝ) ≤
        (2 * n : ℝ) / (Fintype.card F : ℝ) := by
    gcongr
    exact_mod_cast hLineCard
  have hChain := hLineTransfer.trans hLineDensity
  have hFactor : 0 < 1 - 1 / (Fintype.card F : ℝ) := by
    rw [sub_pos, div_lt_one] <;> linarith
  calc
    ((Finset.univ.filter fun x : Fin s → F ↦
        IsMCA (AffineSpaceGenerator F s) (code domain k) x U delta).card : ℝ) /
          (Fintype.card F : ℝ) ^ s
        ≤ ((2 * n : ℝ) / (Fintype.card F : ℝ)) /
            (1 - 1 / (Fintype.card F : ℝ)) :=
      (le_div_iff₀ hFactor).2 (by simpa [mul_comm] using hChain)
    _ = (2 * n : ℝ) / ((Fintype.card F : ℝ) - 1) := by
      field_simp

open Classical in
/-- Every positive-dimensional affine family has half-gap MCA error at most
`2n / (|F| - 1)`, independently of its dimension. -/
theorem mcaError_affineSpace_le_two_mul_div_card_sub_one
    {F : Type} [Field F] [Fintype F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (hs : 1 ≤ s) (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta)) :
    mcaError (AffineSpaceGenerator F s) (code domain k) delta ≤
      ENNReal.ofReal ((2 * n : ℝ) / ((Fintype.card F : ℝ) - 1)) := by
  unfold mcaError
  refine iSup_le fun U ↦ ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  simpa [Fintype.card_fun, Fintype.card_fin, Finset.prod_const] using
    affineSpace_bad_density_le_two_mul_div_card_sub_one
      domain hk hAn hhalf hs delta hthreshold U

open Classical in
/-- Outside an affine exceptional set of density at most `2n / (|F| - 1)`, every close
Reed--Solomon polynomial is the affine combination of constituent degree-`< k` polynomials, and
its full agreement set is exactly their common agreement set. -/
theorem exists_affine_exceptionalSet_full_agreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A)
    (hs : 1 ≤ s) (delta : ℝ) (hthreshold : (A : ℝ) ≤ n * (1 - delta))
    (U : Fin (s + 1) → Fin n → F) :
    ∃ exceptional : Finset (Fin s → F),
      (exceptional.card : ℝ) ≤
          (2 * n : ℝ) * (Fintype.card F : ℝ) ^ s /
            ((Fintype.card F : ℝ) - 1) ∧
      ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
        ((Finset.univ.filter fun i ↦
          P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
            Fintype.card (Fin n) * (1 - delta) →
        ∃ P₀ : Fin (s + 1) → F[X],
          (∀ j, (P₀ j).degree < k) ∧
          P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
          ∀ i,
            (P.eval (domain i) =
                ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
              ∀ j, (P₀ j).eval (domain i) = U j i := by
  classical
  let exceptional := Finset.univ.filter fun x : Fin s → F ↦
    IsMCA (AffineSpaceGenerator F s) (code domain k) x U delta
  refine ⟨exceptional, ?_, ?_⟩
  · have hDensity := affineSpace_bad_density_le_two_mul_div_card_sub_one
      domain hk hAn hhalf hs delta hthreshold U
    have hqPow : 0 < (Fintype.card F : ℝ) ^ s := by positivity
    calc
      (exceptional.card : ℝ) ≤
          ((2 * n : ℝ) / ((Fintype.card F : ℝ) - 1)) *
            (Fintype.card F : ℝ) ^ s := (div_le_iff₀ hqPow).1 hDensity
      _ = (2 * n : ℝ) * (Fintype.card F : ℝ) ^ s /
            ((Fintype.card F : ℝ) - 1) := by ring
  · intro x hx P hPDegree hClose
    have hGood : ¬ IsMCA (AffineSpaceGenerator F s) (code domain k) x U delta := by
      simpa only [exceptional, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hkThreshold : (k : ℝ) ≤ Fintype.card (Fin n) * (1 - delta) := by
      have hkA : k ≤ A := by omega
      simpa only [Fintype.card_fin] using
        ((Nat.cast_le.mpr hkA).trans hthreshold)
    exact ReedSolomon.exists_polynomials_full_agreement_of_not_isMCA
      domain k (AffineSpaceGenerator F s) x U delta hkThreshold hGood P hPDegree
        (by
          convert hClose using 1
          congr 2
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end

end ReedSolomon
