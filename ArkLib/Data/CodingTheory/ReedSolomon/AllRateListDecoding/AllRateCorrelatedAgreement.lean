/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.PrescribedLineMCA
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.CorrelatedAgreementDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Mutual correlated agreement at every Reed–Solomon rate

For every positive capacity gap, one field-independent polynomial exceptional-set bound
works uniformly over message dimensions and evaluation sets. The exception is chosen once
for the two received words, before the challenge and every close polynomial. Outside it,
the full agreement set equals the constituent polynomials' common agreement set.

This is the qualitative all-rate line conclusion of [DKTZ26]. Its proof uses ordinary
joint-space incidence; it does not certify the manuscript's sharper numerical prefactor.
The prescribed small-gap derivative order remains available in `PrescribedLineMCA`.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed–Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], mutual correlated agreement and symbolic interpolation.
-/

noncomputable section

namespace ReedSolomon.AllRateListDecoding

open Polynomial

universe u

/-- Every positive gap has a field-independent polynomial bound on exceptional line
challenges, uniformly over all rates. The conclusion identifies the whole agreement set.
It covers characteristic zero and prime fields of size at least the block length. -/
theorem exists_allRate_correlatedAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n k A : ℕ), N ≤ n → 0 < k → k ≤ n → (k : ℝ) + δ * n ≤ A →
      ∀ (F : Type u) [Field F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) →
        ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
          ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ C * (n : ℝ) ^ (d + 1) ∧
            ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
              A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
              ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
                P = P₀ + Polynomial.C z * P₁ ∧
                polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
                  commonPolynomialAgreementSet domain f g P₀ P₁ := by
  classical
  let ε := min δ (1 / 8 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεquarter : ε < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  let d := Nat.ceil (Real.exp ((169 / 25) / ε))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let C := prescribedLineMCAConstant ε + 1
  have hC₀ : 0 ≤ prescribedLineMCAConstant ε := by
    unfold prescribedLineMCAConstant
    positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨8 * m, d, C, hC, ?_⟩
  intro n k A hn hk _hkn hgap F _ _ hchar domain f g
  have hthreshold : agreementThreshold ε n k ≤ A := by
    apply (agreementThreshold_le_iff_real hε.le n k A).mpr
    have hmul := mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
    linarith
  by_cases hsmall : agreementThreshold ε n k ≤ n
  · let E := AlgebraicClosure F
    let iota : F →+* E := algebraMap F E
    obtain ⟨exceptional, hcard, hgood⟩ := exists_prescribedLineMCA
      ε n k domain f g iota hε hεquarter hk hn hsmall hchar
    obtain ⟨baseExceptional, hbase, hbasegood⟩ :=
      exists_exceptional_correlatedAgreement_descend domain f g iota k
        (agreementThreshold ε n k) exceptional hgood
    refine ⟨baseExceptional, ?_, ?_⟩
    · apply (show (baseExceptional.card : ℝ) ≤ exceptional.card by exact_mod_cast hbase).trans
      apply hcard.trans
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]; linarith
      · positivity
    · intro z hz P hdegree hagree
      obtain ⟨pair, hleft, hright, heq, hsets⟩ :=
        hbasegood z hz P hdegree (hthreshold.trans hagree)
      refine ⟨pair.1, pair.2, hleft, hright, ?_, ?_⟩
      · simpa [correlatedPairSpecialization] using heq
      · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC.le (by positivity)
    · intro z _ P _ hagree
      have hcard : (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hsmall (hthreshold.trans (hagree.trans hcard))).elim

end ReedSolomon.AllRateListDecoding
