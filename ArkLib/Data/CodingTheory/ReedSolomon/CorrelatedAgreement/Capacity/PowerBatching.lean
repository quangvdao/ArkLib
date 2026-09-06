/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.PrescribedCurve
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.ExtensionDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Power-batching mutual correlated agreement at every Reed--Solomon rate

For every positive capacity gap, polynomial curves of every positive degree have a
field-independent exceptional-set bound linear in the curve degree.  The derivative order is
the same gap-dependent order used by the line theorem, and the block-length exponent is `d+1`.

The algebraically closed extension-field theorem is descended to the original field before the
public conclusion is unpacked.  Thus the constituent polynomials live over the received-word
field, and exactness identifies the entire agreement set rather than only a large common subset.
The characteristic hypothesis depends on the block length, not on the batching degree.

The chunked power lift used upstream has deliberately looser constants than the paper's exact
mixed-bidegree calculation, while preserving its qualitative exponent and linear batching loss.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial

universe u

/-- Mutual correlated agreement for powers batching at a fixed gap and error bound.

The constants are chosen before the batching degree, block length, field, received words,
challenge, and close polynomial.  The exceptional set is chosen before the last two. -/
def HasCapacityPowerBatchingAgreement
    (δ : ℝ) (N : ℕ) (E : ℕ → ℕ → ℝ) : Prop :=
  ∀ (ℓ n k A : ℕ),
    0 < ℓ →
    N ≤ n →
    0 < k →
    k ≤ n →
    (k : ℝ) + δ * n ≤ A →
  ∀ (F : Type u) [Field F] [DecidableEq F],
    (ringChar F = 0 ∨ n ≤ ringChar F) →
    ∀ (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F),
      let S := fun z P ↦ polynomialAgreementSet domain (powerBatchedWord w z) P
      let T := fun P : Fin (ℓ + 1) → F[X] ↦ commonCurveAgreementSet domain w P
      ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E ℓ n ∧
        ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k → A ≤ (S z Q).card →
          ∃ P : Fin (ℓ + 1) → F[X],
            (∀ t, (P t).degree < k) ∧
            Q = powerBatchedPolynomial P z ∧
            S z Q = T P

/-- **Power-batching MCA up to capacity.** Every positive gap admits a block threshold,
derivative order, and positive field-independent constant such that degree-`ℓ` powers batching
has at most `ℓ * C * n^(d+1)` exceptional challenges.  Outside them, every close polynomial is
the exact power combination of low-degree constituent messages and has precisely their common
agreement set. -/
theorem exists_capacity_powerBatchingAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      HasCapacityPowerBatchingAgreement δ N
        (fun ℓ n ↦ (ℓ : ℝ) * C * (n : ℝ) ^ (d + 1)) := by
  classical
  let ε := min δ (1 / 8 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεquarter : ε < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  let d := Nat.ceil (Real.exp ((169 / 25) / ε))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let C := prescribedCurveMCAConstant ε + 1
  have hC₀ : 0 ≤ prescribedCurveMCAConstant ε := by
    unfold prescribedCurveMCAConstant polynomialCurveUniformMCAConstant
    positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨8 * m, d, C, hC, ?_⟩
  dsimp only [HasCapacityPowerBatchingAgreement]
  intro ℓ n k A hℓ hn hk _hkn hgap F _ _ hchar domain w
  have hthreshold : agreementThreshold ε n k ≤ A := by
    apply (agreementThreshold_le_iff_real hε.le n k A).mpr
    have hmul := mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
    linarith
  by_cases hsmall : agreementThreshold ε n k ≤ n
  · let E := AlgebraicClosure F
    let iota : F →+* E := algebraMap F E
    obtain ⟨exceptional, hcard, hgood⟩ := exists_prescribedCurveMCA
      ε n k ℓ domain w iota hε hεquarter hk hℓ hn hsmall hchar
    obtain ⟨baseExceptional, hbase, hbasegood⟩ :=
      exists_exceptional_powerAgreement_descend domain w iota k
        (agreementThreshold ε n k) exceptional hgood
    refine ⟨baseExceptional, ?_, ?_⟩
    · apply (show (baseExceptional.card : ℝ) ≤ exceptional.card by exact_mod_cast hbase).trans
      apply hcard.trans
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · dsimp only [C]
          linarith
        · positivity
      · positivity
    · intro z hz Q hdegree hagree
      obtain ⟨P, hP, heq, hsets⟩ :=
        hbasegood z hz Q hdegree (hthreshold.trans hagree)
      refine ⟨P, hP, ?_, ?_⟩
      · simpa [powerBatchedPolynomial, Polynomial.smul_eq_C_mul] using heq
      · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro z _ Q _ hagree
      have hcard : (polynomialAgreementSet domain (powerBatchedWord w z) Q).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hsmall (hthreshold.trans (hagree.trans hcard))).elim

end ReedSolomon
