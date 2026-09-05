/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AllRateCorrelatedAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.LineToAffineAgreement

/-!
# All-rate affine mutual correlated agreement

For each positive gap to capacity, the constants are chosen before the field, message
dimension, and evaluation domain. At distance radius `1 - k / n - δ`, the canonical line
MCA error is bounded by `C * n ^ (d + 1) / |F|`, and the affine error by
`C * n ^ (d + 1) / (|F| - 1)`, independently of affine dimension. One affine exceptional
set also retains the exact full-agreement conclusion for every close polynomial.
-/

noncomputable section

namespace ReedSolomon.AllRateListDecoding

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators

/-- Gap-only constants give line and dimension-independent affine MCA bounds at every rate,
including a single affine exceptional set before every close polynomial witness. -/
theorem exists_allRate_affineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / (Fintype.card F : ℝ)) ∧
          ∀ s : ℕ, 1 ≤ s →
            mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / ((Fintype.card F : ℝ) - 1)) ∧
            ∀ U : Fin (s + 1) → Fin n → F,
              ∃ exceptional : Finset (Fin s → F),
                (exceptional.card : ℝ) ≤ C * (n : ℝ) ^ (d + 1) *
                  (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
                ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
                  ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                    ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
                      (k : ℝ) + δ * n →
                  ∃ P₀ : Fin (s + 1) → F[X],
                    (∀ j, (P₀ j).degree < k) ∧
                    P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
                    ∀ i, (P.eval (domain i) =
                        ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
                      ∀ j, (P₀ j).eval (domain i) = U j i := by
  classical
  obtain ⟨N, d, C, hC, hline⟩ := exists_allRate_correlatedAgreement δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  let radius : ℝ := 1 - (k : ℝ) / n - δ
  let A : ℕ := ⌈(n : ℝ) * (1 - radius)⌉₊
  have hthreshold : (n : ℝ) * (1 - radius) = k + δ * n := by
    dsimp [radius]
    field_simp
    ring
  have hgap : (k : ℝ) + δ * n ≤ A := by
    rw [← hthreshold]
    exact Nat.le_ceil _
  have hexact : LineExactAgreementBound domain k A (C * (n : ℝ) ^ (d + 1)) := by
    intro f g
    exact hline n k A hn hk hkn hgap F hchar domain f g
  have hkthreshold : (k : ℝ) ≤ n * (1 - radius) := by
    rw [hthreshold]
    exact le_add_of_nonneg_right (mul_nonneg hδ.le hnpos.le)
  refine ⟨mcaError_affineLine_le_of_exactAgreement domain _ hexact radius (le_refl A), ?_⟩
  intro s hs
  refine ⟨mcaError_affineSpace_le_of_exactAgreement domain _ hexact hs radius (le_refl A), ?_⟩
  intro U
  simpa only [Fintype.card_fin, hthreshold] using
    exists_affine_exceptionalSet_full_agreement_of_exactLine domain _ hexact hs radius
      (le_refl A) hkthreshold U

end ReedSolomon.AllRateListDecoding
