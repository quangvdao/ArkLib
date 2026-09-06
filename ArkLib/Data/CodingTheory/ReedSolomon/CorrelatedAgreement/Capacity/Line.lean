/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.PrescribedLine
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.ExtensionDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


/-!
# Line mutual correlated agreement at every Reed–Solomon rate

For every positive capacity gap, one field-independent polynomial exceptional-set bound
works uniformly over message dimensions and evaluation sets. The exception is chosen once
for the two received words, before the challenge and every close polynomial. Outside it,
the full agreement set equals the constituent polynomials' common agreement set.

This is the qualitative all-rate line conclusion of [DKTZ26]. Its proof uses ordinary
joint-space incidence; it does not certify the manuscript's sharper numerical prefactor.
The prescribed small-gap derivative order remains available in `exists_prescribedLineMCA`.

## Reading the statement

* `∃` means "there exist", `∀` means "for every", and `→` introduces an assumption.
  Thus `N`, `d`, and `C` depend only on the positive gap `δ`, not on the later inputs.
* `E n` is the polynomial exception budget. `A` is an integer agreement threshold;
  `k + δ * n ≤ A` expresses the capacity gap without rounding conventions.
* `α : Fin n ↪ F` is a list of `n` distinct evaluation points; `F[X]` means polynomials.
* `S z P` is the whole set where `P(α i) = f i + z * g i`.
  `T F₀ G₀` is the set where both `F₀(α i) = f i` and `G₀(α i) = g i`.
* The exceptional set is chosen BEFORE `z` and `P`. The final equality is of full sets,
  not merely a statement that some large common subset exists.
* `P.degree < k` includes the zero polynomial (whose degree is minus infinity).
  `Finset F` is finite even when `F` is infinite; `z • G₀` scales the coefficients of `G₀`.
  A `let` abbreviates an expression, not an extra assumption. Natural-to-real casts do
  not change the represented number. Since `A` is integral, its threshold condition is
  equivalent to `A ≥ k + ceil(δ * n)`.

## Agreement regimes

This is a mutual correlated agreement theorem, not a list-size or running-time theorem.
Unique-decoding and Johnson-range agreement results belong to the general
`CodingTheory/ProximityGap` development. The capacity list-size theorem is separately
in `ReedSolomon/ListDecodability/Capacity`. None of those properties should be inferred
from another merely because their decoding radii coincide.

Compared with the paper's qualitative theorem, `δ < 1` and `A ≤ n` are unnecessary:
impossible agreement thresholds give a vacuous conclusion. The characteristic bound
also includes equality `n = ringChar F`, covering prime fields of size exactly `n`.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Theorem 1.2 and Sections 8–9 and 11.
-/

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial

universe u

/-- Mutual correlated agreement at a fixed gap and specified error bound.

The exceptional set is chosen before the challenge and the close polynomial.
Equality of full agreement sets excludes accidental agreements outside the common set. -/
def HasCapacityLineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  -- Block length, message dimension, and agreement threshold.
  ∀ (n k A : ℕ),
    N ≤ n →
    0 < k →
    k ≤ n →
    (k : ℝ) + δ * n ≤ A →
  -- Fields may be infinite; only their characteristic is restricted.
  ∀ (F : Type u) [Field F] [DecidableEq F],
    (ringChar F = 0 ∨ n ≤ ringChar F) →
    ∀ (α : Fin n ↪ F) (f g : Fin n → F),
      -- S records every agreement with the received line at challenge z.
      let S := fun z P ↦ polynomialAgreementSet α (fun i ↦ f i + z * g i) P
      -- T records simultaneous agreement of a polynomial pair with f and g.
      let T := fun F₀ G₀ ↦ commonPolynomialAgreementSet α f g F₀ G₀
      -- One exceptional set works simultaneously for every close polynomial.
      ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E n ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (S z P).card →
          ∃ F₀ G₀ : F[X],
            F₀.degree < k ∧
            G₀.degree < k ∧
            -- Recover the candidate itself, not merely its evaluations on a subset.
            P = F₀ + z • G₀ ∧
            S z P = T F₀ G₀

/-- Every positive gap has a field-independent polynomial bound on exceptional line
challenges, uniformly over all rates. The conclusion identifies the whole agreement set.
It covers characteristic zero and prime fields of size at least the block length. -/
theorem exists_capacity_lineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      HasCapacityLineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) := by
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
  dsimp only [HasCapacityLineAgreement]
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
      · simpa [correlatedPairSpecialization, Polynomial.smul_eq_C_mul] using heq
      · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC.le (by positivity)
    · intro z _ P _ hagree
      have hcard : (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hsmall (hthreshold.trans (hagree.trans hcard))).elim

end ReedSolomon
