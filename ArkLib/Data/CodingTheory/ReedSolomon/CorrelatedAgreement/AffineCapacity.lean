/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.LineToAffine


/-!
# All-rate affine mutual correlated agreement

For each positive gap to capacity, the constants are chosen before the field, message
dimension, and evaluation domain. At distance radius `1 - k / n - δ`, the canonical line
MCA error is bounded by `C * n ^ (d + 1) / |F|`, and the affine error by
`C * n ^ (d + 1) / (|F| - 1)`, independently of affine dimension. One affine exceptional
set also retains the exact full-agreement conclusion for every close polynomial.

The paper-facing theorem spells out an affine received family as a constant word and its
directions. The probability corollary separately states the canonical MCA errors.
These are qualitative consequences of [DKTZ26], not its sharper numerical prefactor.

## Reading the statements

The received family is a constant word `a` plus directions `u`, with parameter `t`.
The polynomial witnesses have the matching form `F₀ + ∑ j, t j • G j`; the symbol
`•` multiplies every coefficient by the scalar. Degree `< k` includes the zero
polynomial, whose Lean degree is minus infinity. The final pointwise equivalence
identifies every agreement position, not just a selected large subset.

The constants precede the code and affine dimension. The exceptional set precedes
every parameter and polynomial witness; the constituent witnesses may depend on both.
Over a field of size `q`, the parameter space has `q ^ s` elements. Dividing the
exceptional cardinality bound by that size gives density at most
`C * n ^ (d + 1) / (q - 1)`, independently of `s`.

The separate probability theorem uses `mcaError`, the worst-case probability over
received families. Despite its historical name, `IsMCA` describes the bad event:
some sufficiently large position set admits the combined word as a restricted
codeword but does not admit all constituent words. `ENNReal.ofReal` places the
nonnegative real bound in the extended nonnegative reals used for probabilities.
The joint theorem retains one shared choice of constants for witnesses and errors.

Here `ℕ` and `ℝ` denote natural and real numbers; a cast such as `(n : ℝ)` preserves
the integer's value. The real agreement condition is equivalent to at least
`k + ceil(δ * n)` positions. A `let` abbreviates an expression, not an assumption.
`DecidableEq F` supplies equality decisions for finite sets and is available classically.
The line theorem permits infinite fields; these probability statements require finite ones.
These are mathematical agreement theorems, not running-time bounds.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Theorem 1.2 and Corollary 9.10 (affine families).
-/

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators

/-- Joint quantitative interface: one choice of constants gives both the probability bounds
and exact affine witnesses. For the paper-facing presentations, see
`exists_capacity_affineAgreement` and `exists_capacity_mcaError` below. -/
theorem exists_capacity_affineAgreement_and_mcaError (δ : ℝ) (hδ : 0 < δ) :
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
  obtain ⟨N, d, C, hC, hline⟩ := exists_capacity_lineAgreement δ hδ
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
    simpa only [Polynomial.smul_eq_C_mul] using hline n k A hn hk hkn hgap F hchar domain f g
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

/-- **Affine-family agreement, qualitatively [DKTZ26].** For each positive gap, choose
constants before the field, code, and affine dimension. For a constant word `a` and directions
`u`, one exceptional set works for every parameter `t` and every close polynomial `P`.
Outside it, `P` is the same affine combination of low-degree constituent polynomials, and
its entire agreement set is their common agreement set. The exceptional density is at most
`C * n ^ (d + 1) / (|F| - 1)`, independently of the number of directions. -/
theorem exists_capacity_affineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          ∀ s : ℕ, 1 ≤ s → ∀ (a : Fin n → F) (u : Fin s → Fin n → F),
            ∃ exceptional : Finset (Fin s → F),
              (exceptional.card : ℝ) ≤ C * (n : ℝ) ^ (d + 1) *
                (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
              ∀ t ∉ exceptional, ∀ P : F[X], P.degree < k →
                ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                  a i + ∑ j, t j * u j i).card : ℝ) ≥ (k : ℝ) + δ * n →
                ∃ (F₀ : F[X]) (G : Fin s → F[X]),
                  F₀.degree < k ∧ (∀ j, (G j).degree < k) ∧
                  P = F₀ + ∑ j, t j • G j ∧
                  ∀ i, (P.eval (domain i) = a i + ∑ j, t j * u j i) ↔
                    F₀.eval (domain i) = a i ∧ ∀ j, (G j).eval (domain i) = u j i := by
  classical
  obtain ⟨N, d, C, hC, hall⟩ := exists_capacity_affineAgreement_and_mcaError δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain s hs a u
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ((hall n k hn hk hkn F hchar domain).2 s hs).2 (Fin.cons a u)
  refine ⟨exceptional, hcard, ?_⟩
  intro t ht P hp ha
  have ha' : ((Finset.univ.filter fun i ↦ P.eval (domain i) =
      ∑ j, AffineSpaceGenerator F s t j *
        (Fin.cons a u : Fin (s + 1) → Fin n → F) j i).card : ℝ) ≥
        (k : ℝ) + δ * n := by
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using ha
  obtain ⟨P₀, hdegree, heq, hsets⟩ := hgood t ht P hp ha'
  refine ⟨P₀ 0, fun j ↦ P₀ j.succ, hdegree 0, fun j ↦ hdegree j.succ, ?_, ?_⟩
  · simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using heq
  · intro i
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ, Fin.forall_fin_succ] using hsets i

/-- **MCA error bounds, qualitatively [DKTZ26].** The same gap-only constants work for
every code and every positive affine dimension at distance radius `1 - k / n - δ`.
The line error is at most `C * n ^ (d + 1) / |F|`; passing to affine spaces changes only
the denominator to `|F| - 1`, with no dependence on their dimension. -/
theorem exists_capacity_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / (Fintype.card F : ℝ)) ∧
          ∀ s : ℕ, 1 ≤ s →
            mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / ((Fintype.card F : ℝ) - 1)) := by
  obtain ⟨N, d, C, hC, hall⟩ := exists_capacity_affineAgreement_and_mcaError δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain
  exact ⟨(hall n k hn hk hkn F hchar domain).1,
    fun s hs ↦ ((hall n k hn hk hkn F hchar domain).2 s hs).1⟩

end ReedSolomon
