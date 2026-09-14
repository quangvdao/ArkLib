/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FixedRateGate

/-! # Complete list bound from the explicit fixed-rate factor-six gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- Complete lists at a fixed rate `R` and positive gap `δ` from capacity.

We use agreement `R + δ` and the explicit derivative order
`d = ceil(max(500, (20/(27*R)) * exp(R*log(40/(9*R))/δ)))`.
The selected multiplicity and length threshold depend only on `R` and `δ`, not on the field,
evaluation points, or received word. For every code of rate at most `R` above that length,
the complete set of degree-`< k` polynomials with at least `A` agreements is finite and has
size at most `B^2 * (2*B/δ)^d * n^d`, where `B` is the selected jet-degree bound.

The field may be infinite. Its characteristic must be zero or exceed `max(k-1, d, B)`.
Finiteness is a separate conclusion: the numerical `Set.ncard` bound alone would not rule out
an infinite list. This is the selected-parameter form of the paper's fixed-rate corollary;
`fixedRatePartitionOrder_list_bound` hides the particular parameter choice. -/
theorem fixedRatePartitionOrder_list_bound_selected {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    -- Choose the interpolation parameters before the field and code.
    let p := fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- The code has rate at most R; A is an integer agreement count, not a fraction.
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      -- Injectivity of domain supplies distinct evaluation points; this guard is on
      -- characteristic, not field cardinality.
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      -- Bound the full agreement list, not a chosen subset of candidates.
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / δ) ^
              fixedRatePartitionOrder R δ *
            n ^ fixedRatePartitionOrder R δ := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain received hchar
  simpa only [add_sub_cancel_left] using ratePartition_close_list_bound
    (fixedRatePartitionFiniteParameters hR hδ) hR (by linarith : R < R + δ) haone
      (fixedRatePartitionOrder_ge_500 R δ) hn hk hkR haA hAn domain received hchar

open Classical in
/-- At a fixed positive rate and margin, the explicit factor-six derivative order admits a
terminating search for the finite interpolation multiplicity and hence bounds every complete
close-polynomial list.

The order is the fixed explicit value `fixedRatePartitionOrder R δ`; the existential quantifier
chooses only interpolation parameters for the already fixed `R` and `δ`.  Thus this is distinct
from the eventual-small-gap theorem built from `ratePartition_fixedRate_eventually`, whose order of
quantifiers is `∃ δ₀, ∀ δ < δ₀`.  No 300-based closed multiplicity is asserted at this
minimal cutoff. -/
theorem fixedRatePartitionOrder_list_bound {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    -- Choose finite interpolation data from the fixed rate and gap before the field and code.
    ∃ p : RatePartitionFiniteParameters R (R + δ) (fixedRatePartitionOrder R δ),
      -- The field may be infinite; only the later characteristic guard restricts it.
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- The code is long enough, has rate at most `R`, and uses agreement at least `(R + δ)n`.
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      -- Characteristic zero or above the message/order/jet thresholds is allowed.
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      -- The complete degree-`< k` list is finite before its `Set.ncard` is bounded.
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / δ) ^
              fixedRatePartitionOrder R δ *
            n ^ fixedRatePartitionOrder R δ := by
  exact ⟨fixedRatePartitionFiniteParameters hR hδ,
    fixedRatePartitionOrder_list_bound_selected hR hδ haone⟩

end ReedSolomon
