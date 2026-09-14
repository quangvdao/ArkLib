/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FixedRateGate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition

/-! # Exact line MCA from the explicit fixed-rate factor-six gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

open Classical in
/-- Line MCA at a fixed rate `R` and positive gap `δ` from capacity.

Use the same derivative order and selected interpolation parameters as
`fixedRatePartitionOrder` and the fixed-rate list bound: agreement is `R + δ`, and
`d = ceil(max(500, (20/(27*R)) * exp(R*log(40/(9*R))/δ)))`.
For each pair of received words, one exceptional set of at most `C * n^(d+1)` challenges
works for every close polynomial. The constant `C` and length threshold depend only on
`R` and `δ`; the displayed formula computes `C` from the selected jet and height bounds.

Outside that set, `HasExactCorrelatedPair` supplies degree-`< k` polynomials for the two
received words. Their linear combination is the candidate, and their common agreement set
equals its full agreement set. The witnesses may depend on the challenge and candidate;
the exceptional set may not. The field need not be finite, and its characteristic must be
zero or exceed `max(k-1, d, B)`, where `B` is the selected jet-degree bound. -/
theorem fixedRatePartitionOrder_lineMCA {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (haone : R + δ < 1) :
    -- Fix the quantitative choices before the field, code, and received words.
    let p := fixedRatePartitionFiniteParameters hR hδ
    ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- The code is long enough, has rate at most `R`, and realizes agreement between
      -- `(R + δ)n` and `n`.
      ratePartitionMathematicalLength R (fixedRatePartitionOrder R δ) p.multiplicity ≤ n →
      0 < k →
      (k : ℝ) ≤ R * n → (R + δ) * n ≤ A → A ≤ n →
      -- domain is injective; f and g determine the received line f + z*g.
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
      -- Characteristic zero or above the message/order/jet thresholds is allowed;
      -- field size is unrestricted.
      (ringChar F = 0 ∨ max (max (k - 1) (fixedRatePartitionOrder R δ))
        (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      -- One set is chosen before either the challenge z or the candidate P.
      ∃ exceptional : Finset F,
        -- The coefficient comes from the selected jet and finite-ratio height; the exponent is d+1.
        (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
          (ratePartitionJetBound R p.multiplicity)
          (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
            (ratePartitionFiniteRatio R (R + δ) (fixedRatePartitionOrder R δ)
              p.multiplicity))
          (fixedRatePartitionOrder R δ) * (n : ℝ) ^ (fixedRatePartitionOrder R δ + 1) ∧
        -- The conclusion concerns the candidate's full agreement set, not a subset.
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  intro F _ n k A hn hk hkR haA hAn domain f g hchar
  simpa only [add_sub_cancel_left] using exists_ratePartition_lineMCA
    (fixedRatePartitionFiniteParameters hR hδ) hR (by linarith : R < R + δ) haone
      (fixedRatePartitionOrder_ge_500 R δ) hn hk hkR haA hAn domain f g hchar

end ReedSolomon
