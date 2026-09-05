/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexCantelli
import Mathlib.Tactic.FinCases

/-! # Boundary regression tests -/

noncomputable section

namespace ReedSolomon.HiddenDerivative

open DiscreteSimplex
open scoped BigOperators

/-- Unequal margins `4` and `3` give positive mass although the upper Chebyshev loss
`10 / 3²` alone exceeds one. -/
example : (242 / 247 : ℝ) ≤ (asymmetricBandTuples 2 10 0 8).card := by
  have h := asymmetricBand_card_lower_of_simplex_cantelli
    (d := 2) (W := 10) (Cmin := 0) (Cmax := 8) 4 3 (by norm_num) (by norm_num)
  simp only [show 2 - 1 = 1 from rfl, card_ordinarySimplex, Nat.choose_one_right] at h
  norm_num [simplexWeightedMean, simplexWeightedVariance, simplexReciprocalWeights,
    Fin.sum_univ_succ] at h
  exact h

/-- Zero budget has zero variance and every positive upper-tail subset is empty. -/
example (w : Fin 3 → ℝ) (tail : Finset (OrdinarySimplex 3 0))
    (hTail : ∀ u ∈ tail,
      1 ≤ simplexWeightedStatistic w u - simplexWeightedMean 0 w) : tail.card = 0 := by
  have h := simplex_cantelli_tail_count w 1 (by norm_num) 1 (by norm_num) tail
    (fun u hu ↦ by simpa only [one_mul] using hTail u hu)
  simp only [simplexWeightedVariance, Nat.cast_zero, zero_mul, zero_div, zero_add,
    one_pow, mul_zero] at h
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast h)

end ReedSolomon.HiddenDerivative
