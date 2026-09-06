/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The finite first-order curve envelope

The first-derivative cap separates the differential equation's successive separant stages
into two groups. The last `min M μ` stages have order one; the remaining stages have order
zero. Keeping those groups separate preserves the linear and quadratic geometric costs.

The joint degrees count components while retaining the challenge coordinate. The fiber
degrees count candidates after fixing that coordinate. Their incidence ratios use a split
threshold `L`, between the candidate degree bound `k` and agreement threshold `A`. The
order-one joint count also uses the independent ratio from `k` directly to `A`.

These definitions record the rational expression to be evaluated in concrete examples.
This module alone makes no assertion about the cardinality of an exceptional set.
-/

namespace ReedSolomon.HiddenDerivative

/-- Joint degree summed over the order-zero separant stages at common denominator exponent
`τ`. -/
def firstOrderCurveJointZero (_K μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ),
    (h * (1 + τ * t) + (t + 1) * (ell + τ * h))

/-- Joint degree summed over the order-one separant stages, using the same denominator exponent
as the order-zero stages. -/
def firstOrderCurveJointOne (_K μ M ell h τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      h * (1 + τ * t) ^ 2 + 2 * (t + 1) * (ell + τ * h) * (1 + τ * t)
    else 0

/-- Fiber degree summed over the order-zero stages. -/
def firstOrderCurveFiberZero (μ M : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ), (t + 1)

/-- Fiber degree summed over the order-one stages. -/
def firstOrderCurveFiberOne (_K μ M τ : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then (t + 1) * (1 + τ * t) else 0

/-- The rational expression for polynomial-curve exceptional challenges. The common Taylor
exponent and direct order-one joint factor are explicit parameters. -/
def firstOrderCurveBound (n K k L A μ M ell h τ : ℕ) (η : ℚ) : ℚ :=
  let l₁ : ℚ := ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)
  let l₂ : ℚ := ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)
  h + l₁ * firstOrderCurveJointZero K μ M ell h τ +
    l₁ * η * firstOrderCurveJointOne K μ M ell h τ +
    ((ell * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberZero μ M + l₂ * firstOrderCurveFiberOne K μ M τ)

/-- The first-order curve envelope is monotone in its direct joint-incidence factor. -/
theorem firstOrderCurveBound_mono_directFactor
    (n K k L A μ M ell h τ : ℕ) :
    Monotone fun η : ℚ ↦ firstOrderCurveBound n K k L A μ M ell h (τ := τ) (η := η) := by
  intro η η' hη
  have hl₁ : (0 : ℚ) ≤ ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hJ : (0 : ℚ) ≤ firstOrderCurveJointOne K μ M ell h (τ := τ) := by
    exact_mod_cast Nat.zero_le (firstOrderCurveJointOne K μ M ell h (τ := τ))
  have hmiddle :
      (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) * η *
          firstOrderCurveJointOne K μ M ell h (τ := τ) ≤
        (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) * η' *
          firstOrderCurveJointOne K μ M ell h (τ := τ) := by
    calc
      _ = (↑(firstOrderCurveJointOne K μ M ell h (τ := τ)) *
          (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ))) * η := by ac_rfl
      _ ≤ (↑(firstOrderCurveJointOne K μ M ell h (τ := τ)) *
          (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ))) * η' :=
        mul_le_mul_of_nonneg_left hη (mul_nonneg hJ hl₁)
      _ = _ := by ac_rfl
  unfold firstOrderCurveBound
  dsimp only
  simpa only [add_assoc, add_comm, add_left_comm] using
    (add_le_add_right (add_le_add_left hmiddle
      ((h : ℚ) + (((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)) *
        firstOrderCurveJointZero K μ M ell h (τ := τ)))
      (((ell * (n - L) : ℕ) : ℚ) *
        (firstOrderCurveFiberZero μ M +
          (((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)) *
            firstOrderCurveFiberOne K μ M (τ := τ))))

end ReedSolomon.HiddenDerivative
