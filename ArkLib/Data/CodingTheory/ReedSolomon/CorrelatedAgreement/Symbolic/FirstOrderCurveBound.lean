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
degrees count candidates after fixing that coordinate. Their two incidence ratios use a
split threshold `L`, between the candidate degree bound `k` and agreement threshold `A`.

These definitions record the rational expression to be evaluated in concrete examples.
This module alone makes no assertion about the cardinality of an exceptional set.
-/

namespace ReedSolomon.HiddenDerivative

/-- Joint degree summed over the order-zero separant stages. -/
def firstOrderCurveJointZero (K μ M ell h : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ),
    (h * (1 + 2 * K * t) + (t + 1) * (ell + 2 * K * h))

/-- Joint degree summed over the order-one separant stages. -/
def firstOrderCurveJointOne (K μ M ell h : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then
      h * (1 + 2 * K * t) ^ 2 + 2 * (t + 1) * (ell + 2 * K * h) * (1 + 2 * K * t)
    else 0

/-- Fiber degree summed over the order-zero stages. -/
def firstOrderCurveFiberZero (μ M : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (μ - min M μ), (t + 1)

/-- Fiber degree summed over the order-one stages. -/
def firstOrderCurveFiberOne (K μ M : ℕ) : ℕ :=
  ∑ t ∈ Finset.range μ,
    if μ - min M μ ≤ t then (t + 1) * (1 + 2 * K * t) else 0

/-- The sharp rational expression for polynomial-curve exceptional challenges.
Its intended geometric range is `k ≤ L ≤ A ≤ n`, with positive interpolation parameters. -/
def firstOrderCurveBound (n K k L A μ M ell h : ℕ) : ℚ :=
  let l₁ : ℚ := ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)
  let l₂ : ℚ := ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)
  h + l₁ * firstOrderCurveJointZero K μ M ell h +
    l₁ ^ 2 * firstOrderCurveJointOne K μ M ell h +
    ((ell * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberZero μ M + l₂ * firstOrderCurveFiberOne K μ M)

end ReedSolomon.HiddenDerivative
