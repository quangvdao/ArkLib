/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Band


/-!
# Exact finite height sums for polynomial received curves

For a received curve of degree at most `ℓ`, a source monomial with `Y₀` exponent `a`
has challenge-column degree at most `ℓ * a`. Reindexing the full first-order support
by total jet degree `t` and first-derivative exponent `b` gives `a = t - b`.
The resulting executable sum counts every permitted scalar coefficient, including
inactive columns through natural-number truncated subtraction.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {D A m M μ ℓ h : ℕ}

/-- Total number of polynomial coefficient slots allowed by height `h` across the actual finite
first-order support. -/
def firstOrderCurveColumnSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ h + 1 - ℓ * u (some 0)

/-- Executable nested sum for the first-order column-height slot count. -/
def firstOrderCurveHeightSlotCount (D A m M μ ℓ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - ℓ * (t - b))

/-- The dependent `(t,b,x)` index has the expected weighted cardinality, where every `x` at a
fixed `(t,b)` contributes the same number of height slots. -/
theorem sum_firstOrderDimensionIndex_curveHeight (D A m M μ ℓ h : ℕ) :
    (Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
        h + 1 - ℓ * (q.1.val - q.2.1.val)) =
      firstOrderCurveHeightSlotCount D A m M μ ℓ h := by
  rw [Fintype.sum_sigma]
  calc
    (Finset.univ.sum fun t : Fin (μ + 1) ↦
        Finset.univ.sum fun q : (Σ b : Fin (min t.val M + 1),
          Fin (m * A + b.val - D * t.val)) ↦
          h + 1 - ℓ * (t.val - q.1.val)) =
        Finset.univ.sum fun t : Fin (μ + 1) ↦
          Finset.univ.sum fun b : Fin (min t.val M + 1) ↦
            (m * A + b.val - D * t.val) * (h + 1 - ℓ * (t.val - b.val)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.univ.sum fun b : Fin (min t M + 1) ↦
            (m * A + b.val - D * t) * (h + 1 - ℓ * (t - b.val)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun t ↦ Finset.univ.sum fun b : Fin (min t M + 1) ↦
          (m * A + b.val - D * t) * (h + 1 - ℓ * (t - b.val))) (μ + 1)
    _ = Finset.sum (Finset.range (μ + 1)) fun t ↦
          Finset.sum (Finset.range (min t M + 1)) fun b ↦
            (m * A + b - D * t) * (h + 1 - ℓ * (t - b)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Fin.sum_univ_eq_sum_range
        (fun b ↦ (m * A + b - D * t) * (h + 1 - ℓ * (t - b))) (min t M + 1)
    _ = firstOrderCurveHeightSlotCount D A m M μ ℓ h := rfl

/-- The support-side column-slot sum is exactly the executable nested height sum. -/
theorem firstOrderCurveColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderCurveColumnSlotCount D A m M μ ℓ h =
      firstOrderCurveHeightSlotCount D A m M μ ℓ h := by
  rw [firstOrderCurveColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderExponentDimensionIndexEquiv
    (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    (Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
        h + 1 - ℓ * u.1 (some 0)) =
        Finset.univ.sum fun q : FirstOrderDimensionIndex D A m M μ ↦
          h + 1 - ℓ * (q.1.val - q.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      rw [firstOrderExponentDimensionIndex_y₀ hD]
    _ = firstOrderCurveHeightSlotCount D A m M μ ℓ h :=
      sum_firstOrderDimensionIndex_curveHeight D A m M μ ℓ h


end

end ReedSolomon.HiddenDerivative
