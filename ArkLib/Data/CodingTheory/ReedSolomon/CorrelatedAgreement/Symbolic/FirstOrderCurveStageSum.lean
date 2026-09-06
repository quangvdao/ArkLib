/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.CurveStageCharge
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.FirstOrderStageSum

/-!
# Summing first-order polynomial-curve stage charges

The geometric cost of a regular separant stage depends on its actual total jet degree and on
whether its highest active jet has order zero or one. The first-derivative exponent cap limits
the expensive order-one stages. Combining the generic cap-sensitive chain sum with the concrete
joint-and-fiber charges gives exactly the nonterminal part of `firstOrderCurveBound`.

## Reading the statement

The inequalities `k ≤ L ≤ A ≤ n` place the split threshold between message degree and received
agreement. They make both incidence ratios at least one. For every actual symbolic separant chain
whose initial equation has total jet degree at most `μ` and first-derivative degree at most `M`,
the terminal height charge plus all regular-stage charges is bounded by the displayed curve
envelope. No exceptional-set or root-counting premise is assumed here.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial SymbolicSeparantChain
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The joint incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveJointRatio (n L A : ℕ) : ℚ :=
  ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ)

/-- The fiber incidence ratio used by the first-order curve envelope. -/
def firstOrderCurveFiberRatio (n k L : ℕ) : ℚ :=
  ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ)

/-- The actual regular-stage charge whose sum appears in the curve envelope. -/
def firstOrderCurveStageCharge (n K k L A ell h : ℕ) : Stage F[X] 1 → ℚ :=
  firstOrderStageCharge
    (curveStageZero K ell h (firstOrderCurveJointRatio n L A)
      ((ell * (n - L) : ℕ) : ℚ))
    (curveStageOne K ell h (firstOrderCurveJointRatio n L A)
      (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ))

private theorem sum_Ico_eq_sum_range_ite {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) {a μ : ℕ} (_ha : a ≤ μ) :
    ∑ t ∈ Finset.Ico a μ, f t = ∑ t ∈ Finset.range μ, if a ≤ t then f t else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  · intro t _
    rfl

private theorem sum_curveStageZero_eq (K μ M ell h : ℕ) (s c : ℚ) :
    (∑ t ∈ Finset.range (μ - min M μ), curveStageZero K ell h s c (t + 1)) =
      s * firstOrderCurveJointZero K μ M ell h +
        c * firstOrderCurveFiberZero μ M := by
  unfold curveStageZero firstOrderCurveJointZero firstOrderCurveFiberZero
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  rfl

private theorem sum_curveStageOne_eq (K μ M ell h : ℕ) (s t c : ℚ) :
    (∑ j ∈ Finset.Ico (μ - min M μ) μ, curveStageOne K ell h s t c (j + 1)) =
      s ^ 2 * firstOrderCurveJointOne K μ M ell h +
        c * t * firstOrderCurveFiberOne K μ M := by
  rw [sum_Ico_eq_sum_range_ite _ (Nat.sub_le μ (min M μ))]
  unfold curveStageOne firstOrderCurveJointOne firstOrderCurveFiberOne
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : μ - min M μ ≤ j
  · simp [hj]
  · simp [hj]

private theorem firstOrderCurveStageCap_add_height_eq (n K k L A μ M ell h : ℕ) :
    (h : ℚ) + firstOrderStageCap
        (curveStageZero K ell h (firstOrderCurveJointRatio n L A)
          ((ell * (n - L) : ℕ) : ℚ))
        (curveStageOne K ell h (firstOrderCurveJointRatio n L A)
          (firstOrderCurveFiberRatio n k L) ((ell * (n - L) : ℕ) : ℚ)) μ M =
      firstOrderCurveBound n K k L A μ M ell h := by
  rw [firstOrderStageCap, sum_curveStageZero_eq, sum_curveStageOne_eq]
  unfold firstOrderCurveBound firstOrderCurveJointRatio firstOrderCurveFiberRatio
  ring

/-- Terminal height plus all actual regular-stage charges is at most the sharp first-order
polynomial-curve envelope. -/
theorem SymbolicSeparantChain.Chain.sum_firstOrderCurveStageCharge_add_height_le
    {Q terminal : DifferentialPolynomial F[X] 1} {stages : List (Stage F[X] 1)}
    (hc : Chain Q stages terminal) {n K k L A μ M ell h : ℕ}
    (hμ : jetWeight Q ≤ μ) (hM : jetDegree Q 1 ≤ M)
    (_hk : 0 < k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (h : ℚ) + (stages.map (firstOrderCurveStageCharge n K k L A ell h)).sum ≤
      firstOrderCurveBound n K k L A μ M ell h := by
  let s := firstOrderCurveJointRatio n L A
  let t := firstOrderCurveFiberRatio n k L
  let c : ℚ := ((ell * (n - L) : ℕ) : ℚ)
  have hs : 1 ≤ s := by
    unfold s firstOrderCurveJointRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((A - L + 1 : ℕ) : ℚ) ≤ (n - L + 1 : ℕ) by exact_mod_cast (by omega))
  have ht : 1 ≤ t := by
    unfold t firstOrderCurveFiberRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((L - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))
  have hs0 : 0 ≤ s := (by positivity)
  have ht0 : 0 ≤ t := (by positivity)
  have hc0 : 0 ≤ c := by positivity
  have hsum := hc.sum_firstOrderStageCharge_le
    (curveStageZero K ell h s c) (curveStageOne K ell h s t c)
    hμ hM (curveStageZero_nonneg K ell h hs0 hc0)
    (curveStageOne_nonneg K ell h ht0 hc0)
    (curveStageZero_mono K ell h hs0 hc0)
    (curveStageOne_mono K ell h ht0 hc0)
    (curveStageZero_le_one K ell h hs ht hc0)
  change (h : ℚ) + (stages.map (firstOrderStageCharge
    (curveStageZero K ell h s c) (curveStageOne K ell h s t c))).sum ≤ _
  calc
    (h : ℚ) + (stages.map (firstOrderStageCharge
        (curveStageZero K ell h s c) (curveStageOne K ell h s t c))).sum ≤
        (h : ℚ) + firstOrderStageCap (curveStageZero K ell h s c)
          (curveStageOne K ell h s t c) μ M := by
            simpa [add_comm] using add_le_add_left hsum (h : ℚ)
    _ = firstOrderCurveBound n K k L A μ M ell h := by
      exact firstOrderCurveStageCap_add_height_eq n K k L A μ M ell h

end

end ReedSolomon.HiddenDerivative
