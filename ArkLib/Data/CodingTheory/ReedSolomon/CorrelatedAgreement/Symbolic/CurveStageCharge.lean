/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderCurveBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparing the two regular-stage charges

Order-zero and order-one stages have different geometric dimensions. Their charges are
monotone in the total jet-degree cap, and an order-one stage costs at least the corresponding
order-zero stage. These facts let separant descent retain the first-derivative cap when
summing costs: only the highest `M` degree slots need the order-one charge.

The parameters `s` and `t` represent the joint and fiber incidence ratios. The parameter `c`
is the common factor `ell * (n - L)` for accidental agreements. This module proves only
algebraic comparisons of those charges; the geometric cardinality theorem supplies them.
-/

namespace ReedSolomon.HiddenDerivative

/-- Joint and accidental-agreement charge for one order-zero stage. -/
def curveStageZero (K ell h : ℕ) (s c : ℚ) (v : ℕ) : ℚ :=
  s * ((h * (1 + 2 * K * (v - 1)) + v * (ell + 2 * K * h) : ℕ) : ℚ) + c * v

/-- Joint and accidental-agreement charge for one order-one stage. -/
def curveStageOne (K ell h : ℕ) (s t c : ℚ) (v : ℕ) : ℚ :=
  s ^ 2 * ((h * (1 + 2 * K * (v - 1)) ^ 2 +
    2 * v * (ell + 2 * K * h) * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) +
    c * t * ((v * (1 + 2 * K * (v - 1)) : ℕ) : ℚ)

/-- Nonnegative incidence ratios give nonnegative order-zero charges. -/
theorem curveStageZero_nonneg (K ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (v : ℕ) : 0 ≤ curveStageZero K ell h s c v := by
  unfold curveStageZero
  positivity

/-- Nonnegative fiber factors give nonnegative order-one charges. -/
theorem curveStageOne_nonneg (K ell h : ℕ) {s t c : ℚ} (ht : 0 ≤ t) (hc : 0 ≤ c)
    (v : ℕ) : 0 ≤ curveStageOne K ell h s t c v := by
  unfold curveStageOne
  positivity

/-- Enlarging the jet cap can only increase the order-zero charge. -/
theorem curveStageZero_mono (K ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    Monotone (curveStageZero K ell h s c) := by
  intro v w hvw
  unfold curveStageZero
  gcongr

/-- Enlarging the jet cap can only increase the order-one charge. -/
theorem curveStageOne_mono (K ell h : ℕ) {s t c : ℚ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Monotone (curveStageOne K ell h s t c) := by
  intro v w hvw
  unfold curveStageOne
  gcongr

/-- At incidence ratios at least one, order one dominates order zero at every degree. -/
theorem curveStageZero_le_one (K ell h : ℕ) {s t c : ℚ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : 0 ≤ c) (v : ℕ) :
    curveStageZero K ell h s c v ≤ curveStageOne K ell h s t c v := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hb : 1 ≤ 1 + 2 * K * (v - 1) := by omega
  have hb2 : 1 + 2 * K * (v - 1) ≤ (1 + 2 * K * (v - 1)) ^ 2 := by nlinarith
  have hvb : v ≤ v * (1 + 2 * K * (v - 1)) := by nlinarith
  have hjoint : h * (1 + 2 * K * (v - 1)) + v * (ell + 2 * K * h) ≤
      h * (1 + 2 * K * (v - 1)) ^ 2 +
        2 * v * (ell + 2 * K * h) * (1 + 2 * K * (v - 1)) := by
    apply add_le_add (Nat.mul_le_mul_left h hb2)
    calc
      v * (ell + 2 * K * h) ≤ v * (ell + 2 * K * h) *
          (1 + 2 * K * (v - 1)) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ 2 * (v * (ell + 2 * K * h) * (1 + 2 * K * (v - 1))) :=
        Nat.le_mul_of_pos_left _ (by decide)
      _ = 2 * v * (ell + 2 * K * h) * (1 + 2 * K * (v - 1)) := by ring
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hct : c ≤ c * t := by nlinarith
  unfold curveStageZero curveStageOne
  apply add_le_add
  · exact mul_le_mul hs2 (by exact_mod_cast hjoint) (by positivity) (sq_nonneg s)
  · exact mul_le_mul hct (by exact_mod_cast hvb) (by positivity) (mul_nonneg hc ht0)

end ReedSolomon.HiddenDerivative
