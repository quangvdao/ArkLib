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

The parameters `s`, `η`, and `t` represent the split joint, direct joint, and fiber incidence
ratios. The parameter `c` is the common factor `ell * (n - L)` for accidental agreements.
This module proves only algebraic comparisons of those charges; the geometric cardinality
theorem supplies them.
-/

namespace ReedSolomon.HiddenDerivative

/-- Joint and accidental-agreement charge for one order-zero stage. -/
def curveStageZero (K ell h : ℕ) (s c : ℚ) (v : ℕ) (τ : ℕ := 2 * K) : ℚ :=
  s * ((h * (1 + τ * (v - 1)) + v * (ell + τ * h) : ℕ) : ℚ) + c * v

/-- Joint and accidental-agreement charge for one order-one stage. The direct joint ratio `η`
is independent of the split joint ratio `s`. Its default `s` preserves the coarse legacy charge
for callers that have not yet migrated to the dimension-sensitive incidence theorem. -/
def curveStageOne (K ell h : ℕ) (s t c : ℚ) (v : ℕ) (τ : ℕ := 2 * K)
    (η : ℚ := s) : ℚ :=
  s * η * ((h * (1 + τ * (v - 1)) ^ 2 +
    2 * v * (ell + τ * h) * (1 + τ * (v - 1)) : ℕ) : ℚ) +
    c * t * ((v * (1 + τ * (v - 1)) : ℕ) : ℚ)

/-- Nonnegative incidence ratios give nonnegative order-zero charges. -/
theorem curveStageZero_nonneg (K ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (v : ℕ) (τ : ℕ := 2 * K) : 0 ≤ curveStageZero K ell h s c v τ := by
  unfold curveStageZero
  positivity

/-- Nonnegative incidence factors give nonnegative order-one charges. -/
theorem curveStageOne_nonneg_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (v τ : ℕ) : 0 ≤ curveStageOne K ell h s t c v τ η := by
  unfold curveStageOne
  positivity

/-- The former square-factor order-one charge remains nonnegative. -/
theorem curveStageOne_nonneg (K ell h : ℕ) {s t c : ℚ} (ht : 0 ≤ t) (hc : 0 ≤ c)
    (v : ℕ) : 0 ≤ curveStageOne K ell h s t c v := by
  unfold curveStageOne
  exact add_nonneg (mul_nonneg (mul_self_nonneg s) (by positivity))
    (mul_nonneg (mul_nonneg hc ht) (by positivity))

/-- Enlarging the jet cap can only increase the order-zero charge at any common exponent. -/
theorem curveStageZero_mono_of_exponent (K ell h : ℕ) {s c : ℚ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (τ : ℕ) :
    Monotone fun v ↦ curveStageZero K ell h s c v (τ := τ) := by
  intro v w hvw
  have hsub : v - 1 ≤ w - 1 := Nat.sub_le_sub_right hvw 1
  have hb : 1 + τ * (v - 1) ≤ 1 + τ * (w - 1) := by gcongr
  have hjoint : h * (1 + τ * (v - 1)) + v * (ell + τ * h) ≤
      h * (1 + τ * (w - 1)) + w * (ell + τ * h) := by gcongr
  unfold curveStageZero
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) hs
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hvw) hc

/-- Compatibility form at the former coarse exponent. -/
theorem curveStageZero_mono (K ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    Monotone fun v ↦ curveStageZero K ell h s c v :=
  curveStageZero_mono_of_exponent K ell h hs hc (2 * K)

/-- Enlarging the jet cap can only increase the order-one charge. -/
theorem curveStageOne_mono_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c) (τ : ℕ) :
    Monotone fun v ↦ curveStageOne K ell h s t c v τ η := by
  intro v w hvw
  have hsub : v - 1 ≤ w - 1 := Nat.sub_le_sub_right hvw 1
  have hb : 1 + τ * (v - 1) ≤ 1 + τ * (w - 1) := by gcongr
  have hjoint : h * (1 + τ * (v - 1)) ^ 2 +
      2 * v * (ell + τ * h) * (1 + τ * (v - 1)) ≤
      h * (1 + τ * (w - 1)) ^ 2 +
        2 * w * (ell + τ * h) * (1 + τ * (w - 1)) := by gcongr
  have hfiber : v * (1 + τ * (v - 1)) ≤ w * (1 + τ * (w - 1)) := by gcongr
  unfold curveStageOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) (mul_nonneg hs hη)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfiber) (mul_nonneg hc ht)

/-- The former square-factor order-one charge is monotone. -/
theorem curveStageOne_mono (K ell h : ℕ) {s t c : ℚ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    Monotone fun v ↦ curveStageOne K ell h s t c v := by
  intro v w hvw
  have hsub : v - 1 ≤ w - 1 := Nat.sub_le_sub_right hvw 1
  have hb : 1 + 2 * K * (v - 1) ≤ 1 + 2 * K * (w - 1) := by gcongr
  have hjoint : h * (1 + 2 * K * (v - 1)) ^ 2 +
      2 * v * (ell + 2 * K * h) * (1 + 2 * K * (v - 1)) ≤
      h * (1 + 2 * K * (w - 1)) ^ 2 +
        2 * w * (ell + 2 * K * h) * (1 + 2 * K * (w - 1)) := by gcongr
  have hfiber : v * (1 + 2 * K * (v - 1)) ≤
      w * (1 + 2 * K * (w - 1)) := by gcongr
  unfold curveStageOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) (mul_self_nonneg s)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfiber) (mul_nonneg hc ht)

/-- At incidence ratios at least one, order one dominates order zero at every degree. -/
theorem curveStageZero_le_one_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 1 ≤ s) (hη : 1 ≤ η) (ht : 1 ≤ t) (hc : 0 ≤ c) (v τ : ℕ) :
    curveStageZero K ell h s c v τ ≤ curveStageOne K ell h s t c v τ η := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hη0 : 0 ≤ η := le_trans (by norm_num) hη
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hb : 1 ≤ 1 + τ * (v - 1) := by omega
  have hb2 : 1 + τ * (v - 1) ≤ (1 + τ * (v - 1)) ^ 2 := by nlinarith
  have hvb : v ≤ v * (1 + τ * (v - 1)) := by nlinarith
  have hjoint : h * (1 + τ * (v - 1)) + v * (ell + τ * h) ≤
      h * (1 + τ * (v - 1)) ^ 2 +
        2 * v * (ell + τ * h) * (1 + τ * (v - 1)) := by
    apply add_le_add (Nat.mul_le_mul_left h hb2)
    calc
      v * (ell + τ * h) ≤ v * (ell + τ * h) *
          (1 + τ * (v - 1)) := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ 2 * (v * (ell + τ * h) * (1 + τ * (v - 1))) :=
        Nat.le_mul_of_pos_left _ (by decide)
      _ = 2 * v * (ell + τ * h) * (1 + τ * (v - 1)) := by ring
  have hsη : s ≤ s * η := by nlinarith
  have hct : c ≤ c * t := by nlinarith
  unfold curveStageZero curveStageOne
  apply add_le_add
  · exact mul_le_mul hsη (by exact_mod_cast hjoint) (by positivity) (mul_nonneg hs0 hη0)
  · exact mul_le_mul hct (by exact_mod_cast hvb) (by positivity) (mul_nonneg hc ht0)

/-- Compatibility form where the direct joint ratio is the split joint ratio. -/
theorem curveStageZero_le_one (K ell h : ℕ) {s t c : ℚ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : 0 ≤ c) (v : ℕ) :
    curveStageZero K ell h s c v ≤ curveStageOne K ell h s t c v := by
  exact curveStageZero_le_one_of_factors K ell h hs hs ht hc v (2 * K)

end ReedSolomon.HiddenDerivative
