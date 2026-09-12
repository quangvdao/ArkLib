/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.Powering
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Energy contraction for powers of the Gabber--Galil adjacency operator

The exact Gabber--Galil estimate says that the unnormalized adjacency operator has squared
mean-zero norm at most `50 = (5 * sqrt 2)^2`. This file records the estimate as a proposition and
proves its complete powering consequence. Combined with the executable-walk equality in
`Powering`, this turns every length-`t` label enumeration into normalized squared contraction
by `(25 / 32)^t`.
-/

@[expose] public section

namespace GabberGalil

open scoped BigOperators

/-- Squared Euclidean energy of a real-valued function on the square vertex set. -/
def energy {m : ℕ} [NeZero m] (f : Vertex m → ℝ) : ℝ := ∑ v, f v ^ 2

theorem energy_nonneg {m : ℕ} [NeZero m] (f : Vertex m → ℝ) : 0 ≤ energy f := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Squared form of the exact `5 * sqrt 2` nontrivial-eigenvalue estimate. -/
def ExactEnergyEstimate (m : ℕ) [NeZero m] : Prop :=
  ∀ f : Vertex m → ℝ, f ∈ MeanZero → energy (adjacency f) ≤ 50 * energy f

/-- Every adjacency iterate of a mean-zero function remains mean zero. -/
theorem adjacencyPower_mem_meanZero {m : ℕ} [NeZero m] {f : Vertex m → ℝ}
    (hf : f ∈ MeanZero) (t : ℕ) : adjacencyPower t f ∈ MeanZero := by
  induction t with
  | zero => exact hf
  | succ t ih => exact adjacency_mem_meanZero ih

/-- The exact one-step energy estimate iterates along the executable adjacency recursion. -/
theorem adjacencyPower_energy_le {m : ℕ} [NeZero m] (hGG : ExactEnergyEstimate m)
    {f : Vertex m → ℝ} (hf : f ∈ MeanZero) (t : ℕ) :
    energy (adjacencyPower t f) ≤ (50 : ℝ) ^ t * energy f := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        energy (adjacencyPower (t + 1) f) =
            energy (adjacency (adjacencyPower t f)) := rfl
        _ ≤ 50 * energy (adjacencyPower t f) :=
          hGG _ (adjacencyPower_mem_meanZero hf t)
        _ ≤ 50 * ((50 : ℝ) ^ t * energy f) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (50 : ℝ) ^ (t + 1) * energy f := by rw [pow_succ']; ring

/-- Energy after dividing the length-`t` walk sum by its degree `8^t`. -/
noncomputable def normalizedPoweredEnergy {m : ℕ} [NeZero m]
    (t : ℕ) (f : Vertex m → ℝ) : ℝ :=
  energy (adjacencyPower t f) / (64 : ℝ) ^ t

/-- The exact estimate yields the rational normalized squared contraction `(25/32)^t`. -/
theorem normalizedPoweredEnergy_le {m : ℕ} [NeZero m] (hGG : ExactEnergyEstimate m)
    {f : Vertex m → ℝ} (hf : f ∈ MeanZero) (t : ℕ) :
    normalizedPoweredEnergy t f ≤ ((25 : ℝ) / 32) ^ t * energy f := by
  unfold normalizedPoweredEnergy
  calc
    energy (adjacencyPower t f) / (64 : ℝ) ^ t ≤
        ((50 : ℝ) ^ t * energy f) / (64 : ℝ) ^ t :=
      div_le_div_of_nonneg_right (adjacencyPower_energy_le hGG hf t) (by positivity)
    _ = ((25 : ℝ) / 32) ^ t * energy f := by
      have hratio : (50 : ℝ) * 64⁻¹ = 25 * 32⁻¹ := by norm_num
      rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
      rw [← inv_pow, ← inv_pow]
      calc
        50 ^ t * energy f * 64⁻¹ ^ t = energy f * (50 * 64⁻¹) ^ t := by
          rw [mul_pow]
          ring
        _ = energy f * (25 * 32⁻¹) ^ t := by rw [hratio]
        _ = 25 ^ t * 32⁻¹ ^ t * energy f := by rw [mul_pow]; ring

/-- The normalized squared contraction base is strictly below one. -/
theorem normalizedSquaredBound_lt_one : (25 : ℝ) / 32 < 1 := by norm_num

/-- The powered energy formula applies directly to the executable sum over length-`t` words. -/
theorem executable_walk_energy_le {m : ℕ} [NeZero m] (hGG : ExactEnergyEstimate m)
    {f : Vertex m → ℝ} (hf : f ∈ MeanZero) (t : ℕ) :
    energy (fun v ↦ ((labelWords t).map fun word ↦ f (walk word v)).sum) ≤
      (50 : ℝ) ^ t * energy f := by
  simpa only [← adjacencyPower_apply_words] using adjacencyPower_energy_le hGG hf t

end GabberGalil
