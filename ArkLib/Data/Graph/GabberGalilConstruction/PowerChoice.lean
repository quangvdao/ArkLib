/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.SpectralMixing
public import Mathlib.Tactic.NormNum

/-!
# Executable power choice for Gabber--Galil mixing

This file searches a finite interval for the first power satisfying the integer form of the
normalized mixing inequality. A concrete quadratic upper bound proves that the search always
succeeds for positive graph size and threshold.
-/

@[expose] public section

namespace GabberGalil

/-- A uniform quadratic search bound for normalized mixing. -/
def mixingPowerBound (N : ℕ) : ℕ := 4 * N ^ 2

/-- At the search bound, the normalized contraction is below every positive threshold square. -/
theorem mixingPowerBound_numeric (N threshold : ℕ) (hN : 0 < N) (hthreshold : 0 < threshold) :
    ((25 : ℝ) / 32) ^ mixingPowerBound N * (N : ℝ) ^ 2 < (threshold : ℝ) ^ 2 := by
  let s := N ^ 2
  have hs : 0 < s := by positivity
  have hbase : ((25 : ℝ) / 32) ^ 4 < (1 / 2 : ℝ) := by norm_num
  have hpowers : (((25 : ℝ) / 32) ^ 4) ^ s < ((1 / 2 : ℝ)) ^ s :=
    pow_lt_pow_left₀ hbase (by positivity) hs.ne'
  have hnat : s < 2 ^ s := s.lt_two_pow_self
  have hcast : (s : ℝ) < (2 : ℝ) ^ s := by exact_mod_cast hnat
  have hhalfpos : 0 < ((1 / 2 : ℝ)) ^ s := by positivity
  have hhalf : ((1 / 2 : ℝ)) ^ s * s < 1 := by
    have hmul := mul_lt_mul_of_pos_left hcast hhalfpos
    calc
      ((1 / 2 : ℝ)) ^ s * s < ((1 / 2 : ℝ)) ^ s * (2 : ℝ) ^ s := hmul
      _ = 1 := by rw [← mul_pow]; norm_num
  have hratio : ((25 : ℝ) / 32) ^ mixingPowerBound N =
      (((25 : ℝ) / 32) ^ 4) ^ s := by
    simp only [mixingPowerBound, s, pow_mul]
  have hsCast : (s : ℝ) = (N : ℝ) ^ 2 := by norm_num [s]
  have hsmall : ((25 : ℝ) / 32) ^ mixingPowerBound N * (N : ℝ) ^ 2 < 1 := by
    rw [hratio, ← hsCast]
    exact (mul_lt_mul_of_pos_right hpowers (by positivity)).trans hhalf
  have hthresholdReal : (1 : ℝ) ≤ threshold := by exact_mod_cast hthreshold
  exact hsmall.trans_le (one_le_pow₀ hthresholdReal)

/-- Executable integer form of the normalized mixing inequality. -/
def mixingPowerCondition (N threshold t : ℕ) : Bool :=
  decide (25 ^ t * N ^ 2 < 32 ^ t * threshold ^ 2)

/-- The integer test is equivalent to the real-valued normalized inequality. -/
theorem mixingPowerCondition_iff (N threshold t : ℕ) :
    mixingPowerCondition N threshold t ↔
      ((25 : ℝ) / 32) ^ t * (N : ℝ) ^ 2 < (threshold : ℝ) ^ 2 := by
  simp only [mixingPowerCondition, decide_eq_true_eq]
  rw [div_pow]
  have h32 : (0 : ℝ) < (32 : ℝ) ^ t := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ h32]
  norm_cast
  simp only [mul_comm]
/-- Search the finite interval through `mixingPowerBound` for its first successful power. -/
def firstMixingPower (N threshold : ℕ) : ℕ :=
  let bound := mixingPowerBound N
  match Fin.find? (fun t : Fin (bound + 1) => mixingPowerCondition N threshold t) with
  | some t => t
  | none => bound

/-- The executable first power always satisfies the normalized inequality for positive inputs. -/
theorem firstMixingPower_spec (N threshold : ℕ) (hN : 0 < N) (hthreshold : 0 < threshold) :
    ((25 : ℝ) / 32) ^ firstMixingPower N threshold * (N : ℝ) ^ 2 <
      (threshold : ℝ) ^ 2 := by
  let bound := mixingPowerBound N
  let candidate : Fin (bound + 1) := ⟨bound, Nat.lt_succ_self bound⟩
  have hboundReal := mixingPowerBound_numeric N threshold hN hthreshold
  have hboundBool : mixingPowerCondition N threshold candidate = true := by
    rw [mixingPowerCondition_iff]
    exact hboundReal
  have hsome : (Fin.find? (fun t : Fin (bound + 1) =>
      mixingPowerCondition N threshold t)).isSome :=
    Fin.isSome_find?_of_eq_true hboundBool
  cases hfind : Fin.find? (fun t : Fin (bound + 1) =>
      mixingPowerCondition N threshold t) with
  | none => simp [hfind] at hsome
  | some i =>
      have hi := Fin.eq_true_of_find?_eq_some hfind
      rw [mixingPowerCondition_iff] at hi
      simpa [firstMixingPower, bound, hfind] using hi

/-- Every smaller power fails the normalized inequality. -/
theorem firstMixingPower_minimal (N threshold t : ℕ)
    (ht : t < firstMixingPower N threshold) :
    ¬((25 : ℝ) / 32) ^ t * (N : ℝ) ^ 2 < (threshold : ℝ) ^ 2 := by
  let bound := mixingPowerBound N
  cases hfind : Fin.find? (fun i : Fin (bound + 1) =>
      mixingPowerCondition N threshold i) with
  | none =>
      have hfalse := Fin.eq_false_of_find?_eq_none hfind
      intro hnumeric
      rw [← mixingPowerCondition_iff] at hnumeric
      have htBound : t < bound + 1 := by
        simp [firstMixingPower, bound, hfind] at ht
        omega
      exact Bool.false_eq_true.mp ((hfalse ⟨t, htBound⟩).symm.trans hnumeric)
  | some i =>
      have hfalse := Fin.eq_false_of_find?_eq_some_of_lt hfind
      intro hnumeric
      rw [← mixingPowerCondition_iff] at hnumeric
      have hti : t < i := by simpa [firstMixingPower, bound, hfind] using ht
      have htFalse := hfalse ⟨t, Nat.lt_trans hti i.isLt⟩ hti
      exact Bool.false_eq_true.mp (htFalse.symm.trans hnumeric)

end GabberGalil
