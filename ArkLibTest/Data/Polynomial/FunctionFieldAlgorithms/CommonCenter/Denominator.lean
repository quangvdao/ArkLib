/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.Denominator
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.BoundedNilpotence
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.DualNumber

/-! Tests for finite denominator assembly and nonreduced boundary initial values. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter

-- Actual finite sums: two charts combine to the identity in characteristic two.
example : combineDenominator (fun _ : Fin 2 => (1 : ZMod 2))
    ![0, 1] = 1 := by decide

#eval decide (combineDenominator (fun _ : Fin 2 => (1 : ZMod 2)) ![0, 1] = 1)

-- The zero ideal is retained as zero, without manufacturing a unit.
example : combineDenominator (fun _ : Fin 0 => (1 : ZMod 2))
    (fun _ => 0) = 0 := by decide

-- Cross multiplication remains valid in a nonreduced ring of small characteristic.
example : combineDenominator (fun _ : Fin 1 => (1 : ZMod 4)) ![2] * 2 =
    combineNumerator (fun _ : Fin 1 => (1 : ZMod 4)) (fun _ : Fin 1 => ![0]) 0 := by
  decide

-- A rejected center has all denominators zero and cannot satisfy coverage.
example : coverageValue (fun _ : Fin 1 => (0 : ZMod 2))
    (fun _ _ => 0) (fun _ => 1) (fun _ _ : Fin 1 => 1) ≠ 1 := by decide

-- The single rule genuinely uses the same weights on both sides.
example : combineDenominator (fun _ : Fin 2 => (1 : ZMod 5)) ![2, 3] = 0 ∧
    combineNumerator (fun _ : Fin 2 => (1 : ZMod 5))
      (fun l : Fin 2 => if l = 0 then ![4] else ![1]) 0 = 0 := by decide

-- Dual numbers over F₂ are genuinely nonreduced. Their nilpotent initial
-- coordinate dies under every field-valued evaluation.
example {L : Type*} [Field L] (φ : DualNumber (ZMod 2) →+* L) :
    φ DualNumber.eps = 0 :=
  map_eq_zero_of_bounded_power φ DualNumber.eps_pow_two

#print axioms denominatorIdeal
#print axioms square_mul_mem_denominatorIdeal
#print axioms combine_mul
#print axioms exists_denominator_ne_zero
#print axioms combination_idempotent
#print axioms nilpotent_pow_finrank
#print axioms nilpotent_iff_pow_eq_zero

#print axioms nilpotent_sum_iff_powerColumns
#print axioms inverse_power_kernel_iff_nilpotent
