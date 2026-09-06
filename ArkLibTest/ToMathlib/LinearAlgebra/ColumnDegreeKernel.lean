/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.ColumnDegreeKernel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Column-height boundary checks

Use an actual matrix with a column too expensive for the height budget. The two
constant columns leave a kernel, while the quadratic column must be inactive.
This exercises truncation at zero and a nonempty, nonzero constraint matrix.
-/

open Polynomial

example : ∃ v : Fin 3 → ℚ[X], v ≠ 0 ∧
    Matrix.mulVec (fun (_ : Fin 1) (j : Fin 3) ↦ if j = 2 then X ^ 2 else 1) v = 0 ∧
    v 2 = 0 := by
  let M : Matrix (Fin 1) (Fin 3) ℚ[X] := fun _ j ↦ if j = 2 then X ^ 2 else 1
  let weight : Fin 3 → ℕ := fun j ↦ if j = 2 then 2 else 0
  have hdeg : ∀ i j, (M i j).natDegree ≤ weight j := by
    intro i j
    fin_cases j <;> norm_num [M, weight, Fin.ext_iff]
  obtain ⟨v, hv, hMv, hbounds⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT M weight 0 hdeg (by
      norm_num [weight, Fin.sum_univ_succ, Fin.ext_iff])
  refine ⟨v, hv, hMv, ?_⟩
  have hzero : v 2 ∈ Polynomial.degreeLT ℚ 0 := by simpa [weight] using hbounds 2
  apply Polynomial.ext
  intro k
  exact (Polynomial.degree_lt_iff_coeff_zero _ 0).mp
    (Polynomial.mem_degreeLT.mp hzero) k (Nat.zero_le _)
