/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Support.Machine

/-! # Polynomial-module coordinates for interpolation support

A fixed jet monomial contributes the initial interval of X exponents below `W - weight`.
This adapter does not compute a minimal approximant basis.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationModule

/-- Materialized jet exponents, with the zeroth jet separated from the higher jets. -/
structure JetMonomial where
  zeroth : ℕ
  higher : List ℕ
  deriving DecidableEq, Repr

/-- Scalar support vector in the existing enumerator's coordinate order. -/
def JetMonomial.vector (b : JetMonomial) (x : ℕ) : List ℕ := x :: b.zeroth :: b.higher

/-- The differential weight of the fixed jet monomial. -/
def JetMonomial.weight (b : JetMonomial) (D : ℕ) : ℕ :=
  InterpolationSupportMachine.jetWeight D 0 (b.zeroth :: b.higher)

/-- Allowed X exponents are a materialized initial interval, including an empty interval. -/
def JetMonomial.xInterval (b : JetMonomial) (D W : ℕ) : List ℕ :=
  List.range (W - b.weight D)

@[simp]
theorem JetMonomial.mem_xInterval (b : JetMonomial) (D W x : ℕ) :
    x ∈ b.xInterval D W ↔ x + b.weight D < W := by
  simp only [xInterval, List.mem_range]
  omega

/-- A jet monomial at or above the strict weight bound contributes no scalar columns. -/
theorem JetMonomial.xInterval_eq_nil (b : JetMonomial) (D W : ℕ)
    (h : W ≤ b.weight D) : b.xInterval D W = [] := by
  simp [xInterval, Nat.sub_eq_zero_of_le h]

/-- The module coordinate interval agrees exactly with existing scalar support membership. -/
theorem JetMonomial.mem_support_iff (b : JetMonomial) (D d m J A x : ℕ) :
    b.vector x ∈ InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A) ↔
      b.higher.length = d ∧ b.zeroth + b.higher.sum < J ∧
        x ∈ b.xInterval D (m * A) := by
  rw [JetMonomial.vector, InterpolationSupportMachine.mem_supportSpec_iff]
  simp only [InterpolationSupportMachine.parametersWithBudget, List.length_cons,
    List.sum_cons, Nat.add_right_cancel_iff, JetMonomial.mem_xInterval, JetMonomial.weight]

end ReedSolomon.HiddenDerivative.InterpolationModule
