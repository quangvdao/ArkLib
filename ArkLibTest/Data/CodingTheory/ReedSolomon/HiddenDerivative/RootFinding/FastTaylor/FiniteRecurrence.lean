/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.FiniteRecurrence
import Mathlib.Data.ZMod.Basic

/-!
# Finite Taylor-recurrence tests
-/

open ReedSolomon.HiddenDerivative.FastTaylor.FiniteRecurrence

private def increment : System (ZMod 4) where
  leading _ := 1
  remainder known := -(known.getLastD 0 + 1)

-- Two initial coefficients, five newly solved gates, and non-power-of-two precision.
example : increment.through [0, 1] 7 = [0, 1, 2, 3, 0, 1, 2] := by decide

-- The coefficient ring has a nonzero nilpotent.
example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

example : increment.Satisfies [0, 1] 5 [0, 1, 2, 3, 0, 1, 2] := by
  exact increment.run_satisfies [0, 1] 5

example (out : List (ZMod 4)) (h : increment.Satisfies [0, 1] 5 out) :
    out = [0, 1, 2, 3, 0, 1, 2] := by
  exact h.eq_run increment

example : increment.coeff [0, 1] 7 7 = 0 := by
  exact increment.coeff_eq_zero [0, 1] 7 7 (by decide) (by decide)

example : (increment.polynomial [0, 1] 7).degree < (7 : WithBot ℕ) :=
  increment.degree_polynomial_lt [0, 1] 7

#eval increment.through [0, 1] 7
#print axioms System.run_satisfies
#print axioms System.Satisfies.eq_run
#print axioms System.degree_polynomial_lt

example (j : ℕ) (hj : j < 5) :
    increment.Gate ((increment.run [0, 1] 5).take (2 + j))
      ((increment.run [0, 1] 5).getD (2 + j) 0) :=
  increment.gate_run [0, 1] j 5 hj

#print axioms System.gate_run
#print axioms System.eq_run_of_gates

private def negativeUnit : System (ZMod 4) where
  leading _ := -1
  remainder _ := 1

-- Exercise inversion of a nonidentity unit, rather than only multiplication by one.
example : negativeUnit.through [2] 3 = [2, 1, 1] := by decide

#eval negativeUnit.through [2] 3

namespace FiniteRecurrenceTests

/-- Compiled acceptance entrypoint for the executable finite recurrence. -/
def run : IO Unit := do
  unless increment.through [0, 1] 7 == [0, 1, 2, 3, 0, 1, 2] do
    throw (IO.userError "finite recurrence changed the nonreduced seven-term output")
  unless negativeUnit.through [2] 3 == [2, 1, 1] do
    throw (IO.userError "finite recurrence failed inversion of a nonidentity unit")

end FiniteRecurrenceTests
