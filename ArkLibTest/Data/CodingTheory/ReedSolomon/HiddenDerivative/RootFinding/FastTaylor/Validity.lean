/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Validity
import Mathlib.Algebra.Field.ZMod

/-! Characteristic guards and a cleared agreement identity at a nonzero center. -/

open CPoly CPoly.CMvPolynomial ReedSolomon.HiddenDerivative.FastTaylor

namespace FastTaylorValidityTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem supported : Supported 5 1 5 2 := ⟨by decide, by decide, by decide⟩

example : IsUnit (4 : ZMod 5) := supported.integration_unit (by decide) (by decide)
example : IsUnit (Nat.choose 4 1 : ZMod 5) := supported.hasse_pivot_unit (by decide) (by decide)
example : ¬ Supported 5 1 6 2 := by intro h; have := h.precision_le; omega
example : globalDegreeBudget 5 2 < parameterPrecision 5 2 :=
  globalDegreeBudget_lt_precision _ _
example : 0 < 5 - 1 := supported.residual_pos

private def chart : ChartData (ZMod 5) 0 2 where
  center := 2
  projection := 1
  inverseProjection := 1
  equation := X 0 ^ 2
  separant := 1
  denominator := C 3
  numerators := ![C 1, C 4]

example (alpha received : ZMod 5) :
    CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) (fun _ => 0) (chart.agreement alpha received) =
      CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) (fun _ => 0) chart.denominator *
        ((∑ j : Fin 2, (![2, 3] : Fin 2 → ZMod 5) j * (alpha - chart.center) ^ j.val) -
          received) := by
  apply chart.eval₂_agreement_of_cleared
  intro j
  fin_cases j <;> decide

/-- Exercise the common denominator and the local-center power convention. -/
def run : IO Unit := do
  unless CMvPolynomial.eval (fun _ => 0) (chart.agreement 4 3) == 0 do
    throw (IO.userError "cleared agreement failed at a shifted center")
  unless globalDegreeBudget 5 2 == 11 && parameterPrecision 5 2 == 12 do
    throw (IO.userError "paper degree and parameter precision mismatch")

end FastTaylorValidityTests
