/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayDivisionCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and executable checks for graded-lex Macaulay division. -/

open CPoly CPoly.CMvPolynomial
open scoped MonomialOrder
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayDivisionCorrectnessTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def x : CMvPolynomial 1 F := X 0

private def divisor : CMvPolynomial 1 F := x + 1

private def quotient : CMvPolynomial 1 F := x + 2

private def dividend : CMvPolynomial 1 F := quotient * divisor

example {state next : DivisionState 1 (F := F)}
    (hstep : divisionStep? divisor state = some next) :
    MonomialOrder.degLex.withBotDegree (fromCMvPolynomial next.residual)
      ≺'[MonomialOrder.degLex]
    MonomialOrder.degLex.withBotDegree (fromCMvPolynomial state.residual) :=
  divisionStep?_withBotDegree_lt hstep

example {state next : DivisionState 1 (F := F)}
    (hstep : divisionStep? divisor state = some next) :
    next.quotient * divisor + next.residual =
      state.quotient * divisor + state.residual :=
  divisionStep?_invariant hstep

/-- Exercise multiple successful reductions and reject a non-divisible input. -/
def main : IO Unit := do
  unless checkedExactQuotient? dividend divisor == some quotient do
    throw <| IO.userError "graded-lex division rejected an exact quotient"
  unless checkedExactQuotient? x divisor == none do
    throw <| IO.userError "graded-lex division accepted a spurious quotient"
  IO.println "Rojas graded-lex division: exact quotient and rejection passed"

#print axioms leadingTerm?_degree
#print axioms divisionStep_subtrahend_leadingTerm
#print axioms divisionStep?_withBotDegree_lt
#print axioms divisionStep?_totalDegree_le
#print axioms divisionLoop_invariant

end RojasMacaulayDivisionCorrectnessTests

def main : IO Unit := RojasMacaulayDivisionCorrectnessTests.main
