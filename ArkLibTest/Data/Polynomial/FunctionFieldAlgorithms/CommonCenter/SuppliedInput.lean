/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.SuppliedInput
import Mathlib.Algebra.Field.ZMod

/-! Supplied-coordinate conversion, partial derivatives, and actual preparation canaries. -/

namespace CommonCenterSuppliedInputTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter.SuppliedInput

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def x : CMvPolynomial 3 F := CMvPolynomial.X 0
private def y : CMvPolynomial 3 F := CMvPolynomial.X 1
private def z : CMvPolynomial 3 F := CMvPolynomial.X 2
private def inner : CBivariate K := CPolynomial.C CPolynomial.X
private def outer : CBivariate K := CPolynomial.X
private def coefficient (a : K) : CBivariate K := CPolynomial.C (CPolynomial.C a)

private def unequal : CMvPolynomial 3 F := x ^ 2 * y ^ 3 + x ^ 5 * z + y * z ^ 2
private def repeated : CMvPolynomial 3 F := (y - x ^ 2) * (z - 2 * x) ^ 2

/-- Unequal challenge/message/derivative exponents catch coordinate swaps; the second fixture
executes content retention and repeated-state removal from an actual trivariate input. -/
def runTests : IO Unit := do
  let t : K := challenge
  let expected := coefficient (t ^ 2) * inner ^ 3 + coefficient (t ^ 5) * outer +
    inner * outer ^ 2
  unless equation unequal == expected do
    throw (IO.userError "supplied coordinate axes were changed")
  unless equation (CMvPolynomial.partialDerivative 1 unequal) ==
      coefficient (3 * t ^ 2) * inner ^ 2 + outer ^ 2 do
    throw (IO.userError "supplied message partial is wrong")
  unless equation (CMvPolynomial.partialDerivative 2 unequal) ==
      coefficient (t ^ 5) + 2 * inner * outer do
    throw (IO.userError "supplied highest-state partial is wrong")
  unless equation (CMvPolynomial.partialDerivative 1 unequal) ==
      CBivariate.partialDerivX (equation unequal) &&
      equation (CMvPolynomial.partialDerivative 2 unequal) ==
      CBivariate.partialDerivY (equation unequal) do
    throw (IO.userError "stored partial compatibility failed")
  match run 7 repeated with
  | .prepared data =>
    unless data.regular == outer - coefficient (2 * t) &&
        data.ordinary == (CPolynomial.X : CPolynomial K) - CPolynomial.C (t ^ 2) do
      throw (IO.userError "supplied repeated-state/content preparation is wrong")
  | _ => throw (IO.userError "supplied preparation failed")
  match run (F := F) 7 0 with
  | .zeroEquation => pure ()
  | _ => throw (IO.userError "zero supplied equation used the wrong branch")

example (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0) : equation Q ≠ 0 := equation_ne_zero hQ

example (Q : CMvPolynomial 3 F) :
    equation (CMvPolynomial.partialDerivative 1 Q) = CBivariate.partialDerivX (equation Q) :=
  equation_partialDerivative_Y Q

example (Q : CMvPolynomial 3 F) :
    equation (CMvPolynomial.partialDerivative 2 Q) = CBivariate.partialDerivY (equation Q) :=
  equation_partialDerivative_Z Q

example (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0)
    (hd : (ClearDenominators.primitivePart (equation Q)).natDegree < 7) :
    ∃ data, run 7 Q = .prepared data ∧ data.ordinary ≠ 0 := by
  obtain ⟨data, hr, hn, _⟩ := run_exists_partition 7 Q hQ hd
  exact ⟨data, hr, hn⟩

#print axioms equation_evalAt
#print axioms equation_partialDerivative_Y
#print axioms equation_partialDerivative_Z
#print axioms stateHom_injective
#print axioms equation_injective
#print axioms equation_ne_zero
#print axioms equation_graph
#print axioms run_exists_partition

end CommonCenterSuppliedInputTests
