/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.CheckedCandidate
import Mathlib.Algebra.Field.ZMod

open CPoly CPoly.CMvPolynomial CPoly.CMvPolynomial.BoundedGCD CompPoly

namespace CheckedCandidateTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (left right : CMvPolynomial 2 (ZMod 5))
    (result : CheckedCandidate left right) (h : checkedCandidate? left right = some result) :
    result.leftQuotient * result.divisor = left ∧
      result.rightQuotient * result.divisor = right :=
  ⟨checkedCandidate?_left_identity left right result h,
    checkedCandidate?_right_identity left right result h⟩

/-- Exercise a nonconstant common factor in two stored variables. -/
def run : IO Unit := do
  let x : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 0
  let y : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 1
  let common := y + x + 1
  let left := common * (y + 1)
  let right := common * (y + 2)
  unless pseudoGcdCandidate (CPoly.TaylorReconstruction.splitLast left) 0 ==
      CPoly.TaylorReconstruction.splitLast left do
    throw (IO.userError "zero-right pseudo-gcd did not retain the left input")
  let some result := checkedCandidate? left right
    | throw (IO.userError "checked common-factor producer rejected an exact candidate")
  unless result.divisor != 0 do
    throw (IO.userError "checked common-factor producer returned zero")
  unless result.leftQuotient * result.divisor == left do
    throw (IO.userError "left reconstruction failed")
  unless result.rightQuotient * result.divisor == right do
    throw (IO.userError "right reconstruction failed")
  unless result.divisor.totalDegree > 0 do
    throw (IO.userError "producer missed the nonconstant common factor")

#print axioms checkedCandidate?_divisor_ne_zero
#print axioms checkedCandidate?_left_identity
#print axioms checkedCandidate?_right_identity
#print axioms checkedCandidate?_dvd

end CheckedCandidateTests
