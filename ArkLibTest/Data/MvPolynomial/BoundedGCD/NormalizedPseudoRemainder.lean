/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.NormalizedPseudoRemainder
import ArkLib.Data.MvPolynomial.BoundedGCD.CheckedCandidate
import Mathlib.Algebra.Field.ZMod

/-! Executable tests for normalized pseudo-remainder sequences. -/

open CPoly CPoly.CMvPolynomial CompPoly
open CPoly.CMvPolynomial.BoundedGCD
open CPoly.CMvPolynomial.BoundedGCD.NormalizedPseudoRemainder
open CPoly.CMvPolynomial.CheckedExactDivision

namespace NormalizedPseudoRemainderTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def lowerGcd (left right : CMvPolynomial 1 (ZMod 5)) :
    CMvPolynomial 1 (ZMod 5) :=
  if left = 0 then right
  else if right = 0 then left
  else
    match checkedCandidate? left right with
    | some data => data.divisor
    | none => 1

example (dividend divisor : CPolynomial (CMvPolynomial 1 (ZMod 5)))
    (data : Data (CMvPolynomial 1 (ZMod 5)))
    (h : compute? lowerGcd exactQuotient? dividend divisor = some data) :
    CPolynomial.C data.scale * dividend =
      data.quotient * divisor + CPolynomial.C data.content * data.remainder :=
  compute?_certifies lowerGcd exactQuotient? dividend divisor data h

example (dividend divisor common : CPolynomial (CMvPolynomial 1 (ZMod 5)))
    (data : Data (CMvPolynomial 1 (ZMod 5)))
    (h : compute? lowerGcd exactQuotient? dividend divisor = some data)
    (hl : common ∣ dividend) (hr : common ∣ divisor) :
    common ∣ CPolynomial.C data.content * data.remainder :=
  compute?_common_divisor_preserved lowerGcd exactQuotient?
    dividend divisor common data h hl hr

example (dividend divisor : CPolynomial (CMvPolynomial 1 (ZMod 5)))
    (data : Data (CMvPolynomial 1 (ZMod 5)))
    (h : compute? lowerGcd exactQuotient? dividend divisor = some data)
    (hd : divisor ≠ 0) :
    degreeMeasure data.remainder < degreeMeasure divisor :=
  compute?_degreeMeasure_lt lowerGcd exactQuotient? dividend divisor data h hd

/-- The unnormalized sequence proposes `x²` for `x(y+1), xy`. Immediate content normalization
turns that pseudo-remainder into one, and the bounded normalized sequence returns one. -/
def run : IO Unit := do
  let x : CMvPolynomial 1 (ZMod 5) := CMvPolynomial.X 0
  let y : CPolynomial (CMvPolynomial 1 (ZMod 5)) := CPolynomial.X
  let left := CPolynomial.C x * (y + 1)
  let right := CPolynomial.C x * y
  let raw := pseudoDivide left right
  unless raw.remainder == CPolynomial.C (x ^ 2) do
    throw (IO.userError "counterexample did not produce the expected raw x^2 remainder")
  let some step := compute? lowerGcd exactQuotient? left right
    | throw (IO.userError "normalized pseudo-remainder rejected the Gauss counterexample")
  unless CPolynomial.C step.scale * left ==
      step.quotient * right + CPolynomial.C step.content * step.remainder do
    throw (IO.userError "normalized pseudo-remainder reconstruction failed")
  unless step.content == x ^ 2 do
    throw (IO.userError "normalization did not extract the x^2 coefficient content")
  unless step.remainder == 1 do
    throw (IO.userError "normalization retained the rejected x^2 proposal")
  let some result := candidate? lowerGcd exactQuotient? left right
    | throw (IO.userError "normalized pseudo-remainder sequence exhausted its budget")
  unless result == 1 do
    throw (IO.userError "normalized pseudo-remainder sequence returned a nonprimitive candidate")

#print axioms compute?_raw_remainder_identity
#print axioms compute?_certifies
#print axioms compute?_common_divisor_preserved
#print axioms compute?_remainder_eq_zero_iff
#print axioms compute?_natDegree_eq
#print axioms compute?_terminal
#print axioms compute?_degreeMeasure_lt

end NormalizedPseudoRemainderTests
