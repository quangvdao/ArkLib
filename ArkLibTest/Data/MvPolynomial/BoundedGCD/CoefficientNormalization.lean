/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.CoefficientNormalization
import ArkLib.Data.MvPolynomial.BoundedGCD.CheckedCandidate
import Mathlib.Algebra.Field.ZMod

open CPoly CPoly.CMvPolynomial CompPoly
open CPoly.CMvPolynomial.BoundedGCD
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.CheckedExactDivision

namespace CoefficientNormalizationTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def lowerGcd (left right : CMvPolynomial 1 (ZMod 5)) :
    CMvPolynomial 1 (ZMod 5) :=
  if left = 0 then right
  else if right = 0 then left
  else
    match checkedCandidate? left right with
    | some data => data.divisor
    | none => 1

/-- Execute a real lower-dimensional common-factor fold and coefficientwise stored exact division
on a polynomial whose coefficients share `X+1`. -/
def run : IO Unit := do
  let x : CMvPolynomial 1 (ZMod 5) := CMvPolynomial.X 0
  let z : CPolynomial (CMvPolynomial 1 (ZMod 5)) := CPolynomial.X
  let content := x + 1
  let p := CPolynomial.C content * z ^ 2 + CPolynomial.C (content * (x + 2)) * z +
    CPolynomial.C content
  let some data := normalize? lowerGcd exactQuotient? p
    | throw (IO.userError "coefficient normalization rejected exact shared content")
  unless CPolynomial.C data.content * data.primitive == p do
    throw (IO.userError "coefficient normalization reconstruction failed")
  unless data.primitive != 0 do
    throw (IO.userError "coefficient normalization returned zero for nonzero input")

#print axioms normalize?_content_eq
#print axioms normalize?_identity
#print axioms normalize?_primitive_ne_zero

end CoefficientNormalizationTests
