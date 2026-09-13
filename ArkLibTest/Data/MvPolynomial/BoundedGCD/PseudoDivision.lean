/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.PseudoDivision
import Mathlib.Algebra.Field.ZMod

open CPoly CPoly.CMvPolynomial CPoly.CMvPolynomial.BoundedGCD CompPoly

namespace PseudoDivisionTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (dividend divisor : CPolynomial ℤ) :
    (pseudoDivide dividend divisor).Certifies dividend divisor :=
  pseudoDivide_certifies dividend divisor

example (divisor : CPolynomial ℤ) (state : PseudoDivisionState ℤ)
    (hr : state.remainder ≠ 0) (hd : divisor ≠ 0)
    (hle : divisor.natDegree ≤ state.remainder.natDegree) :
    degreeMeasure (pseudoStep divisor state).remainder < degreeMeasure state.remainder :=
  pseudoStep_remainder_degreeMeasure_lt divisor state hr hd hle

example (dividend divisor : CPolynomial ℤ) (hd : divisor ≠ 0) :
    let result := pseudoDivide dividend divisor
    result.remainder = 0 ∨ result.remainder.natDegree < divisor.natDegree :=
  pseudoDivide_terminal dividend divisor hd

example (dividend divisor : CPolynomial (CMvPolynomial 1 (ZMod 5)))
    (hd : divisor ≠ 0) :
    let result := pseudoDivide dividend divisor
    result.remainder = 0 ∨ result.remainder.natDegree < divisor.natDegree :=
  pseudoDivide_terminal dividend divisor hd

example (dividend divisor : CPolynomial (CMvPolynomial 1 (ZMod 5))) :
    let result := pseudoDivide dividend divisor
    CMvPolynomial.rename Fin.castSucc result.scale *
        CPoly.TaylorReconstruction.flattenLast dividend =
      CPoly.TaylorReconstruction.flattenLast result.quotient *
          CPoly.TaylorReconstruction.flattenLast divisor +
        CPoly.TaylorReconstruction.flattenLast result.remainder :=
  flatten_pseudoDivide_identity dividend divisor

/-- Exercise nonmonic pseudo-division over an integral coefficient ring. -/
def run : IO Unit := do
  let x : CPolynomial ℤ := CPolynomial.X
  let dividend := 2 * x ^ 3 + 3 * x ^ 2 - x + 5
  let divisor := 2 * x + 1
  let result := pseudoDivide dividend divisor
  unless CPolynomial.C result.scale * dividend ==
      result.quotient * divisor + result.remainder do
    throw (IO.userError "pseudo-division reconstruction failed")
  unless result.remainder == 48 do
    throw (IO.userError "pseudo-division returned the wrong nonmonic remainder")
  unless result.scale == 8 do
    throw (IO.userError "pseudo-division accumulated the wrong leading-coefficient power")
  let t : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 0
  let z : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 1
  let flatDividend := (t + 1) * z ^ 3 + t * z ^ 2 + z + 2
  let multivariateDividend := CPoly.TaylorReconstruction.splitLast flatDividend
  let multivariateDivisor : CPolynomial (CMvPolynomial 1 (ZMod 5)) :=
    CPolynomial.C (CMvPolynomial.X 0 + 1) * CPolynomial.X + 1
  let multivariateResult := pseudoDivide multivariateDividend multivariateDivisor
  unless CPolynomial.C multivariateResult.scale * multivariateDividend ==
      multivariateResult.quotient * multivariateDivisor + multivariateResult.remainder do
    throw (IO.userError "multivariate pseudo-division reconstruction failed")
  unless multivariateResult.remainder == 0 ||
      multivariateResult.remainder.natDegree < multivariateDivisor.natDegree do
    throw (IO.userError "multivariate pseudo-division exhausted its default fuel")

#print axioms pseudoDivide_certifies
#print axioms pseudoStep_remainder_degreeMeasure_lt
#print axioms pseudoDivide_terminal
#print axioms flatten_pseudoDivide_identity

end PseudoDivisionTests
