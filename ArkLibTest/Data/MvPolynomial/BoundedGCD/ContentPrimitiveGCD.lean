/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.ContentPrimitiveGCD
import Mathlib.Data.Int.GCD

/-! Executable and compile-time tests for content and primitive-part gcd assembly. -/

open CPoly CompPoly
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD

namespace ContentPrimitiveGCDTests

abbrev Coefficient := ℤ

def lowerGcd (left right : Coefficient) : Coefficient :=
  gcd left right

private theorem lowerGcdLaws : GcdLaws lowerGcd where
  dvd_left left right := by simpa [lowerGcd] using gcd_dvd_left left right
  dvd_right left right := by simpa [lowerGcd] using gcd_dvd_right left right
  greatest hleft hright := by simpa [lowerGcd] using dvd_gcd hleft hright

def exactDivide? (dividend divisor : Coefficient) : Option Coefficient :=
  if divisor = 0 then none
  else
    let quotient := dividend / divisor
    if quotient * divisor = dividend then some quotient else none

private theorem exactDivideLaws : DivideLaws exactDivide? where
  sound := by
    intro dividend divisor quotient h
    unfold exactDivide? at h
    split at h
    · simp at h
    · dsimp only at h
      split at h
      · rename_i hidentity
        simp only [Option.some.injEq] at h
        subst quotient
        exact hidentity
      · simp at h
  complete := by
    intro dividend divisor hdivisor hdvd
    refine ⟨dividend / divisor, ?_⟩
    have hidentity : dividend / divisor * divisor = dividend := by
      exact Int.ediv_mul_cancel hdvd
    simp [exactDivide?, hdivisor, hidentity]

example (left right : CPolynomial Coefficient) :
    ∃ result, compute? lowerGcd exactDivide? left right = some result ∧
      Certificate left right result :=
  compute?_exists_certificate lowerGcd exactDivide? lowerGcdLaws exactDivideLaws left right

/-- Both inputs have nonunit integer coefficient content and the nonconstant primitive factor
`y + 1`; the executable full gcd recovers both layers. -/
def run : IO Unit := do
  let y : CPolynomial Coefficient := CPolynomial.X
  let left := CPolynomial.C 6 * ((y + 1) * (y + 2))
  let right := CPolynomial.C 9 * ((y + 1) * (y + 3))
  let expected := CPolynomial.C 3 * (y + 1)
  unless compute? lowerGcd exactDivide? 0 right == some right do
    throw (IO.userError "full gcd mishandled a zero left input")
  unless compute? lowerGcd exactDivide? left 0 == some left do
    throw (IO.userError "full gcd mishandled a zero right input")
  unless compute? lowerGcd exactDivide? 0 0 == some 0 do
    throw (IO.userError "full gcd mishandled two zero inputs")
  let some result := compute? lowerGcd exactDivide? left right
    | throw (IO.userError "full content/primitive gcd computation failed")
  unless result == expected || result == -expected do
    throw (IO.userError
      "full gcd did not recover the shared content and primitive factor up to a unit")

#print axioms Certificate
#print axioms compute?_exists_certificate
#print axioms compute?_certificate

end ContentPrimitiveGCDTests
