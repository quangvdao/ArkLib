/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ClearDenominators

/-! Executed global denominator clearing, primitive descent, and a denominator-zero fiber. -/

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms

namespace ClearDenominatorsTests

private abbrev P := CPolynomial ℚ
private abbrev E := StoredField.Carrier ℚ
private def x : P := CPolynomial.X
private def u : E := StoredField.ofPolynomial x
private def input : CPolynomial E :=
  CPolynomial.ofArray #[u / (u + 1), (u + 1)⁻¹]

example :
    ClearDenominators.valueGlobal (ClearDenominators.clear input).global =
      Polynomial.C
          (algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (ClearDenominators.clear input).scale.toPoly) *
        FunctionFieldEuclid.value input :=
  ClearDenominators.clear_global_identity input

example :
    (CPolynomial.C (ClearDenominators.clear input).content :
        CPolynomial (CPolynomial ℚ)) *
      (ClearDenominators.clear input).primitive =
        (ClearDenominators.clear input).global :=
  ClearDenominators.clear_primitive_identity input

example : Associated
    (ClearDenominators.valueGlobal (ClearDenominators.clear input).primitive)
    (FunctionFieldEuclid.value input) :=
  ClearDenominators.clear_primitive_associated input

example (hp : FunctionFieldEuclid.value input ≠ 0) :
    (CBivariate.toPoly (ClearDenominators.clear input).primitive).IsPrimitive :=
  ClearDenominators.clear_primitive_isPrimitive hp

/-- Both coefficients create the same nonconstant denominator.  Their product is
kept globally, then content removal produces `X + Y`.  At `X = -1` the common
denominator and every raw descended coefficient vanish, while the proved global
cross-product identity still specializes to `0 = 0`. -/
def run : IO Unit := do
  let result := ClearDenominators.clear input
  unless result.scale == (x + 1) ^ 2 do
    throw (IO.userError "denominator product did not retain both coefficient denominators")
  unless CPolynomial.coeff result.global 0 == x * (x + 1) do
    throw (IO.userError "wrong globally cleared constant coefficient")
  unless CPolynomial.coeff result.global 1 == x + 1 do
    throw (IO.userError "wrong globally cleared linear coefficient")
  unless result.content == x + 1 do
    throw (IO.userError "primitive descent computed the wrong content")
  unless CPolynomial.coeff result.primitive 0 == x &&
      CPolynomial.coeff result.primitive 1 == 1 do
    throw (IO.userError "primitive descent did not return X + Y")
  let bad : ℚ := -1
  unless result.scale.eval bad == 0 &&
      (CPolynomial.coeff result.global 0).eval bad == 0 &&
      (CPolynomial.coeff result.global 1).eval bad == 0 do
    throw (IO.userError "test did not reach the denominator-zero fiber")
  let lhs := (CPolynomial.coeff result.global 0).eval bad *
    (StoredField.denominator (input.coeff 0)).eval bad
  let rhs := result.scale.eval bad * (StoredField.numerator (input.coeff 0)).eval bad
  unless lhs == rhs && rhs == 0 do
    throw (IO.userError "global coefficient identity failed at denominator-zero fiber")

end ClearDenominatorsTests

#print axioms ClearDenominators.clear_primitive_isPrimitive
#print axioms ClearDenominators.clear_primitive_associated
#print axioms ClearDenominators.clear_global_coefficient_identity
