/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CanonicalRepresentative

/-! Executed canonical extraction from the stored rational-function quotient. -/

open CompPoly CPolynomial Polynomial.FunctionFieldAlgorithms

namespace CanonicalRepresentativeTests

private abbrev P := CPolynomial ℚ
private abbrev E := StoredField.Carrier ℚ
private def x : P := CPolynomial.X

example (a b : CanonicalRepresentative ℚ) (h : a.value = b.value) : a = b :=
  CanonicalRepresentative.eq_of_value_eq a b h

example (a : E) :
    StoredField.value a =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (StoredField.numerator a).toPoly /
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (StoredField.denominator a).toPoly :=
  StoredField.value_eq_num_div_den a

/-- Equivalent quotient representatives normalize to identical stored data; zero
uses `0/1`, and nonconstant denominators are retained and made monic. -/
def run : IO Unit := do
  let two : P := CPolynomial.C 2
  let a : Fraction ℚ := ⟨two * (x + CPolynomial.C 2), two * (x + CPolynomial.C 3)⟩
  let b : Fraction ℚ := ⟨x + CPolynomial.C 2, x + CPolynomial.C 3⟩
  let qa : E := StoredField.ofFraction a (by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    norm_num [a, two, x, CPolynomial.toPoly_mul, CPolynomial.toPoly_add,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly] at he)
  let qb : E := StoredField.ofFraction b (by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    norm_num [b, x, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
      CPolynomial.X_toPoly] at he)
  let ca := StoredField.canonical qa
  let cb := StoredField.canonical qb
  unless ca.numerator == x + CPolynomial.C 2 && ca.denominator == x + CPolynomial.C 3 do
    throw (IO.userError "canonical quotient extraction returned the wrong fraction")
  unless ca.numerator == cb.numerator && ca.denominator == cb.denominator do
    throw (IO.userError "equivalent fractions did not normalize structurally")
  unless ca.denominator.monic do
    throw (IO.userError "canonical denominator is not monic")
  let cz := StoredField.canonical (0 : E)
  unless cz.numerator == 0 && cz.denominator == 1 do
    throw (IO.userError "zero did not normalize to 0/1")

end CanonicalRepresentativeTests

#print axioms CanonicalRepresentative.eq_of_value_eq
#print axioms StoredField.value_eq_num_div_den
