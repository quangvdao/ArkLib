/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.LowestSCoefficient
import Mathlib.Algebra.Field.ZMod

/-! Compile-time and runtime checks for lowest-`s` coefficient semantics. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay

namespace RojasLowestSCoefficientTests

abbrev F := ZMod 7

private def sample : Parameters 1 F :=
  CMvPolynomial.monomial #v[1, 0, 2] 3 +
    CMvPolynomial.monomial #v[0, 1, 4] 5

private def mutated : Parameters 1 F :=
  sample + CMvPolynomial.monomial #v[0, 0, 1] 6

example {n degree : ℕ} {H : Parameters n F}
    (hdegree : lowestSExponent? H = some degree) :
    coefficientInS degree H ≠ 0 ∧
      ∀ lower < degree, coefficientInS lower H = 0 :=
  lowestSExponent?_eq_some_iff.mp hdegree

example : lowestSExponent? (0 : Parameters 1 F) = none :=
  lowestSExponent?_eq_none_iff _ |>.2 rfl

/-- Check the scanner and coefficient extraction on two distinct final
exponents, then mutate the polynomial by inserting a lower term. -/
def runChecks : IO Unit := do
  unless lowestSExponent? sample == some 2 do
    throw (IO.userError "Rojas lowest-s: wrong lowest exponent")
  unless coefficientInS 0 sample == 0 && coefficientInS 1 sample == 0 do
    throw (IO.userError "Rojas lowest-s: a lower coefficient was nonzero")
  unless coefficientInS 2 sample == CMvPolynomial.monomial #v[1, 0] 3 do
    throw (IO.userError "Rojas lowest-s: extracted coefficient lost its free monomial")
  unless coefficientInS 4 sample == CMvPolynomial.monomial #v[0, 1] 5 do
    throw (IO.userError "Rojas lowest-s: higher coefficient was extracted incorrectly")
  unless lowestSExponent? mutated == some 1 do
    throw (IO.userError "Rojas lowest-s: input mutation did not change the scan")
  unless lowestSExponent? (0 : Parameters 1 F) == none do
    throw (IO.userError "Rojas lowest-s: zero polynomial did not return none")
  IO.println "Rojas lowest-s: scan, extraction, mutation, and zero checks passed"

#print axioms coefficientInS_ne_zero_iff
#print axioms lowestSExponent?_eq_some_iff
#print axioms lowestSExponent?_eq_none_iff

end RojasLowestSCoefficientTests
