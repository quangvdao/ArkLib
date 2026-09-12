/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.UnivariateFactorization

/-! Derived splitting-field factors, with multiplicity retained by roots. -/

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.UnivariatePerturbation
open ArkLib.Rojas.Producer.UnivariateFactorization

namespace RojasUnivariateFactorizationTests

#print axioms ArkLib.Rojas.Producer.UnivariateFactorization.toPoly_derivedFactor
#print axioms ArkLib.Rojas.Producer.UnivariateFactorization.transformed_eq_root_product
#print axioms ArkLib.Rojas.Producer.UnivariateFactorization.derivedFactor_eq_root_product
#print axioms ArkLib.Rojas.Producer.UnivariateFactorization.map_derivedFactor_eq_root_product
#print axioms ArkLib.Rojas.Producer.UnivariateFactorization.Output.map_factor_eq_root_product

/-- The computed cubic factor visibly retains the zero root and both copies of
the repeated nonzero root. -/
def run : IO Unit := do
  let x : CPolynomial ℚ := X
  let f := x * (x - C 2) ^ 2
  let expected := x * (x + C 2) ^ 2
  unless derivedFactor f 3 == expected do
    throw (IO.userError "Rojas factorization: multiplicity-bearing product was not derived")
  unless (derivedFactor f 3).eval 0 == 0 do
    throw (IO.userError "Rojas factorization: zero root was lost")
  unless (derivedFactor f 3).eval (-2) == 0 do
    throw (IO.userError "Rojas factorization: nonzero repeated root was lost")
  IO.println "Rojas univariate factorization: root-multiset checks passed"

end RojasUnivariateFactorizationTests
