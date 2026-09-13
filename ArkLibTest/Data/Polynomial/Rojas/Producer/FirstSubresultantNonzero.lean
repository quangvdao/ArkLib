/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantNonzero
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Proof and runtime checks for mapped first-principal-subresultant nonvanishing. -/

open CompPoly CompPoly.CPolynomial Polynomial
open ArkLib.Rojas ArkLib.Rojas.Producer ArkLib.Rojas.Producer.SubresultantMap

namespace RojasFirstSubresultantNonzeroTests

abbrev F := ZMod 11

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def x : CPolynomial F := X

private def left : CPolynomial F := (x - CPolynomial.C 1) * (x - CPolynomial.C 2)

private def right : CPolynomial F := (x - CPolynomial.C 1) * (x - CPolynomial.C 3)

/-- The coefficient-lift identity is usable at the actual algebraic closure map. -/
example (q : CPolynomial F) (theta : AlgebraicClosure F) :
    (liftInTheta q).toPoly.map (coefficientEval (algebraMap F (AlgebraicClosure F)) theta) =
      q.toPoly.map (algebraMap F (AlgebraicClosure F)) :=
  map_liftInTheta (algebraMap F (AlgebraicClosure F)) theta q

/-- Execute the nonmonic common-factor example and reject a pair with degree-two gcd. -/
def run : IO Unit := do
  let sharedLinear := firstSubresultant left right
  unless sharedLinear.1 == (-1 : F) do
    throw (IO.userError "degree-one gcd produced a zero or incorrectly normalized minor")
  let identical := firstSubresultant left left
  unless identical.1 == 0 do
    throw (IO.userError "degree-two gcd did not zero the first principal subresultant")
  let mappedLinear := firstSubresultant (x - CPolynomial.C 4) (x - CPolynomial.C 4)
  unless mappedLinear.1 != 0 do
    throw (IO.userError "asymmetric degree-one branch produced a zero coefficient")
  IO.println "Rojas mapped first-subresultant nonvanishing: checks passed"

#print axioms FirstSubresultantNonzero.productTailRows_eq_sylvester_mul_tail
#print axioms FirstSubresultantNonzero.map_firstSubresultant_fst_eq_resultant_of_factorization
#print axioms FirstSubresultantNonzero.mapped_firstSubresultant_fst_ne_zero_of_gcd_natDegree_eq_one'
#print axioms normalized_gcd_natDegree_eq_euclidean_gcd
#print axioms coordinateSubresultant_fst_ne_zero_of_factorization
#print axioms reducedCoordinateSubresultant_fst_ne_zero_of_factorization
#print axioms commonDenominator_ne_zero_of_factorization

end RojasFirstSubresultantNonzeroTests

def main : IO Unit := RojasFirstSubresultantNonzeroTests.run
