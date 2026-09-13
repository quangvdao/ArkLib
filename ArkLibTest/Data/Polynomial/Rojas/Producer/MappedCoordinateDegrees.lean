/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MappedCoordinateDegrees
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Proof and runtime checks for actual mapped coordinate degree preservation. -/

open CPoly CPoly.CMvPolynomial
open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas ArkLib.Rojas.Producer ArkLib.Rojas.Producer.SubresultantMap

namespace RojasMappedCoordinateDegreesTests

abbrev F := ZMod 11

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def perturbation : CMvPolynomial 3 F :=
  (CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.X 2) *
    (CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.X 1)

private def candidate : SpecializationCandidate (F := F) :=
  candidateFromParameter perturbation 1 2

/-- The support guard alone supplies the exact degree record over the algebraic closure. -/
example {s M : ℕ} {q : CMvPolynomial (s + 1) F} (alpha epsilon : F)
    (theta : AlgebraicClosure F)
    (hsupport : HasExpectedSupportDegree 11 s M
      (candidateFromParameter q alpha epsilon))
    (hM : 0 < M) (halpha : alpha ≠ 0) :
    MappedCoordinateDegrees (s := s) 11 alpha
      (candidateFromParameter q alpha epsilon)
      (algebraMap F (AlgebraicClosure F)) theta :=
  mappedCoordinateDegrees_of_expected (algebraMap F (AlgebraicClosure F))
    alpha epsilon theta hsupport hM halpha

/-- Execute the asymmetric zero-second-input branch and the actual raw, reduced, and product
coefficient path at both roots of the system-derived candidate. -/
def run : IO Unit := do
  let x : CPolynomial F := CPolynomial.X
  let zeroSecond := firstSubresultant (x - CPolynomial.C 4) 0
  unless zeroSecond.1 != 0 do
    throw (IO.userError "zero-second-input first-subresultant branch vanished")
  unless hasExpectedSupportDegree 11 2 2 candidate do
    throw (IO.userError "system-derived candidate lost its expected support")
  for theta in [7, 9] do
    for index in ([⟨0, by omega⟩, ⟨1, by omega⟩] : List (Fin 2)) do
      let raw := (coordinateSubresultant 11 2 1 candidate index).1.eval theta
      let reduced := (reducedCoordinateSubresultant 11 2 1 candidate index).1.eval theta
      unless raw != 0 && reduced != 0 do
        throw (IO.userError "actual coordinate principal coefficient vanished")
    unless (commonDenominator 11 2 1 candidate).eval theta != 0 do
      throw (IO.userError "actual common denominator vanished after reduction")
  IO.println "Rojas mapped coordinate degrees: checks passed"

#print axioms liftInTheta_toPoly
#print axioms map_liftInTheta
#print axioms map_affineTransform_natDegree
#print axioms mappedCoordinateDegrees_of_expected
#print axioms produce_representsPoint_of_factorization

end RojasMappedCoordinateDegreesTests

def rojasMappedCoordinateDegreesStandaloneMain : IO Unit :=
  RojasMappedCoordinateDegreesTests.run
