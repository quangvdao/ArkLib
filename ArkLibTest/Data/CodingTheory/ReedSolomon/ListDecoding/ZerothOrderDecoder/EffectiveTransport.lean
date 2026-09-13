/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveTransport
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveFrobeniusCoordinates

/-! Generic effective-field transport through all center branches and nonempty recovery. -/

namespace EffectiveTransportTests

open CompPoly Polynomial ReedSolomon ReedSolomon.ListDecoding
open ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms
open ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveTransport

private def scaledGraph {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (m : ℕ) : CBivariate K :=
  CPolynomial.C ((CPolynomial.X : CPolynomial K) ^ m) *
    ((CPolynomial.X : CBivariate K) - CPolynomial.C (CPolynomial.X : CPolynomial K))

private def domain {p : ℕ} {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (field : EffectiveField p K) : Fin field.index.cardinality ↪ K :=
  field.index.equivFin.toEmbedding

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Check a regular equation through the actual dispatcher and exact base-field recovery.
The scaled graph forces extension centers; output coefficients are checked independently. -/
private def checkGraph {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    [DecidableEq K] (field : EffectiveField p K) (scale k : ℕ)
    (branch : SuppliedCenters.Branch) (expected : List K) : IO Unit := do
  let equation : CBivariate K := scaledGraph scale
  let obstruction := RegularCenterObstruction.obstruction equation
  check "unexpected effective center branch" <|
    (EffectiveCenters.run field (obstruction.natDegree + 1)).branch == branch
  check "effective transport failed nonempty base-coefficient recovery" <|
    run? field equation obstruction (domain field) (domain field) k k == some [expected]

/-- Prime-field and supplied cyclic-coordinate clients exercise base, both relative quadratic
branches, and an F4 run with both n and k greater than the characteristic. -/
def run : IO Unit := do
  checkGraph (effectivePrimeField 2) 1 2 .binaryQuadratic [1, 0]
  checkGraph (effectivePrimeField 3) 0 2 .base [1, 0]
  checkGraph (effectivePrimeField 3) 2 2 .oddQuadratic [1, 0]
  checkGraph EffectiveFrobeniusCoordinatesTests.binaryCoordinates.effectiveField
    2 3 .binaryQuadratic [0, 1, 0]
  let field := effectivePrimeField 2
  let equation : CBivariate (ZMod 2) := scaledGraph 2
  let obstruction := RegularCenterObstruction.obstruction equation
  check "capacity failure did not remain explicit" <|
    run? field equation obstruction (domain field) (domain field) 2 2 == none

#print axioms run?_exact

end EffectiveTransportTests

def effectiveTransportMain : IO Unit := EffectiveTransportTests.run
