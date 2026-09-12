/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport
import ArkLibTest.Data.FiniteField.ExplicitConstruction.ArtinSchreierCenters
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasis

/-! Compiled branch and coefficient-transport checks for supplied-field zeroth decoding. -/

namespace SuppliedTransportTests

open CompPoly Polynomial ReedSolomon ReedSolomon.ListDecoding
open ArkLib.FiniteField.ExplicitConstruction ArkLib.PolynomialQuotient
open Polynomial.FunctionFieldAlgorithms
open ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A scaled copy of the graph `Y = X`.  Its obstruction has enough degree to force extension
centers while every regular fiber still lifts the same base-field message. -/
private def scaledGraph {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (m : ℕ) : CBivariate F :=
  CPolynomial.C ((CPolynomial.X : CPolynomial F) ^ m) *
    ((CPolynomial.X : CBivariate F) -
      CPolynomial.C (CPolynomial.X : CPolynomial F))

private def binaryDomain : Fin 2 ↪ Carrier ArtinSchreierCenterTests.Fixtures.f2 where
  toFun i := suppliedIndex 2 ArtinSchreierCenterTests.Fixtures.f2
    ⟨i.val, by
      rw [show ArtinSchreierCenterTests.Fixtures.f2.natDegree = 1 by
        rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]
        exact Polynomial.natDegree_X]
      omega⟩
  inj' := by
    intro i j h
    have hij := (suppliedIndex 2 ArtinSchreierCenterTests.Fixtures.f2).injective h
    apply Fin.ext
    simpa using congrArg Fin.val hij

private def binaryLargeDomain : Fin 4 ↪ Carrier ArtinSchreierCenterTests.Fixtures.f4 where
  toFun i := suppliedIndex 2 ArtinSchreierCenterTests.Fixtures.f4
    ⟨i.val, by rw [ArtinSchreierCenterTests.Fixtures.f4_degree]; omega⟩
  inj' := by
    intro i j h
    have hij := (suppliedIndex 2 ArtinSchreierCenterTests.Fixtures.f4).injective h
    apply Fin.ext
    simpa using congrArg Fin.val hij

private def oddDomain : Fin 2 ↪
    Carrier ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus where
  toFun i := suppliedIndex 3
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
      ⟨i.val, by
        rw [ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree]
        omega⟩
  inj' := by
    intro i j h
    have hij := (suppliedIndex 3
      ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus).injective h
    apply Fin.ext
    simpa using congrArg Fin.val hij

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Execute the base, binary-quadratic, and odd-quadratic paths through lifting and recovery. -/
def run : IO Unit := do
  let f2 := ArtinSchreierCenterTests.Fixtures.f2
  let binaryEquation : CBivariate (Carrier f2) := scaledGraph 1
  let binaryObstruction := RegularCenterObstruction.obstruction binaryEquation
  check "binary scaled-graph obstruction did not request three centers" <|
    binaryObstruction.natDegree + 1 == 3
  check "binary transport did not choose the Artin-Schreier branch" <|
    (SuppliedCenters.suppliedRun 2 f2 (binaryObstruction.natDegree + 1)).branch ==
      .binaryQuadratic
  check "binary quadratic transport failed base-coefficient recovery" <|
    run? 2 f2 binaryEquation binaryObstruction binaryDomain binaryDomain
      2 2 == some [[1, 0]]
  let f4 := ArtinSchreierCenterTests.Fixtures.f4
  let binaryLargeEquation : CBivariate (Carrier f4) := scaledGraph 2
  let binaryLargeObstruction := RegularCenterObstruction.obstruction binaryLargeEquation
  check "large binary transport did not choose the Artin-Schreier branch" <|
    (SuppliedCenters.suppliedRun 2 f4
      (binaryLargeObstruction.natDegree + 1)).branch == .binaryQuadratic
  check "large binary transport failed with n > p and k > p" <|
    run? 2 f4 binaryLargeEquation binaryLargeObstruction binaryLargeDomain binaryLargeDomain
      3 3 == some [[0, 1, 0]]
  let f9 := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
  let oddEquation : CBivariate (Carrier f9) := scaledGraph 5
  let oddObstruction := RegularCenterObstruction.obstruction oddEquation
  check "odd scaled-graph obstruction did not exceed F9" <|
    9 < oddObstruction.natDegree + 1 && oddObstruction.natDegree + 1 ≤ 81
  check "odd transport did not choose the Euler quadratic branch" <|
    (SuppliedCenters.suppliedRun 3 f9 (oddObstruction.natDegree + 1)).branch == .oddQuadratic
  check "odd quadratic transport failed base-coefficient recovery" <|
    run? 3 f9 oddEquation oddObstruction oddDomain oddDomain 2 2 ==
      some [[1, 0]]
  let baseEquation : CBivariate (Carrier f9) := scaledGraph 0
  let baseObstruction := RegularCenterObstruction.obstruction baseEquation
  check "base transport unexpectedly requested an extension" <|
    (SuppliedCenters.suppliedRun 3 f9 (baseObstruction.natDegree + 1)).branch == .base
  check "base transport failed coefficient recovery" <|
    run? 3 f9 baseEquation baseObstruction oddDomain oddDomain 2 2 ==
      some [[1, 0]]

example {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (T : CBivariate F) : (CBivariate.toOrdinaryCMv T).degreeOf 1 = T.natDegree :=
  degreeOf_one_toOrdinaryCMv T

#print axioms degreeOf_one_toOrdinaryCMv
#print axioms toPoly_mapBivariate
#print axioms solution_mapRegularEquation
#print axioms runOver_exact
#print axioms run?_exact

end SuppliedTransportTests
