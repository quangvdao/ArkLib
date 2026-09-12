/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedCenters
import ArkLibTest.Data.FiniteField.ExplicitConstruction.ArtinSchreierCenters
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasis

/-! Runtime checks for all supplied-field center-dispatch outcomes. -/

namespace SuppliedCenterTests

open ArkLib.FiniteField.ExplicitConstruction CompPoly
  ArkLib.PolynomialQuotient
open ArkLib.FiniteField.ExplicitConstruction.SuppliedCenters

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example :
    (suppliedRun 2 ArtinSchreierCenterTests.Fixtures.f2 3).branch = .binaryQuadratic := by
  apply (suppliedRun_binaryQuadratic_iff 2 ArtinSchreierCenterTests.Fixtures.f2 3).mpr
  change 2 = 2 ∧ 2 ^ 1 < 3 ∧ 3 ≤ (2 ^ 1) ^ 2
  decide

example :
    (suppliedRun 3 ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus 10).branch =
      .oddQuadratic := by
  apply (suppliedRun_oddQuadratic_iff 3
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus 10).mpr
  rw [ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree]
  decide

/-- Execute base, odd quadratic, binary quadratic, and insufficient-capacity outcomes. -/
def run : IO Unit := do
  let f2 := ArtinSchreierCenterTests.Fixtures.f2
  let index2 := suppliedIndex 2 f2
  unless (suppliedRun 2 f2 2).branch == .base do
    throw (IO.userError "unified dispatcher rejected exact supplied F2 base capacity")
  match suppliedRun 2 f2 3 with
  | .binaryQuadratic characteristic _ data =>
      let _ : CharP (Carrier f2) 2 := characteristic
      let values := data.centers index2
      unless values.length == 3 && decide values.Nodup do
        throw (IO.userError "unified dispatcher returned a bad F2-to-F4 prefix")
      let w : data.FieldType := ⟨0, 1⟩
      unless decide (w ^ 2 = data.embedding data.parameter + w) do
        throw (IO.userError "unified binary field lost its Artin-Schreier relation")
  | _ => throw (IO.userError "unified dispatcher missed the binary quadratic branch")
  unless (suppliedRun 2 f2 5).branch == .insufficientCapacity do
    throw (IO.userError "unified dispatcher accepted capacity above supplied F4")
  let f4 := ArtinSchreierCenterTests.Fixtures.f4
  let index4 := suppliedIndex 2 f4
  match suppliedRun 2 f4 5 with
  | .binaryQuadratic characteristic _ data =>
      let _ : CharP (Carrier f4) 2 := characteristic
      let values := data.centers index4
      unless values.length == 5 && decide values.Nodup &&
          (values[4]?).map QuadraticAlgebra.im == some (1 : Carrier f4) do
        throw (IO.userError "unified supplied F4-to-F16 coordinates failed")
  | _ => throw (IO.userError "unified dispatcher missed supplied F4 quadratic centers")
  let f9 := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
  let index9 := suppliedIndex 3 f9
  unless (suppliedRun 3 f9 9).branch == .base do
    throw (IO.userError "unified dispatcher rejected exact supplied F9 base capacity")
  let baseValues := suppliedCenterPrefix 3 f9 9 (by
    rw [ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree]
    decide)
  unless baseValues.length == 9 && decide baseValues.Nodup do
    throw (IO.userError "unified supplied F9 base prefix failed")
  match suppliedRun 3 f9 10 with
  | .oddQuadratic data =>
      let values := data.centers index9
      unless values.length == 10 && decide values.Nodup do
        throw (IO.userError "unified supplied F9-to-F81 prefix failed")
      let w : data.FieldType := ⟨0, 1⟩
      unless decide (w ^ 2 = data.embedding data.parameter) do
        throw (IO.userError "unified odd field lost its quadratic relation")
  | _ => throw (IO.userError "unified dispatcher missed the odd quadratic branch")
  unless (suppliedRun 3 f9 82).branch == .insufficientCapacity do
    throw (IO.userError "unified dispatcher accepted capacity above supplied F81")

#print axioms SuppliedCenters.run_oddQuadratic_iff
#print axioms SuppliedCenters.run_binaryQuadratic_iff
#print axioms SuppliedCenters.run_hasCenters_iff

end SuppliedCenterTests
