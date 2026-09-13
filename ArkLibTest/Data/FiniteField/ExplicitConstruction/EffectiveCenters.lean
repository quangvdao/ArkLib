/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveCenters
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveNormalBasis

/-! Characteristic-sensitive center dispatch and effective quotient consumer checks. -/

namespace EffectiveCentersTests

open ArkLib.FiniteField.ExplicitConstruction

/-- Every successful branch supplies actual arithmetic, embeddings, and distinct prefixes. -/
def check {p : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (base : EffectiveField p K) (count : Nat) (expected : SuppliedCenters.Branch) : IO Unit := do
  let result := EffectiveCenters.run base count
  unless result.branch == expected do
    throw (IO.userError "effective center dispatcher chose an unexpected characteristic branch")
  match result with
  | .base capacity =>
    EffectiveFieldTests.check base count capacity
  | .oddQuadratic data =>
    let field := EffectiveCenters.oddField base data
    unless (EffectiveCenters.oddPrefix base data).length == count do
      throw (IO.userError "odd quadratic prefix length disagreed")
    have hcap : count ≤ field.index.cardinality := by
      change count ≤ base.index.cardinality ^ (EffectiveCenters.oddModulus data).natDegree
      rw [EffectiveCenters.oddModulus_degree]
      exact data.capacity
    EffectiveFieldTests.check field count hcap
  | .binaryQuadratic characteristic _ data =>
    let _ : CharP K 2 := characteristic
    let field := EffectiveCenters.binaryField base data
    unless (EffectiveCenters.binaryPrefix base data).length == count do
      throw (IO.userError "binary quadratic prefix length disagreed")
    have hcap : count ≤ field.index.cardinality := by
      change count ≤ base.index.cardinality ^ (EffectiveCenters.binaryModulus data).natDegree
      rw [EffectiveCenters.binaryModulus_degree]
      exact data.capacity
    EffectiveFieldTests.check field count hcap
  | .insufficientCapacity _ _ => pure ()

/-- Preserve binary base/quadratic behavior and odd Euler construction at capacity endpoints. -/
def run : IO Unit := do
  check (effectivePrimeField 2) 0 .base
  check (effectivePrimeField 2) 2 .base
  check (effectivePrimeField 2) 3 .binaryQuadratic
  check (effectivePrimeField 2) 4 .binaryQuadratic
  check (effectivePrimeField 2) 5 .insufficientCapacity
  check (effectivePrimeField 3) 3 .base
  check (effectivePrimeField 3) 4 .oddQuadratic
  check (effectivePrimeField 3) 9 .oddQuadratic
  check (effectivePrimeField 3) 10 .insufficientCapacity
  check EffectiveNormalBasisTests.binaryCoordinates.effectiveField 5 .binaryQuadratic
  check EffectiveNormalBasisTests.binaryCoordinates.effectiveField 16 .binaryQuadratic

#print axioms EffectiveCenters.run_odd_parameter
#print axioms EffectiveCenters.run_binary_parameter
#print axioms EffectiveCenters.run_hasCenters_iff
#print axioms EffectiveCenters.oddModulusIrreducible
#print axioms EffectiveCenters.binaryModulusIrreducible
#print axioms EffectiveCenters.binaryPrefix_nodup

end EffectiveCentersTests
