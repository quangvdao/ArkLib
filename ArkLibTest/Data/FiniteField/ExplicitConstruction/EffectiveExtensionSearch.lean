/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveExtensionSearch
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveField

/-! Real consumers of constructed effective fields and least-degree boundary regressions. -/

namespace EffectiveExtensionSearchTests

open ArkLib.FiniteField.ExplicitConstruction

/-- A client discharges effective-field capacity from the returned construction certificates. -/
def checkExtension {p : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (base : EffectiveField p K) (requested expectedDegree : Nat) : IO Unit := do
  match hrun : EffectiveExtensionSearch.run base requested with
  | .base _ => throw (IO.userError "extension test unexpectedly returned its base field")
  | .searchFailure _ => throw (IO.userError "complete extension construction returned failure")
  | .extension data =>
    have payload := EffectiveExtensionSearch.run_payload base requested data hrun
    unless data.degree == expectedDegree &&
        (data.effectiveCenters base payload.2.1).length == requested do
      throw (IO.userError "least-degree effective extension or requested prefix disagreed")
    unless firstIrreducible? base.index data.degree == some data.modulus do
      throw (IO.userError "effective extension lost first-success search provenance")
    let field := data.effectiveField base
    EffectiveFieldTests.check field data.requested (data.effectiveField_capacity base payload.2.1)

/-- Cover empty/base requests, exact power boundaries, and the next-degree jump. -/
def run : IO Unit := do
  let binary := effectivePrimeField 2
  unless (EffectiveExtensionSearch.run binary 0).branch == .base &&
      (EffectiveExtensionSearch.run binary 2).branch == .base do
    throw (IO.userError "binary base capacity did not bypass extension search")
  checkExtension binary 3 2
  checkExtension binary 4 2
  checkExtension binary 5 3
  let supplied := effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus
  checkExtension supplied 5 2
  checkExtension supplied 16 2
  checkExtension supplied 17 3
  unless leastDegree 4 17 == 3 do
    throw (IO.userError "q²+1 did not increase the least sufficient degree")

#print axioms EffectiveExtensionSearch.run_no_failure
#print axioms EffectiveExtensionSearch.run_provenance
#print axioms SearchResult.effectiveField_least

end EffectiveExtensionSearchTests
