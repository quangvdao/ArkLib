/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.EffectivePolynomialBasis
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-! Generic consumers and runtime regressions for supplied-field operational adapters. -/

namespace EffectiveFieldTests

open ArkLib.FiniteField.ExplicitConstruction

/-- A consumer sees only field operations and the operational package. -/
def check {p : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) (count : Nat) (hcount : count ≤ F.index.cardinality) : IO Unit := do
  let _ : DecidableEq K := instDecidableEqOfLawfulBEq
  let values := F.elementPrefix count hcount
  unless values.length == count && decide values.Nodup do
    throw (IO.userError "effective field prefix length or uniqueness failed")
  let prepared := F.prepareInverseFrobenius ()
  for a in values do
    unless F.unindex (F.elementIndex a) == a do
      throw (IO.userError "effective field coordinate round trip failed")
    unless prepared.inverseFrobenius a ^ p == a do
      throw (IO.userError "effective field inverse Frobenius failed")
    unless a + 0 == a && a * 1 == a && (a == 0 || a / a == 1) do
      throw (IO.userError "effective field arithmetic failed")

example {p : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) : Nat.card K = p ^ F.degree := F.cardinality

example {p : Nat} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) (a : K) :
    (F.prepareInverseFrobenius ()).inverseFrobenius a ^ p = a :=
  (F.prepareInverseFrobenius ()).inverseFrobenius_pow a

/-- Exercise prime, binary extension, and odd extension presentations through the same consumer. -/
def run : IO Unit := do
  check (effectivePrimeField 2) 2 (by decide)
  check (effectivePrimeField 2) 0 (by decide)
  let binary := effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus
  have hb : binary.index.cardinality = 4 := by
    change 2 ^ PolynomialBasisFrobeniusTests.Binary.modulus.natDegree = 4
    simp [PolynomialBasisFrobeniusTests.Binary.modulus_degree]
  check binary 3 (by rw [hb]; decide)
  check binary 4 (by rw [hb])
  let ternary := effectivePolynomialBasis 3
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
  have ht : ternary.index.cardinality = 9 := by
    change 3 ^ ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus.natDegree = 9
    simp [ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree]
  check ternary 4 (by rw [ht]; decide)
  check ternary 9 (by rw [ht])

#print axioms EffectiveField.cardinality
#print axioms EffectiveField.primeEmbedding_injective
#print axioms effectivePolynomialBasis

end EffectiveFieldTests
