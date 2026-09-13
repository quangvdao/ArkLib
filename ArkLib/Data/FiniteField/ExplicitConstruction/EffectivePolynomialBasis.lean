/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveField
public import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-! # Effective supplied-field adapter for the existing polynomial-basis representation -/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Retain the supplied quotient's arithmetic, little-endian index, and computed
inverse Frobenius implementation behind the generic operational interface. -/
def effectivePolynomialBasis (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic]
    [Fact (Irreducible f.toPoly)] : EffectiveField p (Carrier f) :=
  {
    prime := Fact.out
    characteristic := inferInstance
    degree := f.natDegree
    degree_pos := suppliedDegree_pos p f
    index := {
      cardinality := p ^ f.natDegree
      one_lt_cardinality :=
        Nat.one_lt_pow (Nat.ne_of_gt (suppliedDegree_pos p f)) (Fact.out : p.Prime).one_lt
      decode := suppliedIndex p f
      encode := (suppliedIndex p f).symm
      decode_encode := (suppliedIndex p f).apply_symm_apply
      encode_decode := (suppliedIndex p f).symm_apply_apply }
    cardinality_eq := rfl
    primeEmbedding := embedding f
    prepareInverseFrobenius := fun _ =>
      let prepared := prepareInverseFrobenius p f
      { inverseFrobenius := prepared.apply p f
        inverseFrobenius_pow a := by
          rw [prepareInverseFrobenius_apply]
          exact inverseFrobenius_pow p f a } }

/-- The adapter computes exactly the previous prefix operation. -/
theorem effectivePolynomialBasis_prefix (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic]
    [Fact (Irreducible f.toPoly)] (count : Nat) (hcount : count ≤ p ^ f.natDegree) :
    (effectivePolynomialBasis p f).elementPrefix count hcount =
      suppliedCenterPrefix p f count hcount := rfl

/-- The adapter retains the actual stored quotient embedding. -/
theorem effectivePolynomialBasis_embedding (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic]
    [Fact (Irreducible f.toPoly)] :
    (effectivePolynomialBasis p f).primeEmbedding = embedding f := rfl

/-- Prepared callback evaluation agrees with the existing polynomial-basis algorithm. -/
theorem effectivePolynomialBasis_inverseFrobenius (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic]
    [Fact (Irreducible f.toPoly)] (a : Carrier f) :
    ((effectivePolynomialBasis p f).prepareInverseFrobenius ()).inverseFrobenius a =
      inverseFrobenius p f a :=
  prepareInverseFrobenius_apply p f a

end ArkLib.FiniteField.ExplicitConstruction
