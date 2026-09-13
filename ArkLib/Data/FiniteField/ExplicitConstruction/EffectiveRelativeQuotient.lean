/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.RelativeFrobenius

/-!
# Effective relative quotient extensions

A supplied monic irreducible polynomial over an already effective base field
extends that presentation in the relative coefficient basis. Base arithmetic,
quotient arithmetic, and radix indexing retain their existing implementations.
Frobenius preparation is staged: when invoked, it prepares the base callback
once and retains it during coefficient twisting and relative gcd preprocessing.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

variable {p : Nat} {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable (base : EffectiveField p E) (f : CompPoly.CPolynomial E)
variable [Fact f.monic] [Fact (Irreducible f.toPoly)]

omit [Fact f.monic] in
/-- An irreducible supplied relative modulus has positive degree. -/
theorem relativeDegree_pos : 0 < f.natDegree := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_irreducible Fact.out)

/-- Reuse relative quotient coordinates and construct the coefficient-twisted
inverse Frobenius callback only when preparation is requested. -/
def effectiveRelativeQuotient : EffectiveField p (Carrier f) where
  prime := base.prime
  characteristic := by
    let := base.characteristic
    infer_instance
  degree := base.degree * f.natDegree
  degree_pos := Nat.mul_pos base.degree_pos (relativeDegree_pos f)
  index := {
    cardinality := base.index.cardinality ^ f.natDegree
    one_lt_cardinality :=
      Nat.one_lt_pow (Nat.ne_of_gt (relativeDegree_pos f)) base.index.one_lt_cardinality
    decode := polynomialBasisIndex f base.index
    encode := (polynomialBasisIndex f base.index).symm
    decode_encode := (polynomialBasisIndex f base.index).apply_symm_apply
    encode_decode := (polynomialBasisIndex f base.index).symm_apply_apply }
  cardinality_eq := by
    change base.index.cardinality ^ f.natDegree = p ^ (base.degree * f.natDegree)
    rw [base.cardinality_eq, pow_mul]
  primeEmbedding := (embedding f).comp base.primeEmbedding
  prepareInverseFrobenius := fun _ =>
    letI : Fact p.Prime := ⟨base.prime⟩
    letI := base.characteristic
    letI : Finite E := Finite.of_equiv (Fin base.index.cardinality) base.index.equivFin
    let roots := base.prepareInverseFrobenius ()
    let prepared := RelativeFrobenius.prepareInverseFrobenius p roots f
    { inverseFrobenius := prepared.apply p roots f
      inverseFrobenius_pow a := by
        rw [RelativeFrobenius.prepareInverseFrobenius_apply]
        exact RelativeFrobenius.inverseFrobenius_pow p roots f a }

/-- The absolute degree is the product of the supplied base and relative degrees. -/
theorem effectiveRelativeQuotient_degree :
    (effectiveRelativeQuotient base f).degree = base.degree * f.natDegree := rfl

/-- Prime elements are embedded through the base field and the actual quotient map. -/
theorem effectiveRelativeQuotient_embedding :
    (effectiveRelativeQuotient base f).primeEmbedding =
      (embedding f).comp base.primeEmbedding := rfl

/-- The extension prefix is exactly the existing relative mixed-radix prefix. -/
theorem effectiveRelativeQuotient_prefix (count : Nat)
    (hcount : count ≤ base.index.cardinality ^ f.natDegree) :
    (effectiveRelativeQuotient base f).elementPrefix count hcount =
      indexedPrefix (polynomialBasisIndex f base.index) count hcount := rfl

/-- The computed relative root of an embedded base element is exactly the
embedding of its computed base root. -/
theorem effectiveRelativeQuotient_inverseFrobenius_embed (a : E) :
    ((effectiveRelativeQuotient base f).prepareInverseFrobenius ()).inverseFrobenius
        (embedding f a) =
      embedding f ((base.prepareInverseFrobenius ()).inverseFrobenius a) := by
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  apply frobenius_inj (Carrier f) p
  simp only [frobenius_def]
  rw [((effectiveRelativeQuotient base f).prepareInverseFrobenius ()).inverseFrobenius_pow,
    ← map_pow, (base.prepareInverseFrobenius ()).inverseFrobenius_pow]

end ArkLib.FiniteField.ExplicitConstruction
