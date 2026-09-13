/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveRelativeQuotient
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveField

/-! Relative quotient consumers over an actual binary extension base. -/

namespace EffectiveRelativeQuotientTests

open ArkLib.FiniteField.ExplicitConstruction CompPoly CompPoly.CPolynomial

abbrev F4 := Carrier PolynomialBasisFrobeniusTests.Binary.modulus

/-- A relative degree-one quotient still has non-prime base coefficients. -/
abbrev linearModulus : CPolynomial F4 := X

instance : Fact linearModulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

instance : Fact (Irreducible linearModulus.toPoly) := ⟨by
  rw [CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

/-- The extension is supplied over F4; no absolute polynomial conversion occurs. -/
def field : EffectiveField 2 (Carrier linearModulus) :=
  effectiveRelativeQuotient
    (effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus) linearModulus

theorem field_cardinality : field.index.cardinality = 4 := by
  change (2 ^ PolynomialBasisFrobeniusTests.Binary.modulus.natDegree) ^
    linearModulus.natDegree = 4
  rw [PolynomialBasisFrobeniusTests.Binary.modulus_degree]
  have hd : linearModulus.natDegree = 1 := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]
    exact Polynomial.natDegree_X
  simp [hd]

/-- A genuine degree-two extension over the non-prime base F4. -/
abbrev quadraticModulus : CPolynomial F4 :=
  X ^ 2 + X + C (canonical PolynomialBasisFrobeniusTests.Binary.modulus X)

instance : Fact quadraticModulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [quadraticModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  convert Polynomial.monic_X_pow_add (n := 2)
    (p := Polynomial.X + Polynomial.C
      (canonical PolynomialBasisFrobeniusTests.Binary.modulus X))
    (by rw [Polynomial.degree_X_add_C]; decide) using 1
  ring⟩

theorem quadraticModulus_degree : quadraticModulus.natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [quadraticModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.natDegree_quadratic (R := F4)
    (a := 1) (b := 1)
    (c := canonical PolynomialBasisFrobeniusTests.Binary.modulus X) one_ne_zero)

/-- Certified coordinate enumeration is used only as this small test's independent oracle. -/
def baseIndex : Fin 4 ≃ F4 :=
  (finCongr (by simp [PolynomialBasisFrobeniusTests.Binary.modulus_degree])).trans
    (suppliedIndex 2 PolynomialBasisFrobeniusTests.Binary.modulus)

theorem quadraticModulus_no_root :
    ∀ i : Fin 4, CPolynomial.eval (baseIndex i) quadraticModulus ≠ 0 := by decide +kernel

instance : Fact (Irreducible quadraticModulus.toPoly) := ⟨by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    have hz := (Polynomial.mem_roots' (p := quadraticModulus.toPoly)).mp ha
    have hno := quadraticModulus_no_root (baseIndex.symm a)
    rw [baseIndex.apply_symm_apply, CPolynomial.eval_toPoly] at hno
    exact hno hz.2
  · rw [← CPolynomial.natDegree_toPoly, quadraticModulus_degree]
  · rw [← CPolynomial.natDegree_toPoly, quadraticModulus_degree]
    decide⟩

/-- The coefficient twist must be nontrivial on at least one tested base element. -/
def run : IO Unit := do
  EffectiveFieldTests.check field 4 (by rw [field_cardinality])
  let extension := effectiveRelativeQuotient
    (effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus) quadraticModulus
  have hext : extension.index.cardinality = 16 := by
    change (2 ^ PolynomialBasisFrobeniusTests.Binary.modulus.natDegree) ^
      quadraticModulus.natDegree = 16
    simp [PolynomialBasisFrobeniusTests.Binary.modulus_degree, quadraticModulus_degree]
  EffectiveFieldTests.check extension 5 (by rw [hext]; decide)
  EffectiveFieldTests.check extension 16 (by rw [hext])
  let base := effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus
  let roots := base.prepareInverseFrobenius ()
  let theta := canonical PolynomialBasisFrobeniusTests.Binary.modulus CPolynomial.X
  unless roots.inverseFrobenius theta != theta do
    throw (IO.userError "relative Frobenius test did not exercise non-prime coefficient twisting")
  let lifted := embedding linearModulus theta
  let relativeRoots := field.prepareInverseFrobenius ()
  unless relativeRoots.inverseFrobenius lifted ==
      embedding linearModulus (roots.inverseFrobenius theta) do
    throw (IO.userError "relative inverse Frobenius did not respect the base embedding")

#print axioms effectiveRelativeQuotient_inverseFrobenius_embed
#print axioms effectiveRelativeQuotient
#print axioms RelativeFrobenius.inverseFrobenius_pow

end EffectiveRelativeQuotientTests
