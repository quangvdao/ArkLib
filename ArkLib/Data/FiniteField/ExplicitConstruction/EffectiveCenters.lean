/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveRelativeQuotient
public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedCenters

/-!
# Base and quadratic center construction for effective supplied fields

The existing dispatcher scans Euler nonsquares in odd characteristic and trace-one
parameters in characteristic two. Its actual selected modulus is interpreted in
the existing relative quotient representation, with staged inverse Frobenius.
Base capacity is checked before either scan; requests beyond quadratic capacity
retain the explicit unsupported-capacity outcome.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction.EffectiveCenters

open CompPoly CompPoly.CPolynomial

variable {p : Nat} {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Execute base, Euler, or Artin--Schreier dispatch directly from operational data. -/
def run (base : EffectiveField p E) (count : Nat) :
    SuppliedCenters.Result E p base.index.cardinality count base.degree :=
  letI : DecidableEq E := instDecidableEqOfLawfulBEq
  letI : Fact p.Prime := ⟨base.prime⟩
  letI := base.characteristic
  SuppliedCenters.run p base.index.cardinality base.degree count
    base.index.equivFin base.cardinality_eq

/-- Sufficient base capacity takes precedence in every characteristic. -/
theorem run_base_iff (base : EffectiveField p E) (count : Nat) :
    (run base count).branch = .base ↔ count ≤ base.index.cardinality := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  exact SuppliedCenters.run_base_iff _ _ _ _ _ _

/-- The odd branch executes exactly when its capacity and characteristic guards hold. -/
theorem run_odd_iff (base : EffectiveField p E) (count : Nat) :
    (run base count).branch = .oddQuadratic ↔
      p ≠ 2 ∧ base.index.cardinality < count ∧ count ≤ base.index.cardinality ^ 2 := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  exact SuppliedCenters.run_oddQuadratic_iff _ _ _ _ _ _

/-- Binary fields use the trace-one quadratic branch rather than an odd-field fallback. -/
theorem run_binary_iff (base : EffectiveField p E) (count : Nat) :
    (run base count).branch = .binaryQuadratic ↔
      p = 2 ∧ base.index.cardinality < count ∧ count ≤ base.index.cardinality ^ 2 := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  exact SuppliedCenters.run_binaryQuadratic_iff _ _ _ _ _ _

/-- The generic dispatcher succeeds exactly through quadratic capacity. -/
theorem run_hasCenters_iff (base : EffectiveField p E) (count : Nat) :
    (run base count).HasCenters ↔ count ≤ base.index.cardinality ^ 2 := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  exact SuppliedCenters.run_hasCenters_iff _ _ _ _ _ _

/-- The indexed Euler scan whose first successful parameter is used by dispatch. -/
def oddParameter? (base : EffectiveField p E) : Option E :=
  letI : DecidableEq E := instDecidableEqOfLawfulBEq
  OddCenters.nonsquare? base.index.cardinality base.index.equivFin

/-- An odd result retains the exact parameter returned by the existing Euler scan. -/
theorem run_odd_parameter (base : EffectiveField p E) (count : Nat)
    (data : OddCenters.QuadraticData E base.index.cardinality count)
    (h : run base count = .oddQuadratic data) :
    oddParameter? base = some data.parameter := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact p.Prime := ⟨base.prime⟩
  let := base.characteristic
  unfold run SuppliedCenters.run at h
  split at h
  · contradiction
  · split at h
    · split at h
      · contradiction
      · cases h
        unfold oddParameter? OddCenters.certifiedNonsquare
        dsimp only
        split
        · assumption
        · contradiction
    · contradiction

/-- The Euler-selected equation, stored using the supplied field's lawful equality instance. -/
def oddModulus {q count : Nat} (data : OddCenters.QuadraticData E q count) : CPolynomial E :=
  X ^ 2 - C data.parameter

instance oddModulusMonic {q count : Nat} (data : OddCenters.QuadraticData E q count) :
    Fact (oddModulus data).monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [oddModulus, CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_sub_C _ (by decide)⟩

instance oddModulusIrreducible {q count : Nat} (data : OddCenters.QuadraticData E q count) :
    Fact (Irreducible (oddModulus data).toPoly) := ⟨by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  simpa only [oddModulus, OddCenters.QuadraticData.modulus, CPolynomial.toPoly_sub,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly] using
      data.modulus_irreducible⟩

theorem oddModulus_degree {q count : Nat} (data : OddCenters.QuadraticData E q count) :
    (oddModulus data).natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [oddModulus, CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.natDegree_X_pow_sub_C

/-- The actual Euler-selected quadratic becomes a reusable effective field. -/
def oddField (base : EffectiveField p E) {count : Nat}
    (data : OddCenters.QuadraticData E base.index.cardinality count) :
    EffectiveField p (Carrier (oddModulus data)) :=
  effectiveRelativeQuotient base (oddModulus data)

/-- Base-field embedding into the computed odd quotient. -/
def oddEmbedding {q count : Nat} (data : OddCenters.QuadraticData E q count) :
    E →+* Carrier (oddModulus data) := embedding (oddModulus data)

theorem oddEmbedding_injective {q count : Nat} (data : OddCenters.QuadraticData E q count) :
    Function.Injective (oddEmbedding data) := RingHom.injective _

/-- Exactly the requested mixed-radix prefix in the computed odd quadratic. -/
def oddPrefix (base : EffectiveField p E) {count : Nat}
    (data : OddCenters.QuadraticData E base.index.cardinality count) :
    List (Carrier (oddModulus data)) :=
  (oddField base data).elementPrefix count (by
    change count ≤ base.index.cardinality ^ (oddModulus data).natDegree
    rw [oddModulus_degree]
    exact data.capacity)

@[simp] theorem oddPrefix_length (base : EffectiveField p E) {count : Nat}
    (data : OddCenters.QuadraticData E base.index.cardinality count) :
    (oddPrefix base data).length = count := EffectiveField.prefix_length _ _ _

theorem oddPrefix_nodup (base : EffectiveField p E) {count : Nat}
    (data : OddCenters.QuadraticData E base.index.cardinality count) :
    (oddPrefix base data).Nodup := EffectiveField.prefix_nodup _ _ _

section Binary

variable [CharP E 2]

/-- The indexed trace-one scan whose successful parameter is used by binary dispatch. -/
def binaryParameter? (base : EffectiveField 2 E) : Option E :=
  letI : DecidableEq E := instDecidableEqOfLawfulBEq
  ArtinSchreierCenters.traceOne? base.degree
    (ArtinSchreierCenters.traceIndex base.index.equivFin base.cardinality_eq)

/-- A binary result retains the exact first trace-one parameter from the executed scan. -/
theorem run_binary_parameter (base : EffectiveField 2 E) (count : Nat)
    (data : ArtinSchreierCenters.QuadraticData E base.index.cardinality count base.degree)
    (h : run base count = .binaryQuadratic inferInstance base.cardinality_eq data) :
    binaryParameter? base = some data.parameter := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  let : Fact (Nat.Prime 2) := ⟨base.prime⟩
  unfold run SuppliedCenters.run at h
  split at h
  · contradiction
  · split at h
    · cases h
      unfold binaryParameter? ArtinSchreierCenters.certifiedTraceOne
      dsimp only
      split
      · assumption
      · contradiction
    · contradiction

/-- The trace-one-selected equation, with no conversion to an absolute basis. -/
def binaryModulus {q count e : Nat} (data : ArtinSchreierCenters.QuadraticData E q count e) :
    CPolynomial E := X ^ 2 + X + C data.parameter

instance binaryModulusMonic {q count e : Nat}
    (data : ArtinSchreierCenters.QuadraticData E q count e) :
    Fact (binaryModulus data).monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [binaryModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.isMonicOfDegree_add_add_two (1 : E) data.parameter).monic⟩

instance binaryModulusIrreducible {q count e : Nat}
    (data : ArtinSchreierCenters.QuadraticData E q count e) :
    Fact (Irreducible (binaryModulus data).toPoly) := ⟨by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  simpa only [binaryModulus, ArtinSchreierCenters.QuadraticData.modulus,
    CPolynomial.toPoly_add, CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly] using data.modulus_irreducible⟩

theorem binaryModulus_degree {q count e : Nat}
    (data : ArtinSchreierCenters.QuadraticData E q count e) :
    (binaryModulus data).natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [binaryModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.natDegree_quadratic (R := E)
    (a := 1) (b := 1) (c := data.parameter) one_ne_zero)

/-- The actual trace-one quadratic becomes a reusable effective field. -/
def binaryField (base : EffectiveField p E) {count : Nat}
    (data : ArtinSchreierCenters.QuadraticData E base.index.cardinality count base.degree) :
    EffectiveField p (Carrier (binaryModulus data)) :=
  effectiveRelativeQuotient base (binaryModulus data)

/-- Base-field embedding into the computed trace-one quotient. -/
def binaryEmbedding {q count e : Nat}
    (data : ArtinSchreierCenters.QuadraticData E q count e) :
    E →+* Carrier (binaryModulus data) := embedding (binaryModulus data)

theorem binaryEmbedding_injective {q count e : Nat}
    (data : ArtinSchreierCenters.QuadraticData E q count e) :
    Function.Injective (binaryEmbedding data) := RingHom.injective _

/-- Exactly the requested mixed-radix prefix in the computed binary quadratic. -/
def binaryPrefix (base : EffectiveField p E) {count : Nat}
    (data : ArtinSchreierCenters.QuadraticData E base.index.cardinality count base.degree) :
    List (Carrier (binaryModulus data)) :=
  (binaryField base data).elementPrefix count (by
    change count ≤ base.index.cardinality ^ (binaryModulus data).natDegree
    rw [binaryModulus_degree]
    exact data.capacity)

@[simp] theorem binaryPrefix_length (base : EffectiveField p E) {count : Nat}
    (data : ArtinSchreierCenters.QuadraticData E base.index.cardinality count base.degree) :
    (binaryPrefix base data).length = count := EffectiveField.prefix_length _ _ _

theorem binaryPrefix_nodup (base : EffectiveField p E) {count : Nat}
    (data : ArtinSchreierCenters.QuadraticData E base.index.cardinality count base.degree) :
    (binaryPrefix base data).Nodup := EffectiveField.prefix_nodup _ _ _

end Binary

end ArkLib.FiniteField.ExplicitConstruction.EffectiveCenters
