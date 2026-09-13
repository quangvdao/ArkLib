/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveRelativeQuotient
public import ArkLib.Data.FiniteField.ExplicitConstruction.ExtensionSearch

/-!
# Least-degree extension search for effective supplied fields

This adapter reuses the existing complete monic-polynomial search. The base
branch precedes enumeration. On the extension branch the base cardinality is
strictly below the requested bound, and the computed degree is the least positive
sufficient degree. The actual searched quotient gains staged relative inverse
Frobenius through `effectiveRelativeQuotient`, so it is reusable as a supplied base.
No fast-complexity claim is attached to this bounded exhaustive search.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

namespace EffectiveExtensionSearch

variable {p : Nat} {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Execute the existing bounded search using the supplied canonical index. -/
def run (base : EffectiveField p E) (requested : Nat) :
    ExtensionSearchResult E base.index.cardinality requested :=
  ExplicitConstruction.run base.index requested

/-- Sufficient base capacity bypasses all modulus search. -/
theorem run_base_iff (base : EffectiveField p E) (requested : Nat) :
    (run base requested).branch = .base ↔ requested ≤ base.index.cardinality :=
  ExplicitConstruction.run_base_iff base.index requested

/-- Search is performed only with base cardinality below the requested bound. -/
theorem run_extension_iff (base : EffectiveField p E) (requested : Nat) :
    (run base requested).branch = .extension ↔ base.index.cardinality < requested :=
  ExplicitConstruction.run_extension_iff base.index requested

/-- The complete positive-degree search cannot produce its failure constructor. -/
theorem run_no_failure (base : EffectiveField p E) (requested : Nat) :
    (run base requested).branch ≠ .searchFailure :=
  run_searchFailure_ne base.index requested

/-- A returned extension retains the exact request, base cardinality, and least degree. -/
theorem run_payload (base : EffectiveField p E) (requested : Nat) (data : SearchResult E)
    (h : run base requested = .extension data) :
    data.requested = requested ∧ data.baseCardinality = base.index.cardinality ∧
      data.degree = leastDegree base.index.cardinality requested :=
  run_extension_payload base.index requested data h

/-- The returned modulus is the actual first successful tested candidate. -/
theorem run_provenance (base : EffectiveField p E) (requested : Nat) (data : SearchResult E)
    (h : run base requested = .extension data) :
    firstIrreducible? base.index data.degree = some data.modulus := by
  unfold run ExplicitConstruction.run at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · cases h
      assumption

end EffectiveExtensionSearch

namespace SearchResult

variable {p : Nat} {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable (data : SearchResult E) (base : EffectiveField p E)

/-- The executed search's quotient, equipped with the generic operational interface.
Frobenius preparation remains deferred until explicitly requested. -/
def effectiveField : EffectiveField p data.FieldType := by
  letI : Fact data.modulus.monic := ⟨data.monic⟩
  letI : Fact (Irreducible data.modulus.toPoly) := ⟨data.irreducible⟩
  exact effectiveRelativeQuotient base data.modulus

/-- The searched degree controls the effective extension's absolute degree. -/
theorem effectiveField_degree :
    (data.effectiveField base).degree = base.degree * data.degree := by
  change base.degree * data.modulus.natDegree = base.degree * data.degree
  rw [CompPoly.CPolynomial.natDegree_toPoly, data.degree_eq]

/-- Actual search capacity certifies a prefix in the adapted field. -/
theorem effectiveField_capacity (hcard : data.baseCardinality = base.index.cardinality) :
    data.requested ≤ (data.effectiveField base).index.cardinality := by
  change data.requested ≤ base.index.cardinality ^ data.modulus.natDegree
  rw [CompPoly.CPolynomial.natDegree_toPoly, data.degree_eq, ← hcard]
  exact data.sufficient

/-- Only the requested centers are materialized after construction. -/
def effectiveCenters (hcard : data.baseCardinality = base.index.cardinality) :
    List data.FieldType :=
  (data.effectiveField base).elementPrefix data.requested (data.effectiveField_capacity base hcard)

@[simp] theorem effectiveCenters_length
    (hcard : data.baseCardinality = base.index.cardinality) :
    (data.effectiveCenters base hcard).length = data.requested :=
  EffectiveField.prefix_length _ _ _

theorem effectiveCenters_nodup (hcard : data.baseCardinality = base.index.cardinality) :
    (data.effectiveCenters base hcard).Nodup := EffectiveField.prefix_nodup _ _ _

/-- Cardinality and minimality refer to the actual constructed effective field. -/
theorem effectiveField_least (hcard : data.baseCardinality = base.index.cardinality) :
    Nat.card data.FieldType = base.index.cardinality ^ data.degree ∧
      ∀ e, 0 < e → data.requested ≤ base.index.cardinality ^ e → data.degree ≤ e := by
  refine ⟨data.cardinality base.index hcard, ?_⟩
  simpa [hcard] using data.least

/-- The supplied prime field embeds through the existing searched-quotient embedding. -/
theorem effectiveField_primeEmbedding :
    (data.effectiveField base).primeEmbedding = data.embedding.comp base.primeEmbedding := rfl

end SearchResult

end ArkLib.FiniteField.ExplicitConstruction
