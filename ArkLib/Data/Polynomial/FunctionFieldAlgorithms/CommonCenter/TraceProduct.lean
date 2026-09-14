/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TracePresentation

/-!
# Assembly of local trace converses

The trace pairing on a product is the orthogonal sum of the two factor pairings. Together
with the residue coefficient-field theorem, this proves the converse for any explicitly
presented finite family of local factors and transports it through an algebra equivalence.
The empty product is included. Construction of a general Artin
algebra's decomposition and its coefficient fields remains a separate obligation.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

variable {K A B C : Type*} [Field K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]

/-- The product trace radical is exactly the product of the factor trace radicals. -/
theorem trace_radical_prod_iff [FiniteDimensional K A] [FiniteDimensional K B]
    (x : A × B) :
    (∀ y : A × B, Algebra.trace K (A × B) (x * y) = 0) ↔
      (∀ a : A, Algebra.trace K A (x.1 * a) = 0) ∧
      (∀ b : B, Algebra.trace K B (x.2 * b) = 0) := by
  constructor
  · intro h
    constructor
    · intro a
      simpa [Algebra.trace_prod_apply] using h (a, 0)
    · intro b
      simpa [Algebra.trace_prod_apply] using h (0, b)
  · rintro ⟨ha, hb⟩ y
    rw [Algebra.trace_prod_apply]
    simp only [Prod.fst_mul, Prod.snd_mul, ha, hb, add_zero]

/-- A pair is nilpotent exactly when both components are nilpotent; exponents may differ. -/
theorem nilpotent_pair_iff (x : A × B) :
    IsNilpotent x ↔ IsNilpotent x.1 ∧ IsNilpotent x.2 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, congrArg Prod.fst hn⟩, ⟨n, congrArg Prod.snd hn⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m + n, ?_⟩
    apply Prod.ext
    · change x.1 ^ (m + n) = 0
      rw [pow_add, hm, zero_mul]
    · change x.2 ^ (m + n) = 0
      rw [pow_add, hn, mul_zero]

/-- Binary assembly uses proved local converses, with no assumption on the product trace. -/
theorem trace_radical_prod_iff_nilpotent [FiniteDimensional K A] [FiniteDimensional K B]
    (hA : ∀ x : A, (∀ y : A, Algebra.trace K A (x * y) = 0) ↔ IsNilpotent x)
    (hB : ∀ x : B, (∀ y : B, Algebra.trace K B (x * y) = 0) ↔ IsNilpotent x)
    (x : A × B) :
    (∀ y : A × B, Algebra.trace K (A × B) (x * y) = 0) ↔ IsNilpotent x := by
  rw [trace_radical_prod_iff, hA, hB, nilpotent_pair_iff]

/-- An actual algebra decomposition transports both trace and nilpotence. -/
theorem trace_radical_transport (e : C ≃ₐ[K] A)
    (hA : ∀ x : A, (∀ y : A, Algebra.trace K A (x * y) = 0) ↔ IsNilpotent x)
    (x : C) : (∀ y : C, Algebra.trace K C (x * y) = 0) ↔ IsNilpotent x := by
  have htrace : (∀ y : C, Algebra.trace K C (x * y) = 0) ↔
      ∀ y : A, Algebra.trace K A (e x * y) = 0 := by
    constructor
    · intro h y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, Algebra.trace_eq_of_algEquiv e]
      exact h z
    · intro h y
      have hy := h (e y)
      rwa [← map_mul, Algebra.trace_eq_of_algEquiv e] at hy
  rw [htrace, hA]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, e.injective ?_⟩
    simpa using hn
  · exact fun h => h.map e.toAlgHom.toRingHom

/-- Split a finite product into its head and tail as an actual algebra equivalence. -/
def finProductSplit (n : ℕ) (D : Fin (n + 1) → Type*)
    [∀ i, CommRing (D i)] [∀ i, Algebra K (D i)] :
    (∀ i, D i) ≃ₐ[K] D 0 × (∀ i : Fin n, D i.succ) where
  toEquiv := (Fin.consEquiv D).symm
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Finite product assembly, including the empty product. Factor converses are the only
semantic inputs; the product trace identity is proved by binary trace decomposition. -/
theorem trace_radical_finProduct (n : ℕ) (D : Fin n → Type*)
    [∀ i, CommRing (D i)] [∀ i, Algebra K (D i)] [∀ i, FiniteDimensional K (D i)]
    (hD : ∀ i (x : D i), (∀ y : D i, Algebra.trace K (D i) (x * y) = 0) ↔ IsNilpotent x)
    (x : ∀ i, D i) :
    (∀ y : ∀ i, D i, Algebra.trace K (∀ i, D i) (x * y) = 0) ↔ IsNilpotent x := by
  induction n with
  | zero =>
    constructor
    · intro _
      exact ⟨1, Subsingleton.elim _ _⟩
    · intro hx y
      exact nilpotent_trace_mul_eq_zero hx y
  | succ n ih =>
    apply trace_radical_transport (finProductSplit n D)
    apply trace_radical_prod_iff_nilpotent (hD 0)
    exact ih (fun i => D i.succ) (fun i => hD i.succ)

/-- Explicit finite local-factor decomposition gives the trace-radical converse.
No perfectness, precomputed radical, or assumed trace-factorization identity is used. -/
theorem trace_radical_of_residue_factors (n : ℕ) (D L : Fin n → Type*)
    [∀ i, CommRing (D i)] [∀ i, Field (L i)]
    [∀ i, Algebra K (D i)] [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (D i)]
    [∀ i, IsScalarTower K (L i) (D i)]
    [∀ i, FiniteDimensional K (L i)] [∀ i, FiniteDimensional (L i) (D i)]
    [∀ i, Algebra.IsSeparable K (L i)]
    (P : ∀ i, ResidueCoefficientField (L := L i) (A := D i))
    (hlength : ∀ i, (Module.finrank (L i) (D i) : K) ≠ 0)
    (e : C ≃ₐ[K] (∀ i, D i)) (x : C) :
    (∀ y : C, Algebra.trace K C (x * y) = 0) ↔ IsNilpotent x := by
  let : ∀ i, FiniteDimensional K (D i) := fun i => Module.Finite.trans (L i) (D i)
  apply trace_radical_transport e
  exact trace_radical_finProduct n D (fun i => (P i).trace_radical_iff_nilpotent (hlength i))

variable {L₁ L₂ : Type*} [Field L₁] [Field L₂]
    [Algebra K L₁] [Algebra K L₂] [Algebra L₁ A] [Algebra L₂ B]
    [IsScalarTower K L₁ A] [IsScalarTower K L₂ B]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional L₁ A] [FiniteDimensional L₂ B]
    [Algebra.IsSeparable K L₁] [Algebra.IsSeparable K L₂]

/-- A two-factor local decomposition gives the converse from structural data only.
The trace formula and both local converses are derived, not supplied as hypotheses. -/
theorem trace_radical_of_two_residue_factors
    (P₁ : ResidueCoefficientField (L := L₁) (A := A))
    (P₂ : ResidueCoefficientField (L := L₂) (A := B))
    (h₁ : (Module.finrank L₁ A : K) ≠ 0) (h₂ : (Module.finrank L₂ B : K) ≠ 0)
    (e : C ≃ₐ[K] A × B) (x : C) :
    (∀ y : C, Algebra.trace K C (x * y) = 0) ↔ IsNilpotent x := by
  let : FiniteDimensional K A := Module.Finite.trans L₁ A
  let : FiniteDimensional K B := Module.Finite.trans L₂ B
  apply trace_radical_transport e
  exact trace_radical_prod_iff_nilpotent
    (P₁.trace_radical_iff_nilpotent h₁) (P₂.trace_radical_iff_nilpotent h₂)

end Polynomial.FunctionFieldAlgorithms.CommonCenter
