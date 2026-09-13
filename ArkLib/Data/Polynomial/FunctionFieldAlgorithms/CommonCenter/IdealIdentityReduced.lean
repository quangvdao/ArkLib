/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityFinite
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Identity existence for reduced boundary algebras

An Artinian reduced commutative algebra has an identity on each ideal. A multiplicative
linear coordinate presentation transports this identity into the solver's finite equations;
the coefficients are derived from span membership. Thus exhaustive search cannot reject
such a presentation. Constructing the decoder's reduced quotient and its multiplication
presentation remains the responsibility of the caller.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity

/-- Every ideal of an Artinian reduced commutative ring has its own identity. -/
theorem ideal_identity_exists {A : Type*} [CommRing A] [IsArtinianRing A]
    [IsReduced A] (I : Ideal A) :
    ∃ e ∈ I, IsIdempotentElem e ∧ ∀ x ∈ I, e * x = x := by
  let : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  refine ⟨e, hI ▸ Ideal.mem_span_singleton_self e, he, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hI ▸ hx)
  calc
    e * (a * e) = a * (e * e) := by ac_rfl
    _ = a * e := by rw [he.eq]

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d m : ℕ}

/-- A faithful linear presentation of the multiplication table in an actual algebra. -/
structure AlgebraPresentation (table : MultiplicationTable K d) where
  /-- Every algebra element has unique coordinates. -/
  decode : Coordinates K d ≃ₗ[K] A
  /-- The supplied table computes algebra multiplication. -/
  map_multiply : ∀ x y, decode (multiply table x y) = decode x * decode y

/-- Associativity follows from the algebra presentation, without a coordinate axiom. -/
theorem AlgebraPresentation.associative {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (x y z : Coordinates K d) :
    multiply table (multiply table x y) z = multiply table x (multiply table y z) := by
  apply P.decode.injective
  simp only [P.map_multiply, mul_assoc]

/-- The generated coordinate space is an algebraic ideal under a valid presentation. -/
def AlgebraPresentation.generatedIdeal {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (c : Fin m → Coordinates K d) : Ideal A where
  carrier := {a | P.decode.symm a ∈ generatedSpace table c}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simpa using (generatedSpace table c).add_mem ha hb
  smul_mem' := by
    intro a b hb
    change P.decode.symm (a * b) ∈ generatedSpace table c
    have h : P.decode.symm (a * b) =
        multiply table (P.decode.symm a) (P.decode.symm b) := by
      apply P.decode.injective
      simp [P.map_multiply]
    rw [h]
    exact multiply_mem_of_mem table c P.associative _ _ hb

/-- The transported ideal is exactly the ideal of the supplied denominator elements. -/
theorem AlgebraPresentation.generatedIdeal_eq_span {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (c : Fin m → Coordinates K d) :
    P.generatedIdeal c = Ideal.span (Set.range fun l => P.decode (c l)) := by
  let I := Ideal.span (Set.range fun l => P.decode (c l))
  apply le_antisymm
  · intro a ha
    let S : Submodule K (Coordinates K d) :=
      (I.restrictScalars K).comap P.decode.toLinearMap
    have hc : ∀ l, c l ∈ S := fun l => Ideal.subset_span ⟨l, rfl⟩
    have hclosed : ∀ x y, y ∈ S → multiply table x y ∈ S := by
      intro x y hy
      change P.decode (multiply table x y) ∈ I
      rw [P.map_multiply]
      exact I.mul_mem_left _ hy
    have hmem := generatedSpace_le table c S hc hclosed ha
    change P.decode (P.decode.symm a) ∈ I at hmem
    simpa using hmem
  · apply Ideal.span_le.mpr
    rintro _ ⟨l, rfl⟩
    change P.decode.symm (P.decode (c l)) ∈ generatedSpace table c
    simp only [LinearEquiv.symm_apply_apply]
    apply denominator_mem table c (P.decode.symm 1) _ l
    intro x
    apply P.decode.injective
    simp [P.map_multiply]

/-- Reduced Artinian semantics supply equation weights, including for the zero ideal. -/
theorem AlgebraPresentation.exists_identityEquations [IsReduced A]
    {table : MultiplicationTable K d} (P : AlgebraPresentation (A := A) table)
    (c : Fin m → Coordinates K d) : ∃ weights, IdentityEquations table c weights := by
  let : Module.Finite K A := Module.Finite.equiv P.decode
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, he, _, hid⟩ := ideal_identity_exists (P.generatedIdeal c)
  obtain ⟨weights, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp he
  refine ⟨weights, ?_⟩
  intro j
  apply P.decode.injective
  have hj : P.decode (generator table c j) ∈ P.generatedIdeal c := by
    change P.decode.symm (P.decode (generator table c j)) ∈ generatedSpace table c
    simp only [LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span ⟨j, rfl⟩
  change (∑ i, weights i • generator table c i) = P.decode.symm e at hw
  rw [P.map_multiply, show P.decode (assemble table c weights) = e by
    unfold assemble
    rw [hw, LinearEquiv.apply_symm_apply]]
  exact hid _ hj

/-- Exhaustive finite search has no negative branch for a reduced algebra presentation. -/
theorem AlgebraPresentation.runFinite_not_noIdentity [DecidableEq K]
    [IsReduced A] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (enumeration : FieldEnumeration K)
    (c : Fin m → Coordinates K d) : (runFinite enumeration table c).tag ≠ 2 := by
  intro h
  exact ((runFinite_noIdentity_iff enumeration table c).mp h).2
    (P.exists_identityEquations c)

/-- For a reduced presentation, the identity branch is exactly the nonempty boundary case. -/
theorem AlgebraPresentation.runFinite_identity_iff [DecidableEq K] [IsReduced A]
    {table : MultiplicationTable K d} (P : AlgebraPresentation (A := A) table)
    (enumeration : FieldEnumeration K) (c : Fin m → Coordinates K d) :
    (runFinite enumeration table c).tag = 1 ↔ generatedSpace table c ≠ ⊥ := by
  rw [runFinite_complete]
  exact and_iff_left (P.exists_identityEquations c)

end Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity
