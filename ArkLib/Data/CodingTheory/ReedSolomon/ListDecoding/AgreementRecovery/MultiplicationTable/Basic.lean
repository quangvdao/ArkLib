/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.LinearSolve
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Algebra

/-! # Executed multiplication-table kernel/image projections -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

open Matrix

variable {E : Type*} [Field E] {n : ℕ}

/-- Multiplication constants and unit coordinates in a supplied finite basis. Dimension zero is
allowed and represents the zero algebra. -/
structure Table (E : Type*) (n : ℕ) where
  /-- Coordinates of the algebra identity. -/
  unit : Fin n → E
  /-- The `k`-th coordinate of basis vector `i` times basis vector `j`. -/
  constants : Fin n → Fin n → Fin n → E

/-- The matrix of multiplication by one coordinate vector, computed directly from the table. -/
def Table.mulMatrix (T : Table E n) (e : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  fun i j => ∑ k, e k * T.constants k j i

/-- Actual multiplication in the supplied coordinates. -/
def Table.mul (T : Table E n) (x y : Fin n → E) : Fin n → E := T.mulMatrix x *ᵥ y

/-- A proof-only interpretation connecting the data to an ordinary finite commutative algebra.
No factorization or geometric point is part of the executable table. -/
structure Table.Model (T : Table E n) (A : Type*) [CommRing A] [Algebra E A] where
  /-- Supplied coordinate equivalence. -/
  decode : (Fin n → E) ≃ₗ[E] A
  /-- The supplied unit is the algebra identity. -/
  decode_unit : decode T.unit = 1
  /-- The table computes the actual algebra multiplication. -/
  decode_mul : ∀ x y, decode (T.mul x y) = decode x * decode y

/-- A computed generalized inverse, identities, and matrices projecting onto kernel and image.
The projection columns are generating sets for those subspaces, so a second basis ecosystem is
unnecessary. Redundant columns are allowed, including the empty dimension-zero case. -/
structure SplitData (E : Type*) (n : ℕ) where
  /-- A solution to `e²x=e`. -/
  generalizedInverse : Fin n → E
  /-- Identity on the kernel factor. -/
  kernelIdentity : Fin n → E
  /-- Identity on the image factor. -/
  imageIdentity : Fin n → E
  /-- Projection whose image is the kernel of residual multiplication. -/
  kernelProjection : Matrix (Fin n) (Fin n) E
  /-- Projection whose image is the image of residual multiplication. -/
  imageProjection : Matrix (Fin n) (Fin n) E

/-- Materialize both complementary identities and their coordinate projections. -/
def Table.splitData (T : Table E n) (e x : Fin n → E) : SplitData E n :=
  let q := T.mul e x
  let p := T.unit - q
  ⟨x, p, q, T.mulMatrix p, T.mulMatrix q⟩

/-- Execute Gaussian elimination on `m_e² x=e`, then materialize kernel/image projections. -/
def Table.split? [DecidableEq E] (T : Table E n) (e : Fin n → E) : Option (SplitData E n) :=
  (LinearSolve.solve? (T.mulMatrix e * T.mulMatrix e) e).map (T.splitData e)

/-- A reduced finite-algebra model guarantees a solution in coordinates, even at dimension zero. -/
theorem Table.Model.exists_coordinate_inverse
    (T : Table E n) {A : Type*} [CommRing A] [Algebra E A] [IsReduced A]
    (model : T.Model A) (e : Fin n → E) : ∃ x, T.mul e (T.mul e x) = e := by
  let : FiniteDimensional E A :=
    FiniteDimensional.of_injective model.decode.symm.toLinearMap model.decode.symm.injective
  obtain ⟨x, hx⟩ := exists_generalized_inverse (E := E) (model.decode e)
  refine ⟨model.decode.symm x, model.decode.injective ?_⟩
  rw [model.decode_mul, model.decode_mul, model.decode.apply_symm_apply]
  exact hx

/-- The executed split succeeds for every element of a reduced multiplication-table algebra. -/
theorem Table.split?_success [DecidableEq E]
    (T : Table E n) {A : Type*} [CommRing A] [Algebra E A] [IsReduced A]
    (model : T.Model A) (e : Fin n → E) :
    ∃ x, T.split? e = some (T.splitData e x) ∧ T.mul e (T.mul e x) = e := by
  have hc : ∃ x, (T.mulMatrix e * T.mulMatrix e) *ᵥ x = e := by
    obtain ⟨x, hx⟩ := model.exists_coordinate_inverse T e
    refine ⟨x, ?_⟩
    simpa only [Table.mul, Matrix.mulVec_mulVec] using hx
  obtain ⟨x, hx, he⟩ := LinearSolve.solve?_success _ _ hc
  exact ⟨x, by simp [Table.split?, hx], by
    simpa only [Table.mul, Matrix.mulVec_mulVec] using he⟩

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
