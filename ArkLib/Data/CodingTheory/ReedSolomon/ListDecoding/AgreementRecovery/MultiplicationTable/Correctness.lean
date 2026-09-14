/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Correctness of executed multiplication-table projections -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

open Matrix

variable {E A : Type*} [Field E] [DecidableEq E] [CommRing A] [Algebra E A] [IsReduced A]
  {n : ℕ}

/-- Every successful split carries an actual solution to the generalized inverse equation. -/
theorem Table.split?_eq_splitData (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    ∃ x, out = T.splitData e x ∧ T.mul e (T.mul e x) = e := by
  obtain ⟨x, hx, he⟩ := T.split?_success model e
  exact ⟨x, Option.some.inj (hout.symm.trans hx), he⟩

/-- Kernel projection fixes exactly the vectors annihilated by the residual matrix. -/
theorem Table.kernel_projection_fixed (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) (y : Fin n → E) :
    out.kernelProjection *ᵥ y = y ↔ T.mulMatrix e *ᵥ y = 0 := by
  obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
  have hx' := congrArg model.decode hx
  simp only [model.decode_mul] at hx'
  have h := kernel_projection_fixed_iff (model.decode e) (model.decode x) (model.decode y) hx'
  change T.mul (T.unit - T.mul e x) y = y ↔ T.mul e y = 0
  simpa only [← model.decode_mul, ← model.decode_unit,
    ← map_sub, model.decode.injective.eq_iff, ← map_zero model.decode,
    model.decode.injective.eq_iff] using h

/-- Image projection fixes exactly the vectors in the residual matrix image. -/
theorem Table.image_projection_fixed (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) (y : Fin n → E) :
    out.imageProjection *ᵥ y = y ↔ ∃ z, T.mulMatrix e *ᵥ z = y := by
  obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
  have hx' := congrArg model.decode hx
  simp only [model.decode_mul] at hx'
  have h := image_projection_fixed_iff (model.decode e) (model.decode x) (model.decode y) hx'
  constructor
  · intro hy
    have hd := congrArg model.decode hy
    change model.decode (T.mul (T.mul e x) y) = model.decode y at hd
    rw [model.decode_mul, model.decode_mul] at hd
    obtain ⟨z, hz⟩ := h.mp hd
    refine ⟨model.decode.symm z, model.decode.injective ?_⟩
    rw [← Table.mul, model.decode_mul, model.decode.apply_symm_apply, hz]
  · rintro ⟨z, hz⟩
    change T.mul e z = y at hz
    apply model.decode.injective
    change model.decode (T.mul (T.mul e x) y) = model.decode y
    rw [model.decode_mul, model.decode_mul]
    apply h.mpr
    exact ⟨model.decode z, by rw [← model.decode_mul, hz]⟩

/-- The materialized kernel projection has exactly the required kernel as its range. -/
theorem Table.kernel_projection_range (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    LinearMap.range out.kernelProjection.mulVecLin = LinearMap.ker (T.mulMatrix e).mulVecLin := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
    apply model.decode.injective
    change model.decode (T.mul e (T.mul (T.unit - T.mul e x) z)) = model.decode 0
    rw [model.decode_mul, model.decode_mul, map_sub, model.decode_unit, model.decode_mul,
      map_zero, ← mul_assoc]
    have hx' := congrArg model.decode hx
    simp only [model.decode_mul] at hx'
    rw [kernel_identity_annihilates _ _ hx', zero_mul]
  · intro hy
    exact ⟨y, (T.kernel_projection_fixed model e out hout y).mpr hy⟩

/-- The materialized image projection has exactly the residual matrix image as its range. -/
theorem Table.image_projection_range (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    LinearMap.range out.imageProjection.mulVecLin = LinearMap.range (T.mulMatrix e).mulVecLin := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl, _⟩ := T.split?_eq_splitData model e out hout
    refine ⟨T.mul x z, model.decode.injective ?_⟩
    change model.decode (T.mul e (T.mul x z)) = model.decode (T.mul (T.mul e x) z)
    simp only [model.decode_mul, mul_assoc]
  · rintro ⟨z, hz⟩
    exact ⟨y, (T.image_projection_fixed model e out hout y).mpr ⟨z, hz⟩⟩

/-- The computed kernel/image factors conserve the full algebra dimension, including zero. -/
theorem Table.split_dimension (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    Module.finrank E (LinearMap.range out.kernelProjection.mulVecLin) +
      Module.finrank E (LinearMap.range out.imageProjection.mulVecLin) = n := by
  rw [T.kernel_projection_range model e out hout, T.image_projection_range model e out hout,
    add_comm, LinearMap.finrank_range_add_finrank_ker]
  simp

/-- A geometric point belongs to exactly the agreeing kernel or nonagreeing image factor. -/
theorem Table.split_geometric_partition (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out)
    {K : Type*} [Field K] (phi : A →+* K) :
    (phi (model.decode out.kernelIdentity) = 1 ↔ phi (model.decode e) = 0) ∧
      (phi (model.decode out.imageIdentity) = 1 ↔ phi (model.decode e) ≠ 0) := by
  obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
  have hx' := congrArg (fun y => phi (model.decode y)) hx
  simp only [model.decode_mul, map_mul] at hx'
  have hi : phi (model.decode e) ≠ 0 → phi (model.decode e) * phi (model.decode x) = 1 := by
    intro he
    exact mul_left_cancel₀ he (by simpa only [mul_one] using hx')
  simp only [Table.splitData, map_sub, model.decode_unit, model.decode_mul, map_one, map_mul]
  by_cases he : phi (model.decode e) = 0
  · simp [he]
  · simp [he, hi he]

/-- The two computed factor identities are complementary orthogonal idempotents. -/
theorem Table.split_identities (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    out.kernelIdentity + out.imageIdentity = T.unit ∧
      T.mul out.kernelIdentity out.kernelIdentity = out.kernelIdentity ∧
      T.mul out.imageIdentity out.imageIdentity = out.imageIdentity ∧
      T.mul out.kernelIdentity out.imageIdentity = 0 := by
  obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
  have hx' := congrArg model.decode hx
  simp only [model.decode_mul] at hx'
  have hi := image_identity_idempotent (model.decode e) (model.decode x) hx'
  simp only [Table.splitData]
  refine ⟨sub_add_cancel _ _, ?_, ?_, ?_⟩ <;> apply model.decode.injective
  · simp only [model.decode_mul, map_sub, model.decode_unit]
    calc
      (1 - model.decode e * model.decode x) *
          (1 - model.decode e * model.decode x) =
          1 - 2 * (model.decode e * model.decode x) +
            (model.decode e * model.decode x) * (model.decode e * model.decode x) := by ring
      _ = 1 - model.decode e * model.decode x := by rw [hi]; ring
  · simpa only [model.decode_mul] using hi
  · simp only [model.decode_mul, map_sub, model.decode_unit, map_zero]
    rw [sub_mul, one_mul, hi, sub_self]

/-- The residual is zero on the kernel factor and has an explicit inverse relative to the image
identity. The inverse is itself in the image factor, without a factorization oracle. -/
theorem Table.split_residual_zero_unit (T : Table E n) (model : T.Model A)
    (e : Fin n → E) (out : SplitData E n) (hout : T.split? e = some out) :
    T.mul out.kernelIdentity e = 0 ∧
      T.mul e (T.mul out.imageIdentity out.generalizedInverse) = out.imageIdentity ∧
      T.mul out.imageIdentity (T.mul out.imageIdentity out.generalizedInverse) =
        T.mul out.imageIdentity out.generalizedInverse := by
  obtain ⟨x, rfl, hx⟩ := T.split?_eq_splitData model e out hout
  have hx' := congrArg model.decode hx
  simp only [model.decode_mul] at hx'
  have hi := image_identity_idempotent (model.decode e) (model.decode x) hx'
  simp only [Table.splitData]
  refine ⟨?_, ?_, ?_⟩ <;> apply model.decode.injective
  · simpa only [model.decode_mul, map_sub, model.decode_unit, map_zero, mul_comm]
      using kernel_identity_annihilates (model.decode e) (model.decode x) hx'
  · simp only [model.decode_mul]
    rw [← mul_assoc, hx']
  · simp only [model.decode_mul]
    rw [← mul_assoc, hi]

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
