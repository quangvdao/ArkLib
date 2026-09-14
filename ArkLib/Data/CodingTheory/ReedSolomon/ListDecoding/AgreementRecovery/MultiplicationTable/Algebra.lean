/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Kernel/image splitting in a finite reduced algebra -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

variable {E A : Type*} [Field E] [CommRing A] [Algebra E A] [IsReduced A]

/-- Reducedness makes multiplication by an element injective on its own image. -/
theorem mul_mul_eq_zero_iff (e x : A) : e * (e * x) = 0 ↔ e * x = 0 := by
  constructor
  · intro h
    apply IsReduced.eq_zero
    refine ⟨2, ?_⟩
    calc
      (e * x) ^ 2 = (e * (e * x)) * x := by ring
      _ = 0 := by rw [h, zero_mul]
  · intro h
    rw [h, mul_zero]

/-- Finite-dimensional reduced algebras admit a solution of `e²x=e`, including the zero algebra. -/
theorem exists_generalized_inverse [FiniteDimensional E A] (e : A) :
    ∃ x : A, e * (e * x) = e := by
  let M : A →ₗ[E] A := LinearMap.mulLeft E e
  let V := LinearMap.range M
  let T : V →ₗ[E] V :=
    { toFun := fun y => ⟨e * y.val, ⟨y.val, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp [mul_add]
      map_smul' := by intro a y; apply Subtype.ext; simp [Algebra.mul_smul_comm] }
  have hT : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    obtain ⟨a, ha⟩ := y.property
    obtain ⟨b, hb⟩ := z.property
    change e * a = y.val at ha
    change e * b = z.val at hb
    have hmul : e * (e * (a - b)) = 0 := by
      have he := congrArg Subtype.val hyz
      change e * y.val = e * z.val at he
      rw [mul_sub, mul_sub, ha, hb, sub_eq_zero]
      exact he
    have he := (mul_mul_eq_zero_iff e (a - b)).mp hmul
    rwa [mul_sub, ha, hb, sub_eq_zero] at he
  have hsurj := LinearMap.injective_iff_surjective.mp hT
  have he : e ∈ V := ⟨1, by simp [M]⟩
  obtain ⟨y, hy⟩ := hsurj ⟨e, he⟩
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, ?_⟩
  have hy' := congrArg Subtype.val hy
  change e * y.val = e at hy'
  change e * x = y.val at hx
  rw [hx, hy']

omit [IsReduced A] in
/-- The image identity obtained from a generalized inverse is idempotent. -/
theorem image_identity_idempotent (e x : A) (hx : e * (e * x) = e) :
    (e * x) * (e * x) = e * x := by
  calc
    (e * x) * (e * x) = (e * (e * x)) * x := by ring
    _ = e * x := by rw [hx]

omit [IsReduced A] in
/-- The complementary identity annihilates the residual. -/
theorem kernel_identity_annihilates (e x : A) (hx : e * (e * x) = e) :
    e * (1 - e * x) = 0 := by rw [mul_sub, mul_one, hx, sub_self]

omit [IsReduced A] in
/-- Image projection fixes exactly the image of multiplication by the residual. -/
theorem image_projection_fixed_iff (e x y : A) (hx : e * (e * x) = e) :
    (e * x) * y = y ↔ ∃ z, e * z = y := by
  constructor
  · intro h
    exact ⟨x * y, by rw [← mul_assoc, h]⟩
  · rintro ⟨z, rfl⟩
    calc
      (e * x) * (e * z) = (e * (e * x)) * z := by ring
      _ = e * z := by rw [hx]

omit [IsReduced A] in
/-- Kernel projection fixes exactly the kernel of multiplication by the residual. -/
theorem kernel_projection_fixed_iff (e x y : A) (hx : e * (e * x) = e) :
    (1 - e * x) * y = y ↔ e * y = 0 := by
  constructor
  · intro h
    calc
      e * y = e * ((1 - e * x) * y) := by rw [h]
      _ = (e * (1 - e * x)) * y := by ring
      _ = 0 := by rw [kernel_identity_annihilates e x hx, zero_mul]
  · intro h
    have he : (e * x) * y = 0 := by
      calc
        (e * x) * y = x * (e * y) := by ring
        _ = 0 := by rw [h, mul_zero]
    rw [sub_mul, one_mul, he, sub_zero]

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
