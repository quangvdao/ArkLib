/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# The adjacency operator of the labelled Gabber--Galil multigraph

The operator sums over labels. Consequently a loop contributes once for each labelled dart and
parallel darts retain their multiplicity. We prove the four structural facts used by powering:
linearity, self-adjointness, the constant eigenvalue eight, and preservation of mean-zero vectors.
-/

@[expose] public section

namespace GabberGalil

open scoped BigOperators

variable {m : ℕ}

/-- The unnormalised adjacency operator. The sum is over the eight labels, not endpoint sets. -/
def adjacency {R : Type*} [Semiring R] (f : Vertex m → R) : Vertex m → R :=
  fun v ↦ ∑ l : Label, f (step l v)

@[simp]
theorem adjacency_apply {R : Type*} [Semiring R] (f : Vertex m → R) (v : Vertex m) :
    adjacency f v = ∑ l : Label, f (step l v) := rfl

@[simp]
theorem adjacency_zero {R : Type*} [Semiring R] :
    adjacency (m := m) (0 : Vertex m → R) = 0 := by
  ext v
  simp [adjacency]

@[simp]
theorem adjacency_add {R : Type*} [Semiring R] (f g : Vertex m → R) :
    adjacency (f + g) = adjacency f + adjacency g := by
  ext v
  simp [adjacency, Finset.sum_add_distrib]

@[simp]
theorem adjacency_smul {R : Type*} [Semiring R] (a : R) (f : Vertex m → R) :
    adjacency (a • f) = a • adjacency f := by
  ext v
  simp [adjacency, Finset.mul_sum]

/-- Adjacency as an `R`-linear map on vertex functions. -/
def adjacencyLinear (R : Type*) [Semiring R] :
    (Vertex m → R) →ₗ[R] (Vertex m → R) where
  toFun := adjacency
  map_add' := adjacency_add
  map_smul' := adjacency_smul

@[simp]
theorem adjacencyLinear_apply (R : Type*) [Semiring R] (f : Vertex m → R) :
    adjacencyLinear (m := m) R f = adjacency f := rfl

/-- Constants are eigenvectors of unnormalised adjacency with eigenvalue eight. -/
@[simp]
theorem adjacency_const {R : Type*} [Semiring R] (a : R) :
    adjacency (m := m) (fun _ ↦ a) = fun _ ↦ 8 * a := by
  ext v
  simp [adjacency]

variable [NeZero m]

/-- Finite dot product on vertex functions. -/
def dot {R : Type*} [Semiring R] (f g : Vertex m → R) : R :=
  ∑ v, f v * g v

/-- A labelled step permutes the summation index. -/
theorem sum_step {R : Type*} [AddCommMonoid R] (l : Label) (f : Vertex m → R) :
    ∑ v, f (step l v) = ∑ v, f v := by
  exact Equiv.sum_comp (stepPerm m l) f

/-- Reindex one labelled contribution by its reverse label. -/
theorem sum_mul_step {R : Type*} [CommSemiring R] (l : Label)
    (f g : Vertex m → R) :
    ∑ v, f (step l v) * g v = ∑ v, f v * g (step (reverseLabel l) v) := by
  calc
    ∑ v, f (step l v) * g v =
        ∑ v, f (step l (step (reverseLabel l) v)) * g (step (reverseLabel l) v) := by
          symm
          exact Equiv.sum_comp (stepPerm m (reverseLabel l))
            (fun v ↦ f (step l v) * g v)
    _ = ∑ v, f v * g (step (reverseLabel l) v) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [show step l (step (reverseLabel l) v) = v by
        simpa using step_reverse (reverseLabel l) v]

/-- Reversal is a permutation of the eight labels. -/
def reverseLabelEquiv : Label ≃ Label where
  toFun := reverseLabel
  invFun := reverseLabel
  left_inv := reverseLabel_reverseLabel
  right_inv := reverseLabel_reverseLabel

/-- Self-adjointness of the labelled adjacency operator for the finite dot product. -/
theorem adjacency_selfAdjoint {R : Type*} [CommSemiring R] (f g : Vertex m → R) :
    dot (adjacency f) g = dot f (adjacency g) := by
  simp only [dot, adjacency, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [sum_mul_step]
  change (∑ l, (fun l ↦ ∑ v, f v * g (step l v)) (reverseLabelEquiv l)) = _
  calc
    _ = ∑ l, ∑ v, f v * g (step l v) := reverseLabelEquiv.sum_comp _
    _ = ∑ v, f v * ∑ l, g (step l v) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- Vertex functions whose total sum is zero. -/
def MeanZero {R : Type*} [Semiring R] : Submodule R (Vertex m → R) where
  carrier := {f | ∑ v, f v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change ∑ v, (f + g) v = 0
    change (∑ v, f v) = 0 at hf
    change (∑ v, g v) = 0 at hg
    simp [Finset.sum_add_distrib, hf, hg]
  smul_mem' := by
    intro a f hf
    change ∑ v, (a • f) v = 0
    change (∑ v, f v) = 0 at hf
    change ∑ v, a * f v = 0
    rw [← Finset.mul_sum, hf, mul_zero]

theorem mem_meanZero_iff {R : Type*} [Semiring R] (f : Vertex m → R) :
    f ∈ MeanZero (m := m) (R := R) ↔ ∑ v, f v = 0 := by rfl

/-- The sum of adjacency is eight times the original sum. -/
theorem sum_adjacency {R : Type*} [Semiring R] (f : Vertex m → R) :
    ∑ v, adjacency f v = 8 * ∑ v, f v := by
  simp only [adjacency]
  rw [Finset.sum_comm]
  simp_rw [sum_step]
  simp

/-- Adjacency preserves the mean-zero subspace. -/
theorem adjacency_mem_meanZero {R : Type*} [Semiring R] {f : Vertex m → R}
    (hf : f ∈ MeanZero (m := m) (R := R)) :
    adjacency f ∈ MeanZero (m := m) (R := R) := by
  rw [mem_meanZero_iff, sum_adjacency, (mem_meanZero_iff f).mp hf, mul_zero]

end GabberGalil
