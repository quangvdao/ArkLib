/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.HyperplaneAvoidance
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Avoiding cross-family collisions in Rojas specialization

Besides injectivity inside each projection family, Rojas Steps 4--5 require that a root from a
Step-2 family and an affine-transformed root from the corresponding Step-3 family meet only when
both come from the base point selected by the Step-1 root.  This file records the exact labelled
collision polynomial and extends the deterministic moment-curve avoidance bound to these
cross-family collisions.
-/

@[expose] public section

namespace ArkLib.Rojas

open Polynomial

section CrossFamilyCollisions

variable {K : Type*} [Field K]
variable {s M : ℕ}

/-- A coordinate together with the base, Step-2, and Step-3 point labels involved in a possible
cross-family collision. -/
abbrev CrossCollisionLabel (s M : ℕ) := Fin s × (Fin M × (Fin M × Fin M))

@[simp]
theorem coeff_projectionPolynomial_zero (point : Fin s → K) :
    (projectionPolynomial point).coeff 0 = 0 := by
  simp [projectionPolynomial, Polynomial.coeff_X_pow]

/-- The only intended label has the same point in all three roles. -/
def CrossCollisionLabel.IsIntended (label : CrossCollisionLabel s M) : Prop :=
  label.2.2.1 = label.2.1 ∧ label.2.2.2 = label.2.1

/-- The exact polynomial which vanishes when a Step-2 root labelled by `minus` also becomes an
affine-transformed Step-3 root labelled by `plus`, over the Step-1 root labelled by `base`. -/
noncomputable def crossCollisionPolynomial (alpha : K)
    (points : Fin M → Fin s → K) (label : CrossCollisionLabel s M) : K[X] :=
  C (alpha + 1) * shiftedProjectionPolynomial 0 (.inl ()) (points label.2.1) -
    C alpha * shiftedProjectionPolynomial 0 (.inr (.inl label.1)) (points label.2.2.1) -
      shiftedProjectionPolynomial alpha (.inr (.inr label.1)) (points label.2.2.2)

/-- Executable evaluation of a moment-curve projection, without materializing a polynomial. -/
def projectionValue (epsilon : K) (point : Fin s → K) : K :=
  -∑ i, epsilon ^ (i.val + 1) * point i

/-- Executable value of a labelled cross-family collision at one parameter. -/
def crossCollisionValue (alpha epsilon : K)
    (points : Fin M → Fin s → K) (label : CrossCollisionLabel s M) : K :=
  (alpha + 1) * projectionValue epsilon (points label.2.1) -
    alpha * (projectionValue epsilon (points label.2.2.1) +
      points label.2.2.1 label.1) -
    (projectionValue epsilon (points label.2.2.2) -
      alpha * points label.2.2.2 label.1)

@[simp]
theorem crossCollisionPolynomial_intended (alpha : K) (points : Fin M → Fin s → K)
    (i : Fin s) (j : Fin M) :
    crossCollisionPolynomial alpha points (i, j, j, j) = 0 := by
  simp [crossCollisionPolynomial, shiftedProjectionPolynomial, projectionOffset]
  ring

/-- Evaluation of the collision polynomial in terms of the three geometric projections. -/
theorem eval_crossCollisionPolynomial (alpha epsilon : K)
    (points : Fin M → Fin s → K) (label : CrossCollisionLabel s M) :
    (crossCollisionPolynomial alpha points label).eval epsilon =
      (alpha + 1) * (projectionPolynomial (points label.2.1)).eval epsilon -
        alpha * ((projectionPolynomial (points label.2.2.1)).eval epsilon +
          points label.2.2.1 label.1) -
        ((projectionPolynomial (points label.2.2.2)).eval epsilon -
          alpha * points label.2.2.2 label.1) := by
  simp [crossCollisionPolynomial, shiftedProjectionPolynomial, projectionOffset]
  ring

/-- The executable collision value agrees with evaluation of the collision polynomial. -/
theorem crossCollisionValue_eq_eval (alpha epsilon : K)
    (points : Fin M → Fin s → K) (label : CrossCollisionLabel s M) :
    crossCollisionValue alpha epsilon points label =
      (crossCollisionPolynomial alpha points label).eval epsilon := by
  rw [eval_crossCollisionPolynomial]
  simp only [crossCollisionValue, projectionValue, eval_projectionPolynomial]

/-- The exact coefficient-level condition excluding identically-zero nontrivial cross-family
collision polynomials.  Either a positive-degree weighted affine coefficient separates the three
labels, or the coordinate-dependent constant coefficient does. -/
def CrossCollisionSeparated (alpha : K) (points : Fin M → Fin s → K) : Prop :=
  ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
    (∃ coordinate : Fin s,
        (alpha + 1) * points label.2.1 coordinate -
          alpha * points label.2.2.1 coordinate -
            points label.2.2.2 coordinate ≠ 0) ∨
      alpha * (points label.2.2.2 label.1 - points label.2.2.1 label.1) ≠ 0

/-- The geometric separation condition makes every nontrivial labelled collision polynomial
nonzero. -/
theorem crossCollisionPolynomial_ne_zero
    (alpha : K) {points : Fin M → Fin s → K}
    (hseparated : CrossCollisionSeparated alpha points)
    (label : CrossCollisionLabel s M) (hnontrivial : ¬label.IsIntended) :
    crossCollisionPolynomial alpha points label ≠ 0 := by
  intro hzero
  rcases hseparated label hnontrivial with hpositive | hconstant
  · obtain ⟨coordinate, hcoordinate⟩ := hpositive
    have hcoeff := congrArg
      (fun polynomial : K[X] ↦ polynomial.coeff (coordinate.val + 1)) hzero
    simp only [crossCollisionPolynomial, coeff_sub, Polynomial.coeff_C_mul,
      shiftedProjectionPolynomial, coeff_add,
      coeff_projectionPolynomial, coeff_C_succ, add_zero, coeff_zero] at hcoeff
    apply hcoordinate
    have hneg : -((alpha + 1) * points label.2.1 coordinate -
        alpha * points label.2.2.1 coordinate - points label.2.2.2 coordinate) = 0 := by
      convert hcoeff using 1
      all_goals ring
    exact neg_eq_zero.mp hneg
  · have hcoeff := congrArg (fun polynomial : K[X] ↦ polynomial.coeff 0) hzero
    simp only [crossCollisionPolynomial, map_add, map_one, shiftedProjectionPolynomial,
      projectionOffset, map_zero, add_zero, neg_mul, map_neg, map_mul, coeff_sub,
      mul_coeff_zero, coeff_add, coeff_C_zero, coeff_one_zero,
      coeff_projectionPolynomial_zero, mul_zero, zero_add, zero_sub, coeff_neg,
      sub_neg_eq_add, coeff_zero] at hcoeff
    apply hconstant
    calc
      alpha * (points label.2.2.2 label.1 - points label.2.2.1 label.1) =
          -(alpha * points label.2.2.1 label.1) +
            alpha * points label.2.2.2 label.1 := by ring
      _ = 0 := hcoeff

/-- Every labelled cross-family collision has degree at most the ambient dimension. -/
theorem natDegree_crossCollisionPolynomial_le (alpha : K)
    (points : Fin M → Fin s → K) (label : CrossCollisionLabel s M) :
    (crossCollisionPolynomial alpha points label).natDegree ≤ s := by
  have hbase :
      (C (alpha + 1) * shiftedProjectionPolynomial 0 (.inl ())
        (points label.2.1)).natDegree ≤ s :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_shiftedProjectionPolynomial_le _ _ _)
  have hminus :
      (C alpha * shiftedProjectionPolynomial 0 (.inr (.inl label.1))
        (points label.2.2.1)).natDegree ≤ s :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_shiftedProjectionPolynomial_le _ _ _)
  have hplus :
      (shiftedProjectionPolynomial alpha (.inr (.inr label.1))
        (points label.2.2.2)).natDegree ≤ s :=
    natDegree_shiftedProjectionPolynomial_le _ _ _
  exact (natDegree_sub_le _ _).trans <| max_le
    ((natDegree_sub_le _ _).trans (max_le hbase hminus)) hplus

/-- All nontrivial labelled cross-family collision polynomials. -/
noncomputable def crossCollisionPolynomials (alpha : K)
    (points : Fin M → Fin s → K) : Finset K[X] := by
  classical
  exact ((Finset.univ : Finset (CrossCollisionLabel s M)).filter
    fun label ↦ ¬label.IsIntended).image
      (crossCollisionPolynomial alpha points)

theorem card_crossCollisionPolynomials_le (alpha : K)
    (points : Fin M → Fin s → K) :
    (crossCollisionPolynomials alpha points).card ≤ s * M * M * M := by
  classical
  rw [crossCollisionPolynomials]
  calc
    _ ≤ ((Finset.univ : Finset (CrossCollisionLabel s M)).filter
        fun label ↦ ¬label.IsIntended).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (CrossCollisionLabel s M)).card :=
      Finset.card_filter_le _ _
    _ = s * M * M * M := by simp [CrossCollisionLabel]; ring

theorem crossCollisionPolynomials_nonzero (alpha : K)
    {points : Fin M → Fin s → K} (hseparated : CrossCollisionSeparated alpha points) :
    ∀ polynomial ∈ crossCollisionPolynomials alpha points, polynomial ≠ 0 := by
  classical
  intro polynomial hpolynomial
  rw [crossCollisionPolynomials] at hpolynomial
  obtain ⟨label, hlabel, rfl⟩ := Finset.mem_image.mp hpolynomial
  exact crossCollisionPolynomial_ne_zero alpha hseparated label
    (Finset.mem_filter.mp hlabel).2

theorem crossCollisionPolynomials_degree_le (alpha : K)
    (points : Fin M → Fin s → K) :
    ∀ polynomial ∈ crossCollisionPolynomials alpha points, polynomial.natDegree ≤ s := by
  classical
  intro polynomial hpolynomial
  rw [crossCollisionPolynomials] at hpolynomial
  obtain ⟨label, _, rfl⟩ := Finset.mem_image.mp hpolynomial
  exact natDegree_crossCollisionPolynomial_le alpha points label

/-- Within-family and cross-family collision polynomials used by one deterministic scan. -/
noncomputable def safeCollisionPolynomials (alpha : K)
    (points : Fin M → Fin s → K) : Finset K[X] := by
  classical
  exact collisionPolynomials alpha points ∪ crossCollisionPolynomials alpha points

theorem card_safeCollisionPolynomials_le (alpha : K)
    (points : Fin M → Fin s → K) :
    (safeCollisionPolynomials alpha points).card ≤
      (2 * s + 1) * M.choose 2 + s * M * M * M := by
  classical
  unfold safeCollisionPolynomials
  exact (Finset.card_union_le _ _).trans <| Nat.add_le_add
    (card_collisionPolynomials_le alpha points)
    (card_crossCollisionPolynomials_le alpha points)

theorem safeCollisionPolynomials_nonzero (alpha : K)
    {points : Fin M → Fin s → K} (hpoints : Function.Injective points)
    (hseparated : CrossCollisionSeparated alpha points) :
    ∀ polynomial ∈ safeCollisionPolynomials alpha points, polynomial ≠ 0 := by
  classical
  intro polynomial hpolynomial
  unfold safeCollisionPolynomials at hpolynomial
  rcases Finset.mem_union.mp hpolynomial with hwithin | hcross
  · exact collisionPolynomials_nonzero alpha hpoints polynomial hwithin
  · exact crossCollisionPolynomials_nonzero alpha hseparated polynomial hcross

theorem safeCollisionPolynomials_degree_le (alpha : K)
    (points : Fin M → Fin s → K) :
    ∀ polynomial ∈ safeCollisionPolynomials alpha points, polynomial.natDegree ≤ s := by
  classical
  intro polynomial hpolynomial
  unfold safeCollisionPolynomials at hpolynomial
  rcases Finset.mem_union.mp hpolynomial with hwithin | hcross
  · exact collisionPolynomials_degree_le alpha points polynomial hwithin
  · exact crossCollisionPolynomials_degree_le alpha points polynomial hcross

/-- A duplicate-free base-field list longer than the combined root bound contains a parameter
which is injective within every Rojas projection family and avoids every nontrivial cross-family
collision. -/
theorem exists_parameter_with_safe_projections
    {F : Type*} [Field F] (ι : F →+* K) {M : ℕ} (alpha : K)
    {points : Fin M → Fin s → K} (hpoints : Function.Injective points)
    (hseparated : CrossCollisionSeparated alpha points)
    (candidates : List F) (hnodup : candidates.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < candidates.length) :
    ∃ epsilon ∈ candidates,
      (∀ kind : ProjectionKind s, Function.Injective fun j ↦
        (shiftedProjectionPolynomial alpha kind (points j)).eval (ι epsilon)) ∧
      (∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
        (crossCollisionPolynomial alpha points label).eval (ι epsilon) ≠ 0) := by
  classical
  let polynomials := safeCollisionPolynomials alpha points
  have hcard : polynomials.card * s ≤
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s :=
    Nat.mul_le_mul_right s (card_safeCollisionPolynomials_le alpha points)
  obtain ⟨epsilon, hepsilon, havoid⟩ := exists_avoiding_finite_polynomials
    ι polynomials s (safeCollisionPolynomials_nonzero alpha hpoints hseparated)
    (safeCollisionPolynomials_degree_le alpha points) candidates hnodup
    (hcard.trans_lt hlength)
  have hwithin : ∀ polynomial ∈ collisionPolynomials alpha points,
      polynomial.eval (ι epsilon) ≠ 0 := by
    intro polynomial hpolynomial
    apply havoid polynomial
    dsimp only [polynomials, safeCollisionPolynomials]
    exact Finset.mem_union_left _ hpolynomial
  have hcross : ∀ polynomial ∈ crossCollisionPolynomials alpha points,
      polynomial.eval (ι epsilon) ≠ 0 := by
    intro polynomial hpolynomial
    apply havoid polynomial
    dsimp only [polynomials, safeCollisionPolynomials]
    exact Finset.mem_union_right _ hpolynomial
  refine ⟨epsilon, hepsilon, ?_, ?_⟩
  · intro kind left right hequal
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hwithin (collisionPolynomial alpha kind (points left) (points right)) (by
        apply Finset.mem_image.mpr
        exact ⟨(kind, (left, right)), by simp [pointPairs, hlt], rfl⟩)
      simpa only [collisionPolynomial, Polynomial.eval_sub, sub_eq_zero] using hequal
    · apply hwithin (collisionPolynomial alpha kind (points right) (points left)) (by
        apply Finset.mem_image.mpr
        exact ⟨(kind, (right, left)), by simp [pointPairs, hgt], rfl⟩)
      simpa only [collisionPolynomial, Polynomial.eval_sub, sub_eq_zero] using hequal.symm
  · intro label hnontrivial
    apply hcross (crossCollisionPolynomial alpha points label)
    rw [crossCollisionPolynomials]
    apply Finset.mem_image.mpr
    exact ⟨label, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnontrivial⟩, rfl⟩

end CrossFamilyCollisions

end ArkLib.Rojas
