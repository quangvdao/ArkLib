/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Finite

/-! # Polynomial identities along polynomial graphs

A positive-dimensional principal open whose points lie on a polynomial graph supplies
infinitely many parameter values. Consequently every polynomial vanishing on the open
vanishes identically after restriction to that graph. This avoids constructing image
closures when recognizing one-parameter families of polynomial solutions.
-/

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ : Type*} [Field F]

/-- A polynomial graph retaining its parameter as the `none` coordinate. -/
def polynomialGraphPoint (w : σ → Polynomial F) (z : F) : Option σ → F :=
  fun i ↦ i.elim z (fun j ↦ (w j).eval z)

/-- Restriction to a polynomial graph, with no bound on the coordinate degrees. -/
def polynomialGraphPullback (w : σ → Polynomial F) :
    MvPolynomial (Option σ) F →ₐ[F] Polynomial F :=
  aeval (fun i ↦ i.elim Polynomial.X w)

/-- Polynomial-graph restriction commutes with evaluation of the retained parameter. -/
theorem eval_polynomialGraphPullback (w : σ → Polynomial F) (z : F)
    (p : MvPolynomial (Option σ) F) :
    (polynomialGraphPullback w p).eval z = aeval (polynomialGraphPoint w z) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [polynomialGraphPullback]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      cases i <;> simp [polynomialGraphPullback, polynomialGraphPoint]

/-- An infinite subset of a polynomial graph detects all polynomial identities on the graph.
Retaining the parameter makes its projection injective, even when the other coordinates
are constant or inseparable polynomials. -/
theorem polynomialGraphPullback_eq_zero_of_infinite
    (w : σ → Polynomial F) {S : Set (Option σ → F)} (hS : S.Infinite)
    (hgraph : ∀ x ∈ S, x = polynomialGraphPoint w (x none))
    (p : MvPolynomial (Option σ) F) (hzero : ∀ x ∈ S, aeval x p = 0) :
    polynomialGraphPullback w p = 0 := by
  have hinj : Set.InjOn (fun x : Option σ → F ↦ x none) S := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (hS.image hinj).mono
  rintro z ⟨x, hx, rfl⟩
  change (polynomialGraphPullback w p).eval (x none) = 0
  rw [eval_polynomialGraphPullback, ← hgraph x hx]
  exact hzero x hx

/-- A positive-dimensional prime principal open supported on a polynomial graph extends to
identities on the whole graph. Its denominator remains a nonzero univariate polynomial. -/
theorem polynomialGraphPullback_vanishes_of_principalOpen [IsAlgClosed F] [Finite σ]
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (w : σ → Polynomial F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = polynomialGraphPoint w (x none)) :
    (∀ p ∈ P, polynomialGraphPullback w p = 0) ∧ polynomialGraphPullback w s ≠ 0 := by
  have hinfinite : (principalOpenZeroLocus P s).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  constructor
  · intro p hp
    exact polynomialGraphPullback_eq_zero_of_infinite w hinfinite hgraph p
      (fun x hx ↦ hx.1 p hp)
  · obtain ⟨x, hx⟩ := hinfinite.nonempty
    intro hz
    have heval := eval_polynomialGraphPullback w (x none) s
    rw [hz, Polynomial.eval_zero, ← hgraph x hx] at heval
    exact hx.2 heval.symm

/-- The point on an affine graph with parameter `z` and coordinate slopes `b`. -/
def affineGraphPoint (a b : σ → F) (z : F) : Option σ → F :=
  fun i ↦ i.elim z (fun j ↦ a j + z * b j)

/-- Restriction of a multivariate polynomial to an affine graph. -/
def affineGraphPullback (a b : σ → F) :
    MvPolynomial (Option σ) F →ₐ[F] Polynomial F :=
  aeval (fun i ↦ i.elim Polynomial.X
    (fun j ↦ Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j)))

/-- Restriction followed by evaluation equals evaluation at the graph point. -/
theorem eval_affineGraphPullback (a b : σ → F) (z : F)
    (p : MvPolynomial (Option σ) F) :
    (affineGraphPullback a b p).eval z = aeval (affineGraphPoint a b z) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [affineGraphPullback]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      cases i <;> simp only [affineGraphPullback, affineGraphPoint,
        MvPolynomial.aeval_X, Option.elim, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

/-- Vanishing on infinitely many points of an affine graph implies a polynomial
identity after restriction to the graph. -/
theorem affineGraphPullback_eq_zero_of_infinite
    (a b : σ → F) {S : Set (Option σ → F)} (hS : S.Infinite)
    (hgraph : ∀ x ∈ S, x = affineGraphPoint a b (x none))
    (p : MvPolynomial (Option σ) F) (hzero : ∀ x ∈ S, aeval x p = 0) :
    affineGraphPullback a b p = 0 := by
  have hinj : Set.InjOn (fun x : Option σ → F ↦ x none) S := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (hS.image hinj).mono
  rintro z ⟨x, hx, rfl⟩
  change (affineGraphPullback a b p).eval (x none) = 0
  rw [eval_affineGraphPullback, ← hgraph x hx]
  exact hzero x hx

variable [IsAlgClosed F] [Finite σ]

/-- A positive-dimensional regular principal open lying on an affine graph forces
every polynomial in its prime ideal to vanish identically on the graph. The defining
denominator remains nonzero as a polynomial on that graph. -/
theorem graphPullback_vanishes_of_principalOpen
    {P : Ideal (MvPolynomial (Option σ) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Option σ) F} (hs : s ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (a b : σ → F)
    (hgraph : ∀ x ∈ principalOpenZeroLocus P s,
      x = affineGraphPoint a b (x none)) :
    (∀ p ∈ P, affineGraphPullback a b p = 0) ∧ affineGraphPullback a b s ≠ 0 := by
  have hinfinite : (principalOpenZeroLocus P s).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  constructor
  · intro p hp
    exact affineGraphPullback_eq_zero_of_infinite a b hinfinite hgraph p
      (fun x hx ↦ hx.1 p hp)
  · obtain ⟨x, hx⟩ := hinfinite.nonempty
    intro hz
    have heval := eval_affineGraphPullback a b (x none) s
    rw [hz, Polynomial.eval_zero, ← hgraph x hx] at heval
    exact hx.2 heval.symm

end AffineHilbert
