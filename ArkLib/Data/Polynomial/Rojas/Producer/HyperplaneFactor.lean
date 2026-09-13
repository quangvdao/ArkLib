/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Polynomial.Div

/-!
# Divisibility by an affine hyperplane

This file packages polynomial division in one distinguished variable as a
multivariate hyperplane-factor theorem.  The vanishing hypothesis is an
identity after symbolic substitution: the constant coordinate is replaced by
the negative linear combination of the remaining coordinates.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.HyperplaneFactor

open scoped BigOperators
open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The symbolic value substituted for the constant-coordinate variable on
the hyperplane `u₀ + ∑ i, point i * uᵢ₊₁ = 0`. -/
noncomputable def hyperplaneRoot (point : Fin n → R) : MvPolynomial (Fin n) R :=
  -∑ i, C (point i) * X i

/-- The affine linear form `u₀ + ∑ i, point i * uᵢ₊₁`. -/
noncomputable def affineLinearForm (point : Fin n → R) : MvPolynomial (Fin (n + 1)) R :=
  (finSuccEquiv R n).symm
    (Polynomial.X - Polynomial.C (hyperplaneRoot point))

/-- Substitute `u₀ = -∑ i, point i * uᵢ₊₁`, retaining the other variables
symbolically. -/
noncomputable def hyperplaneSubstitution (point : Fin n → R)
    (p : MvPolynomial (Fin (n + 1)) R) : MvPolynomial (Fin n) R :=
  Polynomial.eval (hyperplaneRoot point) (finSuccEquiv R n p)

theorem finSuccEquiv_affineLinearForm (point : Fin n → R) :
    finSuccEquiv R n (affineLinearForm point) =
      Polynomial.X - Polynomial.C (hyperplaneRoot point) := by
  simp [affineLinearForm]

theorem affineLinearForm_eq (point : Fin n → R) :
    affineLinearForm point = X 0 + ∑ i, C (point i) * X i.succ := by
  apply (finSuccEquiv R n).injective
  rw [finSuccEquiv_affineLinearForm]
  simp only [map_add, map_sum, map_mul, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    hyperplaneRoot, Polynomial.C_neg, Polynomial.C_sum, Polynomial.C_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [finSuccEquiv_apply]
  simp

/-- An affine hyperplane form divides a polynomial exactly when symbolic
substitution of the hyperplane equation makes the polynomial zero. -/
theorem affineLinearForm_dvd_iff (point : Fin n → R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    affineLinearForm point ∣ p ↔ hyperplaneSubstitution point p = 0 := by
  rw [← map_dvd_iff (finSuccEquiv R n), finSuccEquiv_affineLinearForm,
    Polynomial.dvd_iff_isRoot]
  rfl

/-- Symbolic vanishing on an affine hyperplane implies divisibility by its
defining linear form. -/
theorem affineLinearForm_dvd_of_substitution_eq_zero (point : Fin n → R)
    (p : MvPolynomial (Fin (n + 1)) R)
    (hvanish : hyperplaneSubstitution point p = 0) :
    affineLinearForm point ∣ p :=
  (affineLinearForm_dvd_iff point p).2 hvanish

end ArkLib.Rojas.Producer.HyperplaneFactor
