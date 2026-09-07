/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolation

/-!
# Symbolic interpolation for polynomial curves

For a curve of degree at most `M`, the YZ weight is `(M, 1)`. The integer `zBudget`
is independent of `M`, allowing the real source budget to be rounded as `ceil (M * D_Z)`.
As a special case, a budget `M * dz` gives exactly `M` times the affine counts, so
the same strict affine surplus suffices for every positive `M` at that scaled budget.

## References

- [BCHKS25] Eli Ben-Sasson, Dan Carmon, Ulrich Haböck, Swastik Kopparty, and Shubhangi Saraf.
  On Proximity Gaps for Reed--Solomon Codes. Cryptology ePrint Archive, Paper 2025/2055,
  Lemma 3.1 and Section 4.1. https://eprint.iacr.org/2025/2055
-/

namespace Polynomial.SymbolicInterpolation

open Finset

variable {F : Type*} [Field F]

/-- Curve monomials have weighted YZ budget `M*j + h < zBudget`. -/
def curveMonomialSupport (M k dx dy zBudget : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range dy).sigma fun j => (range (dx - k * j)) ×ˢ (range (zBudget - M * j))

/-- Degree-one curves recover the affine monomial support. -/
@[simp] theorem curveMonomialSupport_one (k dx dy dz : ℕ) :
    curveMonomialSupport 1 k dx dy dz = monomialSupport k dx dy dz := by
  simp [curveMonomialSupport, monomialSupport]

/-- The support records the curve weight on Y rather than on X or Z. -/
@[simp] theorem mem_curveMonomialSupport (M k dx dy zBudget i j h : ℕ) :
    ⟨j, (i, h)⟩ ∈ curveMonomialSupport M k dx dy zBudget ↔
      j < dy ∧ i + k * j < dx ∧ M * j + h < zBudget := by
  simp only [curveMonomialSupport, mem_sigma, mem_product, mem_range]
  omega

/-- Exact curve monomial count for an arbitrary integer Z budget. -/
theorem card_curveMonomialSupport_sum (M k dx dy zBudget : ℕ) :
    (curveMonomialSupport M k dx dy zBudget).card =
      ∑ j ∈ range dy, (dx - k * j) * (zBudget - M * j) := by
  simp [curveMonomialSupport, card_sigma]

/-- The curve support has exactly `M` times the affine number of monomials. -/
theorem card_curveMonomialSupport (M k dx dy dz : ℕ) :
    (curveMonomialSupport M k dx dy (M * dz)).card =
      M * (monomialSupport k dx dy dz).card := by
  simp only [card_curveMonomialSupport_sum, card_monomialSupport, ← Nat.mul_sub_left_distrib]
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- The Z-coefficient budget at Y-Hasse order `s` is `zBudget-M*s`. -/
def curveConstraintSupport (M m zBudget : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range m).sigma fun s => (range (m - s)) ×ˢ (range (zBudget - M * s))

/-- Degree-one curves recover the affine scalar constraints. -/
@[simp] theorem curveConstraintSupport_one (m dz : ℕ) :
    curveConstraintSupport 1 m dz = constraintSupport m dz := by
  simp [curveConstraintSupport, constraintSupport]

/-- Curve constraints lower the Z budget by `M*s`. -/
@[simp] theorem mem_curveConstraintSupport (M m zBudget r s d : ℕ) :
    ⟨s, (r, d)⟩ ∈ curveConstraintSupport M m zBudget ↔
      r + s < m ∧ d + M * s < zBudget := by
  simp only [curveConstraintSupport, mem_sigma, mem_product, mem_range]
  omega

/-- Exact scalar constraint count for an arbitrary integer Z budget. -/
theorem card_curveConstraintSupport_sum (M m zBudget : ℕ) :
    (curveConstraintSupport M m zBudget).card =
      ∑ s ∈ range m, (m - s) * (zBudget - M * s) := by
  simp [curveConstraintSupport, card_sigma]

/-- The curve system has exactly `M` times the affine number of scalar equations per point. -/
theorem card_curveConstraintSupport (M m dz : ℕ) :
    (curveConstraintSupport M m (M * dz)).card = M * (constraintSupport m dz).card := by
  simp only [card_curveConstraintSupport_sum, card_constraintSupport, ← Nat.mul_sub_left_distrib]
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  ring

/-- Any strict affine surplus survives scaling by a positive curve degree. -/
theorem curve_card_surplus (M k dx dy dz n m : ℕ) (hM : 0 < M)
    (hcount : n * (constraintSupport m dz).card < (monomialSupport k dx dy dz).card) :
    n * (curveConstraintSupport M m (M * dz)).card <
      (curveMonomialSupport M k dx dy (M * dz)).card := by
  rw [card_curveConstraintSupport, card_curveMonomialSupport]
  simpa only [mul_left_comm n M] using Nat.mul_lt_mul_of_pos_left hcount hM

/-- The weighted support kills every high Z coefficient after degree-`M` substitution. -/
theorem hasseConstraint_monomial_eq_zero_of_degree_le (i j h r s d M dz : ℕ)
    (x : F) (y : Polynomial F) (hy : y.natDegree ≤ M)
    (hbudget : M * j + h < dz) (hd : dz ≤ d + M * s) :
    hasseConstraint (C x) y r s d (monomial j (monomial i (monomial h 1))) = 0 := by
  change (((Bivariate.shift (monomial j (monomial i (monomial h 1)))
    (C x) y).coeff s).coeff r).coeff d = 0
  rw [shift_monomial_coeff]
  by_cases hsj : j < s
  · simp [Nat.choose_eq_zero_of_lt hsj]
  · have hdegree :
        (monomial h (x ^ (i - r) * (i.choose r : F) * (j.choose s : F)) *
          y ^ (j - s)).natDegree ≤ h + (j - s) * M := by
      exact natDegree_mul_le.trans (add_le_add (natDegree_monomial_le _)
        (natDegree_pow_le_of_le (j - s) hy))
    have heq : (j - s) * M = M * j - M * s := by
      rw [Nat.sub_mul, Nat.mul_comm j, Nat.mul_comm s]
    exact coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by
      rw [heq]
      have hle := Nat.mul_le_mul_left M (Nat.le_of_not_gt hsj)
      omega))

/-- Exact scalar surplus constructs a curve interpolant for an arbitrary integer Z budget.
The conclusion includes every Hasse coefficient and the weighted monomial support. -/
theorem exists_curve_polynomial_of_card_surplus (M k dx dy zBudget n m : ℕ)
    (x : Fin n → F) (y : Fin n → Polynomial F) (hy : ∀ a, (y a).natDegree ≤ M)
    (hcount : n * (curveConstraintSupport M m zBudget).card <
      (curveMonomialSupport M k dx dy zBudget).card) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        j < dy ∧ i + k * j < dx ∧ M * j + h < zBudget) ∧
      ∀ a r s, r + s < m → ((Bivariate.shift Q (C (x a)) (y a)).coeff s).coeff r = 0 := by
  classical
  let S := curveMonomialSupport M k dx dy zBudget
  let T := curveConstraintSupport M m zBudget
  let L : (S → F) →ₗ[F] (Fin n × T → F) := LinearMap.pi fun q =>
    hasseConstraint (C (x q.1)) (y q.1) q.2.1.2.1 q.2.1.1 q.2.1.2.2 ∘ₗ encode S
  have hfinrank : Module.finrank F (Fin n × T → F) < Module.finrank F (S → F) := by
    simpa [Module.finrank_fintype_fun_eq_card, S, T] using hcount
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfinrank)
  refine ⟨encode S c, encode_ne_zero S hc0, ?_, ?_⟩
  · intro i j h hnz
    apply (mem_curveMonomialSupport M k dx dy zBudget i j h).mp
    by_contra hnot
    exact hnz (coeff_encode_eq_zero_of_not_mem S c i j h hnot)
  · intro a r s hrs
    ext d
    change hasseConstraint (C (x a)) (y a) r s d (encode S c) = 0
    by_cases hd : d + M * s < zBudget
    · have hmem : ⟨s, (r, d)⟩ ∈ T :=
        (mem_curveConstraintSupport M m zBudget r s d).mpr ⟨hrs, hd⟩
      exact congrFun (LinearMap.mem_ker.mp hc) (a, ⟨⟨s, (r, d)⟩, hmem⟩)
    · rw [encode_eq_sum, map_sum]
      apply sum_eq_zero
      intro q _
      rw [map_smul, hasseConstraint_monomial_eq_zero_of_degree_le _ _ _ _ _ _ M zBudget
        (x a) (y a) (hy a)]
      · simp
      · exact ((mem_curveMonomialSupport _ _ _ _ _ _ _ _).mp q.2).2.2
      · exact Nat.le_of_not_gt hd

/-- The exact affine surplus suffices for a positive-degree curve at the scaled integer
budget `M*dz`. This is distinct from rounding a real budget after multiplication by `M`. -/
theorem exists_curve_polynomial_of_affine_card_surplus (M k dx dy dz n m : ℕ) (hM : 0 < M)
    (x : Fin n → F) (y : Fin n → Polynomial F) (hy : ∀ a, (y a).natDegree ≤ M)
    (hcount : n * (constraintSupport m dz).card < (monomialSupport k dx dy dz).card) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        j < dy ∧ i + k * j < dx ∧ M * j + h < M * dz) ∧
      ∀ a r s, r + s < m → ((Bivariate.shift Q (C (x a)) (y a)).coeff s).coeff r = 0 :=
  exists_curve_polynomial_of_card_surplus M k dx dy (M * dz) n m x y hy
    (curve_card_surplus M k dx dy dz n m hM hcount)

end Polynomial.SymbolicInterpolation
