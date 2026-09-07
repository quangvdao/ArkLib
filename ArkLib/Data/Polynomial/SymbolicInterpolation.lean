/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SymbolicInterpolationSupport
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear algebra for symbolic interpolation

Coefficient vectors are encoded in the semantic order Y, X, Z. The linear constraint
map extracts scalar coefficients after shifting X and Y to symbolic interpolation points.

## References

- [BCHKS25] Eli Ben-Sasson, Dan Carmon, Ulrich Haböck, Swastik Kopparty, and Shubhangi Saraf.
  On Proximity Gaps for Reed--Solomon Codes. Cryptology ePrint Archive, Paper 2025/2055,
  Lemma 3.1. https://eprint.iacr.org/2025/2055
-/

namespace Polynomial.SymbolicInterpolation

open Finset

variable {F : Type*} [Field F]

/-- Encode a vector on a finite monomial support in `F[Z][X][Y]`. -/
noncomputable def encode (S : Finset (Σ _ : ℕ, ℕ × ℕ)) :
    (S → F) →ₗ[F] Polynomial (Polynomial (Polynomial F)) :=
  Finsupp.linearCombination F (fun q : S =>
    monomial q.1.1 (monomial q.1.2.1 (monomial q.1.2.2 1))) ∘ₗ
      (Finsupp.linearEquivFunOnFinite F F S).symm.toLinearMap

/-- The encoding is the finite linear combination of nested monomials. -/
theorem encode_eq_sum (S : Finset (Σ _ : ℕ, ℕ × ℕ)) (c : S → F) :
    encode S c = ∑ q : S, c q •
      monomial q.1.1 (monomial q.1.2.1 (monomial q.1.2.2 1)) := by
  classical
  unfold encode
  rw [Finsupp.linearCombination_eq_fintype_linearCombination,
    Fintype.linearCombination_apply]

/-- Every stored scalar coefficient is recovered at its original three exponents. -/
theorem coeff_encode (S : Finset (Σ _ : ℕ, ℕ × ℕ)) (c : S → F) (q : S) :
    (((encode S c).coeff q.1.1).coeff q.1.2.1).coeff q.1.2.2 = c q := by
  classical
  rw [encode_eq_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
  rw [sum_eq_single q]
  · simp [smul_monomial]
  · intro r _ hr
    have hne : r.1.1 ≠ q.1.1 ∨ r.1.2.1 ≠ q.1.2.1 ∨ r.1.2.2 ≠ q.1.2.2 := by
      by_contra h
      push Not at h
      apply hr
      apply Subtype.ext
      rcases r with ⟨⟨rj, ri, rh⟩, _⟩
      rcases q with ⟨⟨qj, qi, qh⟩, _⟩
      simp only at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    rcases hne with h | h | h
    · simp [smul_monomial, coeff_monomial, h]
    · by_cases hj : r.1.1 = q.1.1 <;> simp [smul_monomial, coeff_monomial, h, hj]
    · by_cases hj : r.1.1 = q.1.1 <;> by_cases hi : r.1.2.1 = q.1.2.1 <;>
        simp [smul_monomial, coeff_monomial, h, hj, hi]
  · simp

/-- Encoding cannot turn a nonzero coefficient vector into the zero polynomial. -/
theorem encode_ne_zero (S : Finset (Σ _ : ℕ, ℕ × ℕ)) {c : S → F} (hc : c ≠ 0) :
    encode S c ≠ 0 := by
  intro hz
  apply hc
  funext q
  have h := coeff_encode S c q
  simpa [hz] using h.symm

/-- Encoding has no nonzero scalar coefficient outside its prescribed support. -/
theorem coeff_encode_eq_zero_of_not_mem (S : Finset (Σ _ : ℕ, ℕ × ℕ))
    (c : S → F) (i j h : ℕ) (hnot : ⟨j, (i, h)⟩ ∉ S) :
    (((encode S c).coeff j).coeff i).coeff h = 0 := by
  classical
  rw [encode_eq_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
  apply sum_eq_zero
  intro q _
  by_cases hj : q.1.1 = j
  · by_cases hi : q.1.2.1 = i
    · by_cases hh : q.1.2.2 = h
      · exfalso
        apply hnot
        have heq : q.1 = ⟨j, (i, h)⟩ := by
          rcases q with ⟨⟨qj, qi, qh⟩, _⟩
          simp only at hj hi hh ⊢
          subst qj
          subst qi
          subst qh
          rfl
        rw [← heq]
        exact q.2
      · simp [smul_monomial, coeff_monomial, hj, hi, hh]
    · simp [smul_monomial, coeff_monomial, hj, hi]
  · simp [smul_monomial, coeff_monomial, hj]

/-- Every nonzero coefficient of the constructed polynomial obeys all three support bounds. -/
theorem encode_support_bounds (k dx dy dz : ℕ) (c : monomialSupport k dx dy dz → F)
    (i j h : ℕ) (hc : (((encode (monomialSupport k dx dy dz) c).coeff j).coeff i).coeff h ≠ 0) :
    j < dy ∧ i + k * j < dx ∧ j + h < dz := by
  apply (mem_monomialSupport k dx dy dz i j h).mp
  by_contra hnot
  exact hc (coeff_encode_eq_zero_of_not_mem _ c i j h hnot)

/-- One scalar Hasse constraint: X order `r`, Y order `s`, and Z coefficient `d`. -/
noncomputable def hasseConstraint (x y : Polynomial F) (r s d : ℕ) :
    Polynomial (Polynomial (Polynomial F)) →ₗ[F] F where
  toFun Q := ((((Bivariate.shift Q x y).coeff s).coeff r).coeff d)
  map_add' Q R := by simp [Bivariate.shift]
  map_smul' a Q := by simp [Bivariate.shift]

/-- The finite scalar system at symbolic interpolation points. -/
noncomputable def constraintMap (S : Finset (Σ _ : ℕ, ℕ × ℕ))
    (n m dz : ℕ) (x y : Fin n → Polynomial F) :
    (S → F) →ₗ[F] (Fin n × constraintSupport m dz → F) :=
  LinearMap.pi fun q =>
    hasseConstraint (x q.1) (y q.1) q.2.1.2.1 q.2.1.1 q.2.1.2.2 ∘ₗ encode S

/-- Exact scalar surplus gives a nonzero encoded polynomial satisfying every constraint
in the finite system. Controlling the remaining Z coefficients is a separate degree step. -/
theorem exists_nonzero_finite_constraints (k dx dy dz n m : ℕ)
    (x y : Fin n → Polynomial F)
    (hcount : n * (constraintSupport m dz).card <
      (monomialSupport k dx dy dz).card) :
    ∃ c : monomialSupport k dx dy dz → F,
      encode (monomialSupport k dx dy dz) c ≠ 0 ∧
      ∀ a r s d, r + s < m → d + s < dz →
        hasseConstraint (x a) (y a) r s d (encode (monomialSupport k dx dy dz) c) = 0 := by
  classical
  let S := monomialSupport k dx dy dz
  have hfinrank : Module.finrank F (Fin n × constraintSupport m dz → F) <
      Module.finrank F (S → F) := by
    simpa [Module.finrank_fintype_fun_eq_card, S] using hcount
  have hker : LinearMap.ker (constraintMap S n m dz x y) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨c, encode_ne_zero S hc0, ?_⟩
  intro a r s d hrs hds
  have hmem : ⟨s, (r, d)⟩ ∈ constraintSupport m dz :=
    (mem_constraintSupport m dz r s d).mpr ⟨hrs, hds⟩
  exact congrFun (LinearMap.mem_ker.mp hc) (a, ⟨⟨s, (r, d)⟩, hmem⟩)

private theorem innerMonomial_shift_coeff (i h r : ℕ) (x : F) :
    (((monomial i (monomial h 1) : Polynomial (Polynomial F)).comp
      (Polynomial.X + C (C x))).coeff r) =
        monomial h (x ^ (i - r) * (i.choose r : F)) := by
  rw [monomial_comp, coeff_C_mul, coeff_X_add_C_pow]
  rw [← C_eq_natCast, ← map_pow, ← map_mul, monomial_mul_C, one_mul]

/-- Shifting one nested monomial gives the expected two Hasse binomial factors. -/
theorem shift_monomial_coeff (i j h r s : ℕ) (x : F) (y : Polynomial F) :
    ((Bivariate.shift (monomial j (monomial i (monomial h 1))) (C x) y).coeff s).coeff r =
      monomial h (x ^ (i - r) * (i.choose r : F) * (j.choose s : F)) * y ^ (j - s) := by
  classical
  have hmap : map (compRingHom (Polynomial.X + C (C x)))
      (Polynomial.X + C (C y)) = Polynomial.X + C (C y) := by
    simp [coe_compRingHom_apply]
  unfold Bivariate.shift
  rw [monomial_comp, Polynomial.map_mul, map_C, Polynomial.map_pow, hmap]
  rw [coeff_C_mul, coeff_X_add_C_pow, ← C_eq_natCast]
  rw [← map_pow, ← map_mul, coeff_mul_C]
  rw [coe_compRingHom_apply, innerMonomial_shift_coeff, ← C_eq_natCast]
  calc
    monomial h (x ^ (i - r) * (i.choose r : F)) * (y ^ (j - s) * C (j.choose s : F)) =
        (monomial h (x ^ (i - r) * (i.choose r : F)) * C (j.choose s : F)) *
          y ^ (j - s) := by ring
    _ = _ := by rw [monomial_mul_C]

/-- Affine symbolic substitution leaves no Z coefficient at or above `dz - s`.
The Y-Hasse order really reduces the budget; this is the saving in the BCHKS25 count. -/
theorem hasseConstraint_monomial_eq_zero (i j h r s d dz : ℕ)
    (x : F) (y : Polynomial F) (hy : y.natDegree ≤ 1)
    (hbudget : j + h < dz) (hd : dz ≤ d + s) :
    hasseConstraint (C x) y r s d (monomial j (monomial i (monomial h 1))) = 0 := by
  change (((Bivariate.shift (monomial j (monomial i (monomial h 1)))
    (C x) y).coeff s).coeff r).coeff d = 0
  rw [shift_monomial_coeff]
  by_cases hsj : j < s
  · simp [Nat.choose_eq_zero_of_lt hsj]
  · have hdegree :
        (monomial h (x ^ (i - r) * (i.choose r : F) * (j.choose s : F)) *
          y ^ (j - s)).natDegree ≤ h + (j - s) := by
      exact natDegree_mul_le.trans (add_le_add (natDegree_monomial_le _)
        (by simpa using natDegree_pow_le_of_le (j - s) hy))
    exact coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by omega))

/-- All high Z coefficients vanish after an affine symbolic substitution. -/
theorem hasseConstraint_encode_eq_zero (k dx dy dz r s d : ℕ)
    (c : monomialSupport k dx dy dz → F) (x : F) (y : Polynomial F)
    (hy : y.natDegree ≤ 1) (hd : dz ≤ d + s) :
    hasseConstraint (C x) y r s d (encode (monomialSupport k dx dy dz) c) = 0 := by
  classical
  rw [encode_eq_sum, map_sum]
  apply sum_eq_zero
  intro q _
  rw [map_smul, hasseConstraint_monomial_eq_zero _ _ _ _ _ _ dz x y hy]
  · simp
  · exact ((mem_monomialSupport _ _ _ _ _ _ _).mp q.2).2.2
  · exact hd

/-- Under exact surplus, there is a nonzero polynomial whose Hasse coefficients of total
order below `m` vanish at every affine symbolic point. -/
theorem exists_nonzero_hasse_vanishing (k dx dy dz n m : ℕ)
    (x : Fin n → F) (y : Fin n → Polynomial F) (hy : ∀ a, (y a).natDegree ≤ 1)
    (hcount : n * (constraintSupport m dz).card <
      (monomialSupport k dx dy dz).card) :
    ∃ c : monomialSupport k dx dy dz → F,
      encode (monomialSupport k dx dy dz) c ≠ 0 ∧
      ∀ a r s, r + s < m →
        ((Bivariate.shift (encode (monomialSupport k dx dy dz) c)
          (C (x a)) (y a)).coeff s).coeff r = 0 := by
  obtain ⟨c, hc, hv⟩ := exists_nonzero_finite_constraints k dx dy dz n m
    (fun a => C (x a)) y hcount
  refine ⟨c, hc, ?_⟩
  intro a r s hrs
  ext d
  change hasseConstraint (C (x a)) (y a) r s d _ = 0
  by_cases hd : d + s < dz
  · exact hv a r s d hrs hd
  · exact hasseConstraint_encode_eq_zero k dx dy dz r s d c (x a) (y a) (hy a)
      (Nat.le_of_not_gt hd)

/-- Symbolic interpolation under the exact support surplus: the resulting nonzero
polynomial has the non-Cartesian support budgets and all required Hasse vanishings.
No assumption on the field characteristic or distinctness of the points is needed. -/
theorem exists_polynomial_of_card_surplus (k dx dy dz n m : ℕ)
    (x : Fin n → F) (y : Fin n → Polynomial F) (hy : ∀ a, (y a).natDegree ≤ 1)
    (hcount : n * (constraintSupport m dz).card <
      (monomialSupport k dx dy dz).card) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)), Q ≠ 0 ∧
      (∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 →
        j < dy ∧ i + k * j < dx ∧ j + h < dz) ∧
      ∀ a r s, r + s < m → ((Bivariate.shift Q (C (x a)) (y a)).coeff s).coeff r = 0 := by
  obtain ⟨c, hc, hv⟩ := exists_nonzero_hasse_vanishing k dx dy dz n m x y hy hcount
  exact ⟨encode (monomialSupport k dx dy dz) c, hc,
    encode_support_bounds k dx dy dz c, hv⟩

end Polynomial.SymbolicInterpolation
