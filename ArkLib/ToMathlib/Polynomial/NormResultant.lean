/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix

/-! # Resultants as norms in monic polynomial quotients -/

@[expose] public section

noncomputable section

namespace Polynomial

open Matrix

variable {K : Type*} [Field K]

/-- The sign in the linear-factor norm agrees with the Sylvester convention. -/
theorem norm_adjoinRoot_X_sub_C (h : K[X]) (hh : h.Monic) (a : K) :
    Algebra.norm K (AdjoinRoot.mk h (X - C a)) = (-1) ^ h.natDegree * h.eval a := by
  let b := AdjoinRoot.powerBasis' hh
  have hc : (Algebra.leftMulMatrix b.basis b.gen).charpoly = h := by
    rw [charpoly_leftMulMatrix, show b.gen = AdjoinRoot.root h from rfl,
      AdjoinRoot.minpoly_root hh.ne_zero, hh.leadingCoeff]
    simp
  rw [Algebra.norm_eq_matrix_det b.basis, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  have he := congrArg (fun p : K[X] => p.eval a) hc
  rw [Matrix.eval_charpoly] at he
  have hm : Algebra.leftMulMatrix b.basis
      (AdjoinRoot.root h - algebraMap K (AdjoinRoot h) a) =
      -(Matrix.scalar (Fin b.dim) a - Algebra.leftMulMatrix b.basis b.gen) := by
    rw [map_sub, AlgHom.commutes]
    simp [b, Matrix.algebraMap_eq_diagonal, Matrix.scalar]
  change (Algebra.leftMulMatrix b.basis
    (AdjoinRoot.root h - algebraMap K (AdjoinRoot h) a)).det = _
  rw [hm, Matrix.det_neg, Fintype.card_fin, he]
  rfl

/-- Padding the second Sylvester degree does not change a monic first resultant. -/
theorem Monic.resultant_eq_of_le {R : Type*} [CommRing R] {h : R[X]} (hh : h.Monic)
    (g : R[X]) {n : ℕ} (hn : g.natDegree ≤ n) :
    resultant h g h.natDegree n = resultant h g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, hh.coeff_natDegree, one_pow, one_mul]

/-- A monic first input gives a multiplicative resultant even when a factor is zero. -/
theorem Monic.resultant_mul {R : Type*} [CommRing R] {h : R[X]} (hh : h.Monic)
    (g₁ g₂ : R[X]) : resultant h (g₁ * g₂) = resultant h g₁ * resultant h g₂ := by
  rw [← hh.resultant_eq_of_le (g₁ * g₂) natDegree_mul_le,
    resultant_mul_right _ _ _ _ le_rfl]

/-- The norm/resultant identity when the residual splits; the modulus need not split or be
squarefree, and its quotient may have nilpotents. -/
theorem norm_adjoinRoot_eq_resultant_of_splits (h g : K[X]) (hh : h.Monic)
    (hg : g.Splits) : Algebra.norm K (AdjoinRoot.mk h g) = resultant h g := by
  have hC (a : K) : Algebra.norm K (AdjoinRoot.mk h (C a)) = resultant h (C a) := by
    rw [AdjoinRoot.mk_C]
    change Algebra.norm K (algebraMap K (AdjoinRoot h) a) = _
    rw [Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasisAux' hh)]
    simp
  induction hg using Submonoid.closure_induction with
  | mem p hp =>
    obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := hp
    · exact hC a
    · rw [show X + C a = X - C (-a) by simp]
      rw [norm_adjoinRoot_X_sub_C h hh, natDegree_X_sub_C,
        resultant_X_sub_C_right _ _ _ le_rfl]
  | one => exact (by simpa only [C_1] using hC 1)
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy, hh.resultant_mul]

end Polynomial

namespace CompPoly.CPolynomial.NormProducts

variable {R : Type*} [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R]

/-- The executed multiplication determinant is the Sylvester resultant over any coefficient
domain. The monic quotient is not required to be reduced. -/
theorem polynomialNorm_eq_resultant (h g : CPolynomial R) (hh : h.monic) :
    polynomialNorm h g = Polynomial.resultant h.toPoly g.toPoly := by
  let K := FractionRing R
  let q := g.toPoly.map (algebraMap R K)
  let L := q.SplittingField
  let σ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hσ : Function.Injective σ :=
    (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  apply hσ
  rw [polynomialNorm, natDegree_toPoly, map_norm_eq_algebraNorm σ h g hh]
  have hs : (g.toPoly.map σ).Splits := by
    simpa only [σ, L, q, Polynomial.map_map] using Polynomial.SplittingField.splits q
  rw [Polynomial.norm_adjoinRoot_eq_resultant_of_splits _ _
    (((monic_toPoly_iff h).mp hh).map σ) hs]
  rw [Polynomial.natDegree_map_eq_of_injective hσ,
    Polynomial.natDegree_map_eq_of_injective hσ, Polynomial.resultant_map_map]

end CompPoly.CPolynomial.NormProducts

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The finite-free quotient norm equals the Sylvester resultant, without any reducedness
condition on the quotient. -/
theorem norm_adjoinRoot_eq_resultant (h g : R[X]) (hh : h.Monic) :
    Algebra.norm R (AdjoinRoot.mk h g) = resultant h g := by
  classical
  let h' := CompPoly.CPolynomial.ringEquiv.symm h
  let g' := CompPoly.CPolynomial.ringEquiv.symm g
  have eh : h'.toPoly = h := by
    simpa only [CompPoly.CPolynomial.ringEquiv_apply] using
      CompPoly.CPolynomial.ringEquiv.apply_symm_apply h
  have eg : g'.toPoly = g := by
    simpa only [CompPoly.CPolynomial.ringEquiv_apply] using
      CompPoly.CPolynomial.ringEquiv.apply_symm_apply g
  have hh' : h'.monic := by
    rw [CompPoly.CPolynomial.monic_toPoly_iff, eh]
    exact hh
  have he := CompPoly.CPolynomial.NormProducts.polynomialNorm_eq_resultant h' g' hh'
  rw [CompPoly.CPolynomial.NormProducts.polynomialNorm_eq_algebraNorm _ _ hh'] at he
  rw [eh, eg] at he
  exact he

/-- Monic-remainder columns compute the Sylvester resultant over a domain. -/
theorem det_modByMonic_eq_resultant (h g : R[X]) (hh : h.Monic) :
    Matrix.det (fun i j : Fin h.natDegree => ((g * X ^ j.val) %ₘ h).coeff i.val) =
      resultant h g := by
  rw [← norm_adjoinRoot_eq_resultant h g hh,
    Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasisAux' hh)]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [show AdjoinRoot.powerBasisAux' hh j = AdjoinRoot.root h ^ j.val from
    (AdjoinRoot.powerBasis' hh).basis_eq_pow j]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk]

/-- The characteristic polynomial of multiplication by a residual is its Sylvester
resultant against a new scalar variable. -/
theorem charpoly_modByMonic_eq_resultant (h g : R[X]) (hh : h.Monic) :
    Matrix.charpoly (fun i j : Fin h.natDegree => ((g * X ^ j.val) %ₘ h).coeff i.val) =
      resultant (h.map C) (C X - g.map C) := by
  rw [← det_modByMonic_eq_resultant _ _ (hh.map C)]
  have hd : (h.map (C : R →+* R[X])).natDegree = h.natDegree := hh.natDegree_map C
  conv_rhs => erw [← Matrix.det_reindex_self (finCongr hd)]
  unfold Matrix.charpoly
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (if i = j then X else 0) - C (((g * X ^ j.val) %ₘ h).coeff i.val) =
    (((C X - g.map C) * X ^ j.val) %ₘ h.map C).coeff i.val
  rw [sub_mul, sub_modByMonic, ← smul_eq_C_mul, smul_modByMonic]
  have hj : (X ^ j.val : R[X][X]) %ₘ h.map C = X ^ j.val := by
    apply (modByMonic_eq_self_iff (hh.map C)).mpr
    rw [degree_X_pow, degree_eq_natDegree (hh.map C).ne_zero, hd]
    exact_mod_cast j.isLt
  rw [hj, smul_eq_C_mul, coeff_sub, coeff_C_mul, coeff_X_pow]
  rw [← map_X (C : R →+* R[X]), ← Polynomial.map_pow, ← Polynomial.map_mul,
    ← Polynomial.map_modByMonic C hh, coeff_map]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all

end Polynomial
