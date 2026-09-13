/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantMap
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Correctness of the first-subresultant coordinate relation

This module proves directly from the stored deleted-column matrices that a common root `z` of
the two input polynomials satisfies `R₁ + R₀ z = 0`.  The proof is a fraction-free instance of
Cramer's rule and therefore does not require the first subresultant to be normalized as a gcd.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.SubresultantMap

open CompPoly CompPoly.CPolynomial
open ArkLib.UnivariateRepresentation

/-- Fraction-free Cramer's rule: a known solution is sent to the determinant-scaled solution. -/
private theorem cramer_of_mulVec_eq
    {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (x b : Fin n → R) (h : Matrix.mulVec A x = b) :
    A.cramer b = A.det • x := by
  rw [Matrix.cramer_eq_adjugate_mulVec, ← h, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The two maximal minors of a `k × (k+1)` matrix obey the expected Cramer relation whenever
the nonconstant power vector solves the system obtained from its constant column. -/
theorem deletedMinors_relation_of_mulVec_eq
    {R : Type*} [CommRing R] {k : ℕ} (hk : 0 < k)
    (matrix : Matrix (Fin k) (Fin (k + 1)) R) (z : R)
    (hsolve : Matrix.mulVec (minorOmitting matrix ⟨0, by omega⟩)
        (fun j : Fin k ↦ z ^ (j.val + 1)) =
      fun i ↦ -matrix i ⟨0, by omega⟩) :
    (minorOmitting matrix ⟨1, by omega⟩).det +
        (minorOmitting matrix ⟨0, by omega⟩).det * z = 0 := by
  let A := minorOmitting matrix ⟨0, by omega⟩
  let B := minorOmitting matrix ⟨1, by omega⟩
  let x : Fin k → R := fun j ↦ z ^ (j.val + 1)
  let b : Fin k → R := fun i ↦ -matrix i ⟨0, by omega⟩
  have hcramer := congrFun (cramer_of_mulVec_eq A x b hsolve) ⟨0, hk⟩
  have hupdate : A.updateCol ⟨0, hk⟩ b =
      B.updateCol ⟨0, hk⟩ ((-1 : R) • (fun i ↦ B i ⟨0, hk⟩)) := by
    ext i j
    by_cases hj : j = ⟨0, hk⟩
    · subst j
      have hcolumn : (⟨1, by omega⟩ : Fin (k + 1)).succAbove ⟨0, hk⟩ =
          ⟨0, by omega⟩ := by
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · change (0 : ℕ) < 1
          omega
      simp [A, B, b, minorOmitting, hcolumn]
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero fun hzero ↦ hj (Fin.ext hzero)
      have hlinear : (⟨1, by omega⟩ : Fin (k + 1)).succAbove j = j.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        exact hjpos
      have hconstant : (⟨0, by omega⟩ : Fin (k + 1)).succAbove j = j.succ := by
        exact Fin.zero_succAbove j
      simp only [Matrix.updateCol_apply, hj, ↓reduceIte, A, B, minorOmitting,
        Matrix.of_apply]
      rw [hconstant, hlinear]
  rw [Matrix.cramer_apply, hupdate, Matrix.det_updateCol_smul,
    Matrix.updateCol_eq_self] at hcramer
  rw [Pi.smul_apply, smul_eq_mul] at hcramer
  dsimp only [x] at hcramer
  simp only [zero_add, pow_one] at hcramer
  change (-1 : R) * B.det = A.det * z at hcramer
  change B.det + A.det * z = 0
  rw [← hcramer]
  ring

/-- Every row of the stored rectangular matrix annihilates the full power vector at a common
root.  The first block consists of shifts of `g`; the second block consists of shifts of `f`. -/
theorem firstSubresultantMatrix_mulVec_eq_zero
    {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) (z : R)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hfroot : f.toPoly.eval z = 0) (hgroot : g.toPoly.eval z = 0) :
    Matrix.mulVec (firstSubresultantMatrix f g)
      (fun c : Fin (firstSubresultantSize f g + 1) ↦ z ^ c.val) = 0 := by
  funext row
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  let d₁ := f.natDegree
  let d₂ := g.natDegree
  let k := firstSubresultantSize f g
  by_cases hrow : row.val < d₁ - 1
  · have hgne : g.toPoly ≠ 0 := by
      intro hzero
      have : g.natDegree = 0 := by
        rw [CPolynomial.natDegree_toPoly, hzero, Polynomial.natDegree_zero]
      omega
    have hbound : (Polynomial.X ^ row.val * g.toPoly).natDegree < k + 1 := by
      rw [Polynomial.natDegree_X_pow_mul (p := g.toPoly) row.val hgne,
        ← CPolynomial.natDegree_toPoly]
      dsimp only [k, firstSubresultantSize, d₁, d₂] at *
      omega
    have hentry : ∀ c : Fin (k + 1),
        firstSubresultantMatrix f g row c =
          (Polynomial.X ^ row.val * g.toPoly).coeff c.val := by
      intro c
      rw [Polynomial.coeff_X_pow_mul']
      simp only [firstSubresultantMatrix, Matrix.of_apply]
      rw [dif_pos (show row.val < f.natDegree - 1 by simpa only [d₁] using hrow)]
      change (if _hleft : row.val ≤ c.val then
          if c.val ≤ row.val + d₂ then g.coeff (c.val - row.val) else 0 else 0) = _
      by_cases hleft : row.val ≤ c.val
      · by_cases hright : c.val ≤ row.val + d₂
        · simp [hleft, hright, CPolynomial.coeff_toPoly]
        · have hzero : g.toPoly.coeff (c.val - row.val) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [← CPolynomial.natDegree_toPoly]
            omega
          simp [hleft, hright, hzero]
      · simp [hleft]
    rw [show (∑ c, firstSubresultantMatrix f g row c * z ^ c.val) =
        ∑ c : Fin (k + 1),
          (Polynomial.X ^ row.val * g.toPoly).coeff c.val * z ^ c.val by
      apply Finset.sum_congr rfl
      intro c _
      rw [hentry c]]
    calc
      (∑ c : Fin (k + 1),
          (Polynomial.X ^ row.val * g.toPoly).coeff c.val * z ^ c.val) =
          ∑ i ∈ Finset.range (k + 1),
            (Polynomial.X ^ row.val * g.toPoly).coeff i * z ^ i := by
        simpa using Fin.sum_univ_eq_sum_range
          (fun i ↦ (Polynomial.X ^ row.val * g.toPoly).coeff i * z ^ i) (k + 1)
      _ = (Polynomial.X ^ row.val * g.toPoly).eval z :=
        (Polynomial.eval_eq_sum_range' hbound z).symm
      _ = 0 := by simp [hgroot]
  · let shift := row.val - (d₁ - 1)
    have hfne : f.toPoly ≠ 0 := by
      intro hzero
      have : f.natDegree = 0 := by
        rw [CPolynomial.natDegree_toPoly, hzero, Polynomial.natDegree_zero]
      omega
    have hrowBound : row.val < k := row.isLt
    have hshiftBound : shift < d₂ - 1 := by
      dsimp only [shift, k, firstSubresultantSize, d₁, d₂] at *
      omega
    have hbound : (Polynomial.X ^ shift * f.toPoly).natDegree < k + 1 := by
      rw [Polynomial.natDegree_X_pow_mul (p := f.toPoly) shift hfne,
        ← CPolynomial.natDegree_toPoly]
      dsimp only [shift, k, firstSubresultantSize, d₁, d₂] at *
      omega
    have hentry : ∀ c : Fin (k + 1),
        firstSubresultantMatrix f g row c =
          (Polynomial.X ^ shift * f.toPoly).coeff c.val := by
      intro c
      rw [Polynomial.coeff_X_pow_mul']
      simp only [firstSubresultantMatrix, Matrix.of_apply]
      rw [dif_neg (show ¬row.val < f.natDegree - 1 by simpa only [d₁] using hrow)]
      change (if _hleft : shift ≤ c.val then
          if c.val ≤ shift + d₁ then f.coeff (c.val - shift) else 0 else 0) = _
      by_cases hleft : shift ≤ c.val
      · by_cases hright : c.val ≤ shift + d₁
        · simp [hleft, hright, CPolynomial.coeff_toPoly]
        · have hzero : f.toPoly.coeff (c.val - shift) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [← CPolynomial.natDegree_toPoly]
            omega
          simp [hleft, hright, hzero]
      · simp [hleft]
    rw [show (∑ c, firstSubresultantMatrix f g row c * z ^ c.val) =
        ∑ c : Fin (k + 1),
          (Polynomial.X ^ shift * f.toPoly).coeff c.val * z ^ c.val by
      apply Finset.sum_congr rfl
      intro c _
      rw [hentry c]]
    calc
      (∑ c : Fin (k + 1),
          (Polynomial.X ^ shift * f.toPoly).coeff c.val * z ^ c.val) =
          ∑ i ∈ Finset.range (k + 1),
            (Polynomial.X ^ shift * f.toPoly).coeff i * z ^ i := by
        simpa using Fin.sum_univ_eq_sum_range
          (fun i ↦ (Polynomial.X ^ shift * f.toPoly).coeff i * z ^ i) (k + 1)
      _ = (Polynomial.X ^ shift * f.toPoly).eval z :=
        (Polynomial.eval_eq_sum_range' hbound z).symm
      _ = 0 := by simp [hfroot]

/-- A common root supplies the linear system used in the deleted-minor Cramer argument. -/
theorem firstSubresultantMatrix_mulVec_eq_neg_constant
    {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) (z : R)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hfroot : f.toPoly.eval z = 0) (hgroot : g.toPoly.eval z = 0)
    (hk : 0 < firstSubresultantSize f g) :
    Matrix.mulVec
        (minorOmitting (firstSubresultantMatrix f g) ⟨0, by omega⟩)
        (fun j : Fin (firstSubresultantSize f g) ↦ z ^ (j.val + 1)) =
      fun i ↦ -firstSubresultantMatrix f g i ⟨0, by omega⟩ := by
  have hfull := firstSubresultantMatrix_mulVec_eq_zero f g z hfpos hgpos hfroot hgroot
  funext row
  have hrow := congrFun hfull row
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow ⊢
  rw [Fin.sum_univ_succ] at hrow
  have htail :
      (∑ j : Fin (firstSubresultantSize f g),
          firstSubresultantMatrix f g row j.succ * z ^ j.succ.val) =
        ∑ j : Fin (firstSubresultantSize f g),
          minorOmitting (firstSubresultantMatrix f g) ⟨0, by omega⟩ row j *
            z ^ (j.val + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [minorOmitting, Fin.zero_succAbove]
  rw [htail] at hrow
  simpa using eq_neg_of_add_eq_zero_right hrow

/-- Direct first-subresultant root relation.  It uses only positive input degrees and a common
root, and does not assert any normalization or association with `EuclideanDomain.gcd`. -/
theorem firstSubresultant_relation_of_common_root
    {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (f g : CPolynomial R) (z : R)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hfroot : f.toPoly.eval z = 0) (hgroot : g.toPoly.eval z = 0) :
    (firstSubresultant f g).2 + (firstSubresultant f g).1 * z = 0 := by
  let k := firstSubresultantSize f g
  by_cases hk : k = 0
  · have hfdegree : f.natDegree = 1 := by
      dsimp only [k, firstSubresultantSize] at hk
      omega
    have hgdegree : g.natDegree = 1 := by
      dsimp only [k, firstSubresultantSize] at hk
      omega
    rw [firstSubresultant_of_natDegree_eq_one f g hfdegree hgdegree]
    have heval := Polynomial.eval_eq_sum_range'
      (p := f.toPoly) (n := 2) ( (by
        rw [← CPolynomial.natDegree_toPoly, hfdegree]
        omega)) z
    rw [hfroot] at heval
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
      pow_one] at heval
    rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly] at heval
    exact heval.symm
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [firstSubresultant]
    rw [dif_neg hk]
    apply deletedMinors_relation_of_mulVec_eq hkpos
    exact firstSubresultantMatrix_mulVec_eq_neg_constant f g z hfpos hgpos hfroot hgroot hkpos

/-- Positive stored degree implies that conversion to `Polynomial` is nonzero. -/
private theorem toPoly_ne_zero_of_natDegree_pos
    {R : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
    (q : CPolynomial R) (hq : 0 < q.natDegree) : q.toPoly ≠ 0 := by
  intro hz
  have hdegree : q.toPoly.natDegree = 0 := by rw [hz, Polynomial.natDegree_zero]
  rw [← CPolynomial.natDegree_toPoly] at hdegree
  omega

/-- The row-kernel theorem after mapping coefficients.  It uses stored degree bounds, so the
coefficient specialization may lower degree. -/
theorem firstSubresultantMatrix_map_mulVec_eq_zero
    {R S : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
    [CommRing S] (φ : R →+* S) (f g : CPolynomial R) (z : S)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hfroot : f.toPoly.eval₂ φ z = 0) (hgroot : g.toPoly.eval₂ φ z = 0) :
    Matrix.mulVec ((firstSubresultantMatrix f g).map φ) (fun j ↦ z ^ j.val) = 0 := by
  funext row
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply]
  let d₁ := f.natDegree
  let d₂ := g.natDegree
  let k := firstSubresultantSize f g
  by_cases hrow : row.val < d₁ - 1
  · have hgpoly : g.toPoly ≠ 0 := toPoly_ne_zero_of_natDegree_pos g hgpos
    have hbound : (Polynomial.X ^ row.val * g.toPoly).natDegree < k + 1 := by
      rw [Polynomial.natDegree_X_pow_mul row.val hgpoly, ← CPolynomial.natDegree_toPoly]
      dsimp [k, firstSubresultantSize, d₁, d₂]
      omega
    have hgshift : (Polynomial.X ^ row.val * g.toPoly).eval₂ φ z = 0 := by
      simp [Polynomial.eval₂_mul, hgroot]
    rw [Polynomial.eval₂_eq_sum_range' φ hbound z] at hgshift
    have hsum :
        (∑ col : Fin (k + 1),
          φ ((Polynomial.X ^ row.val * g.toPoly).coeff col.val) * z ^ col.val) = 0 := by
      have heq := Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
        φ ((Polynomial.X ^ row.val * g.toPoly).coeff i) * z ^ i) (k + 1)
      exact heq.trans hgshift
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro col _
    congr 2
    dsimp [d₁, d₂] at hrow ⊢
    simp only [firstSubresultantMatrix, Matrix.of_apply]
    dsimp
    rw [if_pos hrow]
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hleft hupper
    · rw [CPolynomial.coeff_toPoly]
    · have hcoeff : g.toPoly.coeff (col.val - row.val) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [← CPolynomial.natDegree_toPoly]
          omega)
      rw [hcoeff]
    · rfl
  · let shift := row.val - (d₁ - 1)
    have hfpoly : f.toPoly ≠ 0 := toPoly_ne_zero_of_natDegree_pos f hfpos
    have hrowlt : row.val < k := row.isLt
    have hshift : shift < d₂ - 1 := by
      dsimp [shift, k, firstSubresultantSize, d₁, d₂] at *
      omega
    have hbound : (Polynomial.X ^ shift * f.toPoly).natDegree < k + 1 := by
      rw [Polynomial.natDegree_X_pow_mul shift hfpoly, ← CPolynomial.natDegree_toPoly]
      dsimp [shift, k, firstSubresultantSize, d₁, d₂] at *
      omega
    have hfshift : (Polynomial.X ^ shift * f.toPoly).eval₂ φ z = 0 := by
      simp [Polynomial.eval₂_mul, hfroot]
    rw [Polynomial.eval₂_eq_sum_range' φ hbound z] at hfshift
    have hsum :
        (∑ col : Fin (k + 1),
          φ ((Polynomial.X ^ shift * f.toPoly).coeff col.val) * z ^ col.val) = 0 := by
      have heq := Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
        φ ((Polynomial.X ^ shift * f.toPoly).coeff i) * z ^ i) (k + 1)
      exact heq.trans hfshift
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro col _
    congr 2
    dsimp [d₁, d₂, shift] at hrow ⊢
    simp only [firstSubresultantMatrix, Matrix.of_apply]
    dsimp
    rw [if_neg hrow]
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hleft hupper
    · rw [CPolynomial.coeff_toPoly]
    · have hcoeff : f.toPoly.coeff (col.val - shift) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [← CPolynomial.natDegree_toPoly]
          omega)
      rw [hcoeff]
    · rfl

/-- Mapped version of the deleted-minor relation. -/
theorem deletedMinors_map_relation_of_mulVec_eq
    {R S : Type*} [CommRing R] [CommRing S] {k : ℕ} (hk : 0 < k)
    (φ : R →+* S) (matrix : Matrix (Fin k) (Fin (k + 1)) R) (z : S)
    (hkernel : Matrix.mulVec (matrix.map φ) (fun j ↦ z ^ j.val) = 0) :
    φ (minorOmitting matrix ⟨1, by omega⟩).det +
      φ (minorOmitting matrix ⟨0, by omega⟩).det * z = 0 := by
  have h := deletedMinors_relation_of_mulVec_eq (R := S) hk (matrix.map φ) z ?_
  · have hmap0 :
        (minorOmitting matrix (⟨0, by omega⟩ : Fin (k + 1))).map φ =
          minorOmitting (matrix.map φ) (⟨0, by omega⟩ : Fin (k + 1)) := by
      ext i j
      rfl
    have hmap1 :
        (minorOmitting matrix (⟨1, by omega⟩ : Fin (k + 1))).map φ =
          minorOmitting (matrix.map φ) (⟨1, by omega⟩ : Fin (k + 1)) := by
      ext i j
      rfl
    rw [φ.map_det, φ.map_det]
    change ((minorOmitting matrix (⟨1, by omega⟩ : Fin (k + 1))).map φ).det +
      ((minorOmitting matrix (⟨0, by omega⟩ : Fin (k + 1))).map φ).det * z = 0
    rw [hmap0, hmap1]
    exact h
  · funext row
    have hrow := congrFun hkernel row
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow ⊢
    rw [Fin.sum_univ_succ] at hrow
    have htail :
        (∑ j : Fin k, matrix.map φ row j.succ * z ^ j.succ.val) =
          ∑ j : Fin k,
            minorOmitting (matrix.map φ) ⟨0, by omega⟩ row j * z ^ (j.val + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [minorOmitting, Fin.zero_succAbove]
    rw [← htail]
    have hzero : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := rfl
    rw [hzero]
    simpa only [Matrix.map_apply, Fin.val_zero, pow_zero, mul_one] using
      eq_neg_of_add_eq_zero_right hrow

/-- The stored first-subresultant coefficients satisfy their root relation after any coefficient
specialization. -/
theorem firstSubresultant_map_relation_of_common_root
    {R S : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
    [CommRing S] [Nontrivial S] (φ : R →+* S) (f g : CPolynomial R) (z : S)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hfroot : f.toPoly.eval₂ φ z = 0) (hgroot : g.toPoly.eval₂ φ z = 0) :
    φ (firstSubresultant f g).2 + φ (firstSubresultant f g).1 * z = 0 := by
  let k := firstSubresultantSize f g
  by_cases hk : k = 0
  · have hfdegree : f.natDegree = 1 := by
      dsimp [k, firstSubresultantSize] at hk
      omega
    have hgdegree : g.natDegree = 1 := by
      dsimp [k, firstSubresultantSize] at hk
      omega
    rw [firstSubresultant_of_natDegree_eq_one f g hfdegree hgdegree]
    have hbound : f.toPoly.natDegree < 2 := by
      rw [← CPolynomial.natDegree_toPoly, hfdegree]
      omega
    rw [Polynomial.eval₂_eq_sum_range' φ hbound z] at hfroot
    norm_num [Finset.sum_range_succ] at hfroot
    rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly]
    exact hfroot
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkernel := firstSubresultantMatrix_map_mulVec_eq_zero
      φ f g z hfpos hgpos hfroot hgroot
    have hrelation := deletedMinors_map_relation_of_mulVec_eq hkpos φ
      (firstSubresultantMatrix f g) z hkernel
    simpa only [firstSubresultant, k, hk, dite_false] using hrelation

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]
variable {K : Type*} [Field K]

noncomputable section

local instance : DecidableEq K := Classical.decEq K

omit [Fintype F] in
/-- Evaluating a coefficient-lifted polynomial is independent of the coefficient parameter. -/
theorem liftInTheta_eval₂
    (ι : F →+* K) (θ t : K) (q : CPolynomial F) :
    (liftInTheta q).toPoly.eval₂ (coefficientEval ι θ) t = q.toPoly.eval₂ ι t := by
  let outerEval : CPolynomial (CPolynomial F) →+* K :=
    (Polynomial.eval₂RingHom (coefficientEval ι θ) t).comp CPolynomial.toPolyRingHom
  calc
    _ = outerEval (liftInTheta q) := by simp [outerEval, RingHom.comp_apply]
    _ = outerEval (q.toPoly.eval₂ (CHom.comp CHom) X) := by
      rw [liftInTheta, CPolynomial.eval₂_toPoly]
    _ = _ := by
      rw [Polynomial.hom_eval₂]
      congr 1
      · ext a
        simp [outerEval, coefficientEval, RingHom.comp_apply, CPolynomial.C_toPoly]
      · simp [outerEval, coefficientEval, RingHom.comp_apply, CPolynomial.X_toPoly]

omit [Fintype F] in
/-- Exact common-root bridge for the unshifted Step-2 polynomial. -/
theorem eval_specializeTheta_liftInTheta
    (ι : F →+* K) (θ t : K) (q : CPolynomial F) :
    (specializeTheta ι θ (liftInTheta q)).eval t = q.toPoly.eval₂ ι t := by
  rw [specializeTheta, Polynomial.eval_map]
  exact liftInTheta_eval₂ ι θ t q

omit [Fintype F] in
/-- Exact common-root bridge for the Step-3 affine transform. -/
theorem eval_specializeTheta_affineTransform
    (ι : F →+* K) (θ t : K) (α : F) (q : CPolynomial F) :
    (specializeTheta ι θ (affineTransform α q)).eval t =
      q.toPoly.eval₂ ι ((ι α + 1) * θ - ι α * t) := by
  rw [specializeTheta, Polynomial.eval_map]
  exact affineTransform_eval₂ ι θ t α q

/-- Proof-facing hypotheses stated directly at the two specialized polynomial families.  Unlike
`GcdLinearAtRoot`, this contract does not mention a normalized gcd or require the computed
linear subresultant to be associated to one. -/
structure CommonRootsAtPoint (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (ι : F →+* K)
    (θ : K) (point : Fin dimension → K) : Prop where
  candidate_nonzero : candidate.eliminant ≠ 0
  modulus_root : (modulus p candidate).toPoly.eval₂ ι θ = 0
  denominator_ne_zero : ∀ i : Fin dimension,
    coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate i).1 ≠ 0
  minus_degree_pos : ∀ i : Fin dimension,
    0 < (liftInTheta (minusPolynomial p dimension candidate i)).natDegree
  plus_degree_pos : ∀ i : Fin dimension,
    0 < (affineTransform α (plusPolynomial p dimension candidate i)).natDegree
  minus_root : ∀ i : Fin dimension,
    (specializeTheta ι θ
      (liftInTheta (minusPolynomial p dimension candidate i))).eval (θ + point i) = 0
  plus_root : ∀ i : Fin dimension,
    (specializeTheta ι θ
      (affineTransform α (plusPolynomial p dimension candidate i))).eval (θ + point i) = 0

/-- The direct determinant argument gives the reduced coordinate relation at every common root. -/
theorem CommonRootsAtPoint.coefficient_relation
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : CommonRootsAtPoint p dimension α candidate ι θ point)
    (i : Fin dimension) :
    coefficientEval ι θ
        (reducedCoordinateSubresultant p dimension α candidate i).2 +
      coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1 *
        (θ + point i) = 0 := by
  let f := liftInTheta (minusPolynomial p dimension candidate i)
  let g := affineTransform α (plusPolynomial p dimension candidate i)
  have hfroot : f.toPoly.eval₂ (coefficientEval ι θ) (θ + point i) = 0 := by
    rw [← Polynomial.eval_map]
    exact hypotheses.minus_root i
  have hgroot : g.toPoly.eval₂ (coefficientEval ι θ) (θ + point i) = 0 := by
    rw [← Polynomial.eval_map]
    exact hypotheses.plus_root i
  have hraw := firstSubresultant_map_relation_of_common_root
    (coefficientEval ι θ) f g (θ + point i)
    (hypotheses.minus_degree_pos i) (hypotheses.plus_degree_pos i)
    hfroot hgroot
  change coefficientEval ι θ
        ((coordinateSubresultant p dimension α candidate i).2.modByMonic
          (modulus p candidate)) +
      coefficientEval ι θ
          ((coordinateSubresultant p dimension α candidate i).1.modByMonic
            (modulus p candidate)) *
        (θ + point i) = 0
  rw [coefficientEval_modByModulus p hypotheses.candidate_nonzero
      hypotheses.modulus_root,
    coefficientEval_modByModulus p hypotheses.candidate_nonzero hypotheses.modulus_root]
  simpa only [f, g, coordinateSubresultant] using hraw

/-- The computed Step-4 coefficient ratio is the negative shifted coordinate, derived directly
from common-root equations and the executable determinant matrix. -/
theorem CommonRootsAtPoint.subresultant_ratio
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : CommonRootsAtPoint p dimension α candidate ι θ point)
    (i : Fin dimension) :
    coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).2 /
        coefficientEval ι θ
          (reducedCoordinateSubresultant p dimension α candidate i).1 =
      -(θ + point i) := by
  have hrelation := CommonRootsAtPoint.coefficient_relation (p := p) hypotheses i
  have hne := hypotheses.denominator_ne_zero i
  field_simp
  linear_combination hrelation

/-- Rojas Steps 4--5 represent every point satisfying the actual specialized common-root
equations and the executable nonzero-denominator check. -/
theorem produce_representsPoint_of_commonRoots
    {dimension : ℕ} {α : F} {candidate : SpecializationCandidate (F := F)}
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (hypotheses : CommonRootsAtPoint p dimension α candidate ι θ point) :
    (produce p dimension α candidate).RepresentsPoint ι θ point := by
  refine ⟨hypotheses.modulus_root, ?_, by simp [produce], ?_⟩
  · rw [show (produce p dimension α candidate).denominator =
      commonDenominator p dimension α candidate from rfl]
    rw [← coefficientEval_apply]
    rw [coefficientEval_commonDenominator (p := p) dimension α candidate ι θ
      hypotheses.candidate_nonzero hypotheses.modulus_root]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hypotheses.denominator_ne_zero i
  · intro i
    simp only [produce, List.getElem?_ofFn]
    have hget :
        (if h : i.val < dimension then
            some (coordinateNumerator p dimension α candidate ⟨i.val, h⟩)
          else none).getD 0 =
        coordinateNumerator p dimension α candidate i := by
      simp [i.isLt]
    rw [hget, ← coefficientEval_apply, ← coefficientEval_apply]
    rw [coefficientEval_coordinateNumerator (p := p) dimension α candidate ι θ i
        hypotheses.candidate_nonzero hypotheses.modulus_root,
      coefficientEval_commonDenominator (p := p) dimension α candidate ι θ
        hypotheses.candidate_nonzero hypotheses.modulus_root]
    let a : Fin dimension → K := fun j ↦ coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate j).1
    let b : Fin dimension → K := fun j ↦ coefficientEval ι θ
      (reducedCoordinateSubresultant p dimension α candidate j).2
    have hrelation : b i + a i * (θ + point i) = 0 :=
      CommonRootsAtPoint.coefficient_relation (p := p) hypotheses i
    have hfactor : (-1) * (θ * a i + b i) = a i * point i := by
      linear_combination -hrelation
    have hprod : a i * ∏ j ∈ Finset.univ.erase i, a j = ∏ j, a j := by
      exact Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)
    have hdenominator : (∏ j, a j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ hypotheses.denominator_ne_zero j
    change ((-1) * (θ * a i + b i) * ∏ j ∈ Finset.univ.erase i, a j) /
        (∏ j, a j) = point i
    rw [hfactor]
    rw [show a i * point i * (∏ j ∈ Finset.univ.erase i, a j) =
      point i * (a i * ∏ j ∈ Finset.univ.erase i, a j) by ring, hprod]
    exact mul_div_cancel_right₀ (point i) hdenominator

end

end ArkLib.Rojas.Producer.SubresultantMap
