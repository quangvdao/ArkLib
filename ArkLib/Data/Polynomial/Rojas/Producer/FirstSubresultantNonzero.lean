/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantCorrectness
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Nonvanishing of the first principal subresultant coefficient

This module proves directly from the stored increasing-coefficient matrix that its constant-column
minor is nonzero when the mapped inputs have degree-one gcd.  The proof factors the common linear
factor from both rows and identifies the minor with a padded resultant times a unit lower
bidiagonal matrix.
-/

@[expose] public section

open Polynomial Matrix

namespace ArkLib.Rojas.Producer.FirstSubresultantNonzero

variable {K : Type*} [Field K]

def tailMul (c : K) (k : ℕ) : Matrix (Fin k) (Fin k) K :=
  fun i j => if i = j then 1 else if i.val = j.val + 1 then c else 0

def lowerShift (k : ℕ) : Matrix (Fin k) (Fin k) K :=
  fun i j => if i.val = j.val + 1 then 1 else 0

theorem mul_lowerShift_apply {k : ℕ} (M : Matrix (Fin k) (Fin k) K) (i j : Fin k) :
    (M * (lowerShift (K := K) k)) i j =
      if h : j.val + 1 < k then M i ⟨j.val + 1, h⟩ else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨j.val + 1, h⟩]
    · simp [lowerShift]
    · intro b hb
      simp only [lowerShift]
      rw [if_neg]
      · simp
      · intro heq
        apply hb
        exact Fin.ext heq
  · apply Finset.sum_eq_zero
    intro b hb
    simp only [lowerShift]
    rw [if_neg]
    · simp
    · omega

theorem tailMul_eq (c : K) (k : ℕ) :
    tailMul c k = 1 + c • (lowerShift (K := K) k) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tailMul, lowerShift]
  · simp [tailMul, lowerShift, hij]

theorem mul_tailMul_apply {k : ℕ} (M : Matrix (Fin k) (Fin k) K) (c : K) (i j : Fin k) :
    (M * tailMul c k) i j = M i j +
      c * (if h : j.val + 1 < k then M i ⟨j.val + 1, h⟩ else 0) := by
  rw [tailMul_eq, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_lowerShift_apply]

/-- Shift rows of products with the constant coefficient column omitted. -/
def productTailRows (P Q : K[X]) (m n : ℕ) :
    Matrix (Fin (m+n)) (Fin (m+n)) K := fun row col =>
  row.addCases
    (fun r => if r.val ≤ col.val + 1 then Q.coeff (col.val + 1 - r.val) else 0)
    (fun r => if r.val ≤ col.val + 1 then P.coeff (col.val + 1 - r.val) else 0)

theorem coeff_X_add_C_mul (c : K) (H : K[X]) (a : ℕ) :
    ((X + C c) * H).coeff (a + 1) = H.coeff a + c * H.coeff (a + 1) := by
  simpa using (Polynomial.coeff_X_sub_C_mul (p := H) (r := -c) (a := a))

theorem productTailRows_eq_sylvester_mul_tail
    (A B : K[X]) (c : K) (m n : ℕ)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    productTailRows ((X + C c) * A) ((X + C c) * B) m n =
      (sylvester A B m n).transpose * tailMul c (m+n) := by
  ext row col
  cases row using Fin.addCases with
  | left r =>
      rw [mul_tailMul_apply]
      simp only [productTailRows, Fin.addCases_left, transpose_apply]
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc]
      by_cases hrc : r.val ≤ col.val
      · have hpos : r.val ≤ col.val + 1 := by omega
        rw [if_pos hpos]
        have hidx : col.val + 1 - r.val = (col.val - r.val) + 1 := by omega
        rw [hidx, coeff_X_add_C_mul]
        by_cases hup : col.val ≤ r.val + n
        · rw [if_pos ⟨hrc, hup⟩]
          by_cases hend : col.val + 1 < m + n
          · rw [dif_pos hend]
            by_cases hup' : col.val + 1 ≤ r.val + n
            · rw [if_pos ⟨by omega, hup'⟩]
            · rw [if_neg (by omega)]
              have hz : B.coeff ((col.val - r.val) + 1) = 0 := by
                apply Polynomial.coeff_eq_zero_of_natDegree_lt
                omega
              rw [hz, mul_zero, add_zero]
          · rw [dif_neg hend, mul_zero, add_zero]
            have hz : B.coeff ((col.val - r.val) + 1) = 0 := by
              apply Polynomial.coeff_eq_zero_of_natDegree_lt
              omega
            rw [hz]
            simp
        · rw [if_neg (by omega)]
          have hz0 : B.coeff (col.val - r.val) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
          rw [hz0, zero_add]
          have hz1 : B.coeff ((col.val - r.val) + 1) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
          rw [hz1, mul_zero]
          by_cases hend : col.val + 1 < m + n
          · rw [dif_pos hend]
            rw [if_neg (by omega), mul_zero]
            simp
          · rw [dif_neg hend, mul_zero]
            simp
      · by_cases heq : r.val = col.val + 1
        · rw [if_pos (by omega)]
          have hzero : col.val + 1 - r.val = 0 := by omega
          rw [hzero]
          have hnot : ¬(r.val ≤ col.val ∧ col.val ≤ r.val + n) := by omega
          rw [if_neg hnot]
          have hend : col.val + 1 < m + n := by omega
          rw [dif_pos hend]
          rw [if_pos (by omega)]
          simp
        · rw [if_neg (by omega)]
          rw [if_neg (by omega)]
          by_cases hend : col.val + 1 < m+n
          · rw [dif_pos hend]
            rw [if_neg (by omega), mul_zero]
            simp
          · rw [dif_neg hend, mul_zero]
            simp
  | right r =>
      rw [mul_tailMul_apply]
      simp only [productTailRows, Fin.addCases_right, transpose_apply]
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc]
      by_cases hrc : r.val ≤ col.val
      · have hpos : r.val ≤ col.val + 1 := by omega
        rw [if_pos hpos]
        have hidx : col.val + 1 - r.val = (col.val - r.val) + 1 := by omega
        rw [hidx, coeff_X_add_C_mul]
        by_cases hup : col.val ≤ r.val + m
        · rw [if_pos ⟨hrc, hup⟩]
          by_cases hend : col.val + 1 < m + n
          · rw [dif_pos hend]
            by_cases hup' : col.val + 1 ≤ r.val + m
            · rw [if_pos ⟨by omega, hup'⟩]
            · rw [if_neg (by omega)]
              have hz : A.coeff ((col.val - r.val) + 1) = 0 := by
                apply Polynomial.coeff_eq_zero_of_natDegree_lt
                omega
              rw [hz, mul_zero, add_zero]
          · rw [dif_neg hend, mul_zero, add_zero]
            have hz : A.coeff ((col.val - r.val) + 1) = 0 := by
              apply Polynomial.coeff_eq_zero_of_natDegree_lt
              omega
            rw [hz]
            simp
        · rw [if_neg (by omega)]
          have hz0 : A.coeff (col.val - r.val) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
          rw [hz0, zero_add]
          have hz1 : A.coeff ((col.val - r.val) + 1) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
          rw [hz1, mul_zero]
          by_cases hend : col.val + 1 < m + n
          · rw [dif_pos hend]
            rw [if_neg (by omega), mul_zero]
            simp
          · rw [dif_neg hend, mul_zero]
            simp
      · by_cases heq : r.val = col.val + 1
        · rw [if_pos (by omega)]
          have hzero : col.val + 1 - r.val = 0 := by omega
          rw [hzero]
          have hnot : ¬(r.val ≤ col.val ∧ col.val ≤ r.val + m) := by omega
          rw [if_neg hnot]
          have hend : col.val + 1 < m + n := by omega
          rw [dif_pos hend]
          rw [if_pos (by omega)]
          simp
        · rw [if_neg (by omega)]
          rw [if_neg (by omega)]
          by_cases hend : col.val + 1 < m+n
          · rw [dif_pos hend]
            rw [if_neg (by omega), mul_zero]
            simp
          · rw [dif_neg hend, mul_zero]
            simp

end ArkLib.Rojas.Producer.FirstSubresultantNonzero

namespace ArkLib.Rojas.Producer.FirstSubresultantNonzero

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.SubresultantMap

variable {R K : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
  [Field K]

omit [Nontrivial R] in
theorem mapped_constantMinor_reindex_eq_productTailRows
    (φ : R →+* K) (f g : CPolynomial R)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree) :
    let m := f.natDegree - 1
    let n := g.natDegree - 1
    let hsize : firstSubresultantSize f g = m + n := by
      simp only [firstSubresultantSize]
      omega
    let e := finCongr hsize
    Matrix.reindex e e
      ((minorOmitting (firstSubresultantMatrix f g) ⟨0, Nat.zero_lt_succ _⟩).map φ) =
      productTailRows (f.toPoly.map φ) (g.toPoly.map φ) m n := by
  dsimp only
  let hsize : firstSubresultantSize f g = (f.natDegree - 1) + (g.natDegree - 1) := by
    simp only [firstSubresultantSize]
    omega
  let e := finCongr hsize
  change Matrix.reindex e e
      ((minorOmitting (firstSubresultantMatrix f g) ⟨0, Nat.zero_lt_succ _⟩).map φ) = _
  have hminor (i : Fin (firstSubresultantSize f g))
      (j : Fin (firstSubresultantSize f g)) :
      ((minorOmitting (firstSubresultantMatrix f g) ⟨0, Nat.zero_lt_succ _⟩).map φ) i j =
        φ (firstSubresultantMatrix f g i j.succ) := by
    simp [minorOmitting, Fin.zero_succAbove]
  ext row col
  cases row using Fin.addCases with
  | left r =>
      change ((minorOmitting (firstSubresultantMatrix f g)
        ⟨0, Nat.zero_lt_succ _⟩).map φ) (e.symm (Fin.castAdd _ r)) (e.symm col) = _
      rw [hminor]
      simp only [firstSubresultantMatrix, Matrix.of_apply]
      rw [dif_pos (by
        change r.val < f.natDegree - 1
        exact r.isLt)]
      simp only [productTailRows, Fin.addCases_left]
      by_cases hleft : r.val ≤ col.val + 1
      · rw [dif_pos (by simpa [e] using hleft), if_pos hleft]
        by_cases hright : col.val + 1 ≤ r.val + g.natDegree
        · rw [if_pos (by simpa [e] using hright)]
          rw [CPolynomial.coeff_toPoly, Polynomial.coeff_map]
          simp [e]
        · rw [if_neg (by
            intro hh
            apply hright
            simpa [e] using hh)]
          have hz : (g.toPoly.map φ).coeff (col.val + 1 - r.val) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            calc
              (g.toPoly.map φ).natDegree ≤ g.toPoly.natDegree :=
                Polynomial.natDegree_map_le
              _ = g.natDegree := (CPolynomial.natDegree_toPoly g).symm
              _ < col.val + 1 - r.val := by omega
          simpa using hz.symm
      · rw [dif_neg (by
          intro hh
          apply hleft
          simpa [e] using hh), if_neg hleft]
        simp
  | right r =>
      change ((minorOmitting (firstSubresultantMatrix f g)
        ⟨0, Nat.zero_lt_succ _⟩).map φ) (e.symm (Fin.natAdd _ r)) (e.symm col) = _
      rw [hminor]
      simp only [firstSubresultantMatrix, Matrix.of_apply]
      rw [dif_neg (by
        change ¬(f.natDegree - 1 + r.val < f.natDegree - 1)
        omega)]
      simp only [productTailRows, Fin.addCases_right]
      have hshift : (e.symm (Fin.natAdd (f.natDegree - 1) r)).val -
          (f.natDegree - 1) = r.val := by simp [e]
      rw [show (e.symm (Fin.natAdd (f.natDegree - 1) r)).val -
          (f.natDegree - 1) = r.val from hshift]
      by_cases hleft : r.val ≤ col.val + 1
      · rw [dif_pos (by simpa [e] using hleft), if_pos hleft]
        by_cases hright : col.val + 1 ≤ r.val + f.natDegree
        · rw [if_pos (by simpa [e] using hright)]
          rw [CPolynomial.coeff_toPoly, Polynomial.coeff_map]
          simp [e]
        · rw [if_neg (by
            intro hh
            apply hright
            simpa [e] using hh)]
          have hz : (f.toPoly.map φ).coeff (col.val + 1 - r.val) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            calc
              (f.toPoly.map φ).natDegree ≤ f.toPoly.natDegree :=
                Polynomial.natDegree_map_le
              _ = f.natDegree := (CPolynomial.natDegree_toPoly f).symm
              _ < col.val + 1 - r.val := by omega
          simpa using hz.symm
      · rw [dif_neg (by simpa [e] using hleft), if_neg hleft]
        simp

end ArkLib.Rojas.Producer.FirstSubresultantNonzero

namespace ArkLib.Rojas.Producer.FirstSubresultantNonzero

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.SubresultantMap

variable {R K : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R] [Field K]

theorem tailMul_isLowerTriangular (c : K) (k : ℕ) :
    (tailMul c k).IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  simp only [tailMul]
  split_ifs with h₁ h₂
  · omega
  · omega
  · rfl

theorem tailMul_det (c : K) (k : ℕ) : (tailMul c k).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (tailMul_isLowerTriangular c k)]
  simp [tailMul]

omit [Nontrivial R] in
theorem map_firstSubresultant_fst_eq_resultant_of_factorization
    (φ : R →+* K) (f g : CPolynomial R)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hk : firstSubresultantSize f g ≠ 0)
    (A B : K[X]) (c : K)
    (hf : f.toPoly.map φ = (Polynomial.X + Polynomial.C c) * A)
    (hg : g.toPoly.map φ = (Polynomial.X + Polynomial.C c) * B)
    (hA : A.natDegree ≤ f.natDegree - 1)
    (hB : B.natDegree ≤ g.natDegree - 1) :
    φ (firstSubresultant f g).1 =
      resultant A B (f.natDegree - 1) (g.natDegree - 1) := by
  let m := f.natDegree - 1
  let n := g.natDegree - 1
  let hsize : firstSubresultantSize f g = m + n := by
    dsimp only [m, n, firstSubresultantSize]
    omega
  let e := finCongr hsize
  have hadapter := mapped_constantMinor_reindex_eq_productTailRows φ f g hfpos hgpos
  dsimp only at hadapter
  have hmatrix :
      Matrix.reindex e e
        ((minorOmitting (firstSubresultantMatrix f g) ⟨0, Nat.zero_lt_succ _⟩).map φ) =
      (sylvester A B m n).transpose * tailMul c (m+n) := by
    rw [hadapter]
    rw [hf, hg]
    exact productTailRows_eq_sylvester_mul_tail A B c m n
      (by simpa only [m] using hA) (by simpa only [n] using hB)
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_transpose, tailMul_det, mul_one] at hdet
  rw [firstSubresultant, dif_neg hk]
  simp only
  rw [RingHom.map_det]
  change ((minorOmitting (firstSubresultantMatrix f g) ⟨0, Nat.zero_lt_succ _⟩).map φ).det = _
  simpa only [m, n, Polynomial.resultant] using hdet

end ArkLib.Rojas.Producer.FirstSubresultantNonzero

namespace ArkLib.Rojas.Producer.FirstSubresultantNonzero

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.SubresultantMap

variable {R K : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
  [Field K] [DecidableEq K]

omit [Nontrivial R] in
theorem mapped_firstSubresultant_fst_ne_zero_of_gcd_natDegree_eq_one
    (φ : R →+* K) (f g : CPolynomial R)
    (hfdeg : (f.toPoly.map φ).natDegree = f.natDegree)
    (hgdeg : (g.toPoly.map φ).natDegree = g.natDegree)
    (hfpos : 0 < f.natDegree) (hgpos : 0 < g.natDegree)
    (hgcd : (gcd (f.toPoly.map φ) (g.toPoly.map φ)).natDegree = 1) :
    φ (firstSubresultant f g).1 ≠ 0 := by
  classical
  let P := f.toPoly.map φ
  let Q := g.toPoly.map φ
  let D := gcd P Q
  let A := P / D
  let B := Q / D
  have hPne : P ≠ 0 := by
    intro h
    have : P.natDegree = 0 := by simp [h]
    dsimp only [P] at this
    omega
  have hQne : Q ≠ 0 := by
    intro h
    have : Q.natDegree = 0 := by simp [h]
    dsimp only [Q] at this
    omega
  have hDne : D ≠ 0 := by
    dsimp only [D]
    exact gcd_ne_zero_of_left hPne
  have hDmonic : D.Monic := by
    apply (Polynomial.normalize_eq_self_iff_monic hDne).mp
    dsimp only [D]
    exact normalize_gcd P Q
  have hDdegree : D.natDegree = 1 := by
    simpa [D, P, Q] using hgcd
  let c := D.coeff 0
  have hDform : D = Polynomial.X + Polynomial.C c :=
    hDmonic.eq_X_add_C hDdegree
  have hDP : D * A = P := by
    dsimp only [A, D]
    exact EuclideanDomain.mul_div_cancel' hDne (gcd_dvd_left P Q)
  have hDQ : D * B = Q := by
    dsimp only [B, D]
    exact EuclideanDomain.mul_div_cancel' hDne (gcd_dvd_right P Q)
  have hAne : A ≠ 0 := by
    intro h
    have hDP' := hDP
    rw [h] at hDP'
    have hPzero : P = 0 := by
      calc
        P = D * (0 : K[X]) := hDP'.symm
        _ = 0 := by ring
    exact hPne hPzero
  have hBne : B ≠ 0 := by
    intro h
    have hDQ' := hDQ
    rw [h] at hDQ'
    have hQzero : Q = 0 := by
      calc
        Q = D * (0 : K[X]) := hDQ'.symm
        _ = 0 := by ring
    exact hQne hQzero
  have hAdeg : A.natDegree = f.natDegree - 1 := by
    have hmul := hDmonic.natDegree_mul' hAne
    rw [hDP, hDdegree] at hmul
    dsimp only [P] at hmul
    omega
  have hBdeg : B.natDegree = g.natDegree - 1 := by
    have hmul := hDmonic.natDegree_mul' hBne
    rw [hDQ, hDdegree] at hmul
    dsimp only [Q] at hmul
    omega
  have hcop : IsCoprime A B := by
    dsimp only [A, B, D]
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hDne
  by_cases hk : firstSubresultantSize f g = 0
  · have hf1 : f.natDegree = 1 := by
      dsimp only [firstSubresultantSize] at hk
      omega
    rw [firstSubresultant_of_natDegree_eq_one f g hf1 (by
      dsimp only [firstSubresultantSize] at hk
      omega)]
    simp only
    have hlead : P.coeff 1 ≠ 0 := by
      have hPdeg : P.natDegree = 1 := by
        dsimp only [P]
        omega
      rw [← hPdeg]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    dsimp only [P] at hlead
    rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly] at hlead
    exact hlead
  · have heq := map_firstSubresultant_fst_eq_resultant_of_factorization
      φ f g hfpos hgpos hk A B c
      (by
        change P = (Polynomial.X + Polynomial.C c) * A
        rw [← hDform]
        exact hDP.symm)
      (by
        change Q = (Polynomial.X + Polynomial.C c) * B
        rw [← hDform]
        exact hDQ.symm)
      hAdeg.le hBdeg.le
    rw [heq]
    have hres := Polynomial.resultant_ne_zero A B hcop
    rw [hAdeg, hBdeg] at hres
    exact hres

end ArkLib.Rojas.Producer.FirstSubresultantNonzero

namespace ArkLib.Rojas.Producer.FirstSubresultantNonzero

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.SubresultantMap

variable {R K : Type*} [CommRing R] [Nontrivial R] [BEq R] [LawfulBEq R]
  [Field K] [DecidableEq K]

omit [Nontrivial R] in
/-- Exact asymmetric form: only the first mapped/stored degree is required positive. -/
theorem mapped_firstSubresultant_fst_ne_zero_of_gcd_natDegree_eq_one'
    (φ : R →+* K) (f g : CPolynomial R)
    (hfdeg : (f.toPoly.map φ).natDegree = f.natDegree)
    (hgdeg : (g.toPoly.map φ).natDegree = g.natDegree)
    (hfpos : 0 < f.natDegree)
    (hgcd : (gcd (f.toPoly.map φ) (g.toPoly.map φ)).natDegree = 1) :
    φ (firstSubresultant f g).1 ≠ 0 := by
  classical
  let P := f.toPoly.map φ
  let Q := g.toPoly.map φ
  let D := gcd P Q
  have hPne : P ≠ 0 := by
    intro h
    have : P.natDegree = 0 := by simp [h]
    dsimp only [P] at this
    omega
  have hDne : D ≠ 0 := by
    dsimp only [D]
    exact gcd_ne_zero_of_left hPne
  have hDdegree : D.natDegree = 1 := by
    simpa [D, P, Q] using hgcd
  by_cases hQ : Q = 0
  · have hPD : P ∣ D := by
      dsimp only [D]
      simp [Q, hQ, (associated_normalize P).dvd]
    have hPle : P.natDegree ≤ D.natDegree :=
      Polynomial.natDegree_le_of_dvd hPD hDne
    have hf1 : f.natDegree = 1 := by
      dsimp only [P] at hPle
      omega
    have hg0 : g.natDegree = 0 := by
      have : Q.natDegree = 0 := by simp [hQ]
      dsimp only [Q] at this
      omega
    have hk : firstSubresultantSize f g = 0 := by
      simp [firstSubresultantSize, hf1, hg0]
    rw [firstSubresultant, dif_pos hk]
    simp only
    have hlead : P.coeff 1 ≠ 0 := by
      have hPdeg : P.natDegree = 1 := by
        dsimp only [P]
        omega
      rw [← hPdeg]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    dsimp only [P] at hlead
    rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly] at hlead
    exact hlead
  · have hDdvdQ : D ∣ Q := by
      dsimp only [D]
      exact gcd_dvd_right P Q
    have hDleQ : D.natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_le_of_dvd hDdvdQ hQ
    have hgpos : 0 < g.natDegree := by
      dsimp only [Q] at hDleQ
      omega
    exact mapped_firstSubresultant_fst_ne_zero_of_gcd_natDegree_eq_one
      φ f g hfdeg hgdeg hfpos hgpos hgcd

end ArkLib.Rojas.Producer.FirstSubresultantNonzero
