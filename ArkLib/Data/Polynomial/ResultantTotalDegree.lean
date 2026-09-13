/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ResultantDegree
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Parameter total-degree bounds for univariate resultants

This file bounds the total degree in an arbitrary family of coefficient parameters of a
univariate Sylvester resultant.  The proof refines the determinant degree argument used by the
dense Macaulay producer: each Sylvester column carries the degree budget of the polynomial from
which that column is drawn.  The resulting weighted bound remains valid for padded resultants
and over commutative rings.
-/

@[expose] public section

namespace Polynomial

variable {R σ : Type*} [CommRing R]

/-- A determinant's total degree is bounded by the sum of column budgets. -/
theorem totalDegree_det_le_sum_columnBudget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ R)) (budget : ι → ℕ)
    (hentry : ∀ i j, (M i j).totalDegree ≤ budget j) :
    M.det.totalDegree ≤ ∑ j, budget j := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro permutation _
  refine (MvPolynomial.totalDegree_smul_le
    (permutation.sign : ℤ) (∏ i, M (permutation i) i)).trans ?_
  refine (MvPolynomial.totalDegree_finsetProd Finset.univ
    (fun i => M (permutation i) i)).trans ?_
  exact Finset.sum_le_sum fun i _ => hentry _ i

/-- A padded resultant has total parameter degree at most the Sylvester column count times each
input's coefficient total-degree budget.  No degree or nonzero assumptions are needed. -/
theorem totalDegree_resultant_le_of_coeff_totalDegree_le
    (P Q : Polynomial (MvPolynomial σ R)) (m n A B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ A)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q m n).totalDegree ≤ n * A + m * B := by
  classical
  let M := sylvester P Q m n
  let budget : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m => B) (fun _ : Fin n => A)
  have hentry (i j : Fin (m + n)) : (M i j).totalDegree ≤ budget j := by
    cases j using Fin.addCases with
    | left column =>
      simp only [budget, Fin.addCases_left]
      have hM : M i (.castAdd n column) =
          if (i : ℕ) ∈ Set.Icc (column : ℕ) ((column : ℕ) + n) then
            Q.coeff ((i : ℕ) - column) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hQ _
      · simp
    | right column =>
      simp only [budget, Fin.addCases_right]
      have hM : M i (.natAdd m column) =
          if (i : ℕ) ∈ Set.Icc (column : ℕ) ((column : ℕ) + m) then
            P.coeff ((i : ℕ) - column) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hP _
      · simp
  change M.det.totalDegree ≤ _
  refine (totalDegree_det_le_sum_columnBudget M budget hentry).trans ?_
  simp [budget, Fin.sum_univ_add, Nat.add_comm]

/-- The actual-degree resultant satisfies the coefficientwise total-degree bound. -/
theorem totalDegree_resultant_le_of_coeff_totalDegree_le_actual
    (P Q : Polynomial (MvPolynomial σ R)) (A B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ A)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q).totalDegree ≤ Q.natDegree * A + P.natDegree * B :=
  totalDegree_resultant_le_of_coeff_totalDegree_le
    P Q P.natDegree Q.natDegree A B hP hQ

/-- A common coefficient budget gives the symmetric actual-degree bound. -/
theorem totalDegree_resultant_le_of_coeff_totalDegree_le_common
    (P Q : Polynomial (MvPolynomial σ R)) (B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ B)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ B) :
    (resultant P Q).totalDegree ≤ (Q.natDegree + P.natDegree) * B := by
  simpa [add_mul] using
    totalDegree_resultant_le_of_coeff_totalDegree_le_actual P Q B B hP hQ

/-- Differentiating in the univariate variable does not increase the total degree of any
parameter coefficient. -/
theorem coeff_derivative_totalDegree_le (P : Polynomial (MvPolynomial σ R)) (j : ℕ) :
    (P.derivative.coeff j).totalDegree ≤ (P.coeff (j + 1)).totalDegree := by
  rw [coeff_derivative,
    show (j : MvPolynomial σ R) + 1 = MvPolynomial.C ((j : R) + 1) by simp,
    mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact MvPolynomial.totalDegree_smul_le _ _

/-- The actual-degree derivative resultant obeys the sharp Sylvester column budget in total
parameter degree, including when the derivative degree drops in positive characteristic. -/
theorem totalDegree_resultant_derivative_le_of_coeff_totalDegree_le
    (P : Polynomial (MvPolynomial σ R)) (B : ℕ)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ B) :
    (resultant P P.derivative).totalDegree ≤ (2 * P.natDegree - 1) * B := by
  have h := totalDegree_resultant_le_of_coeff_totalDegree_le_actual P P.derivative B B hP
    (fun j => (coeff_derivative_totalDegree_le P j).trans (hP (j + 1)))
  calc
    _ ≤ (P.derivative.natDegree + P.natDegree) * B := by
      simpa only [add_mul] using h
    _ ≤ (2 * P.natDegree - 1) * B := by
      apply Nat.mul_le_mul_right
      have hd := natDegree_derivative_le P
      omega

/-- A uniform outer-degree and coefficient budget gives the decoder's convenient
`2 * Bjet * (Bjet - 1)` envelope. -/
theorem totalDegree_resultant_le_two_mul_degreeBudget
    (P Q : Polynomial (MvPolynomial σ R)) (Bjet : ℕ)
    (hPdegree : P.natDegree ≤ Bjet) (hQdegree : Q.natDegree ≤ Bjet - 1)
    (hP : ∀ j, (P.coeff j).totalDegree ≤ Bjet)
    (hQ : ∀ j, (Q.coeff j).totalDegree ≤ Bjet - 1) :
    (resultant P Q).totalDegree ≤ 2 * Bjet * (Bjet - 1) := by
  refine (totalDegree_resultant_le_of_coeff_totalDegree_le_actual
    P Q Bjet (Bjet - 1) hP hQ).trans ?_
  calc
    Q.natDegree * Bjet + P.natDegree * (Bjet - 1) ≤
        (Bjet - 1) * Bjet + Bjet * (Bjet - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hQdegree) (Nat.mul_le_mul_right _ hPdegree)
    _ = 2 * Bjet * (Bjet - 1) := by ring

end Polynomial
