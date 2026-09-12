/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.ToCompPoly.Univariate.Basic
public import Mathlib.Algebra.Polynomial.CoeffMem

/-!
# Degree bounds for executable multiplication determinants

The multiplication determinant is built from actual monic remainders.  This file controls the
coefficient-variable degree of every matrix entry through `coeff_modByMonic_mem_pow_natDegree_mul`
and then applies the Leibniz determinant formula.  The resulting bound does not assume that the
quotient is reduced or that any fiber is unramified.
-/

@[expose] public section

open Polynomial

namespace CompPoly.CPolynomial.NormProducts

variable {F : Type*} [Field F]

private theorem degreeLE_mul_le (A B : ℕ) :
    Polynomial.degreeLE F (A : WithBot ℕ) * Polynomial.degreeLE F (B : WithBot ℕ) ≤
      Polynomial.degreeLE F (A + B : ℕ) := by
  rw [Submodule.mul_le]
  intro a ha b hb
  rw [Polynomial.mem_degreeLE] at ha hb ⊢
  exact (Polynomial.degree_mul_le a b).trans (by simpa using add_le_add ha hb)

private theorem degreeLE_pow_mul_le (A B k : ℕ) :
    Polynomial.degreeLE F (A : WithBot ℕ) ^ k * Polynomial.degreeLE F (B : WithBot ℕ) ≤
      Polynomial.degreeLE F (k * A + B : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc, Submodule.mul_le]
      intro a ha z hz
      have haz : a * z ∈ Polynomial.degreeLE F (A + (k * A + B) : ℕ) :=
        degreeLE_mul_le (F := F) A (k * A + B) (Submodule.mul_mem_mul ha (ih hz))
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haz

private theorem remainder_coeff_natDegree_le
    (H G : Polynomial (Polynomial F)) (j i : ℕ) :
    (((G * Polynomial.X ^ j) %ₘ H).coeff i).natDegree ≤
      (G.natDegree + j) * Polynomial.Bivariate.degreeX H +
        Polynomial.Bivariate.degreeX G := by
  let A := Polynomial.Bivariate.degreeX G
  let B := Polynomial.Bivariate.degreeX H
  let Q := G * Polynomial.X ^ j
  have hQcoeff : ∀ k, (Q.coeff k).natDegree ≤ A := by
    intro k
    rw [show Q = G * Polynomial.X ^ j by rfl, Polynomial.coeff_mul_X_pow']
    split
    · exact Polynomial.Bivariate.coeff_natDegree_le_degreeX _ _
    · simp
  have hQone : (1 : Polynomial F) ∈ Polynomial.degreeLE F (A : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLE]
    simp
  have hHcoeff : ∀ k, (H.coeff k).natDegree ≤ B :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX _
  have hHone : (1 : Polynomial F) ∈ Polynomial.degreeLE F (B : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLE]
    simp
  have hmem := Polynomial.coeff_modByMonic_mem_pow_natDegree_mul Q H
    (Polynomial.degreeLE F (A : WithBot ℕ))
    (fun k => Polynomial.mem_degreeLE.mpr
      ((Polynomial.natDegree_le_iff_degree_le).mp (hQcoeff k))) hQone
    (Polynomial.degreeLE F (B : WithBot ℕ))
    (fun k => Polynomial.mem_degreeLE.mpr
      ((Polynomial.natDegree_le_iff_degree_le).mp (hHcoeff k))) hHone i
  have hdegree : ((Q %ₘ H).coeff i).natDegree ≤ Q.natDegree * B + A := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact Polynomial.mem_degreeLE.mp (degreeLE_pow_mul_le (F := F) B A Q.natDegree hmem)
  refine hdegree.trans ?_
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  dsimp [Q]
  simpa using (Polynomial.natDegree_mul_le (p := G) (q := Polynomial.X ^ j))

variable [BEq F] [LawfulBEq F]

/-- Degree in the stored projection parameter after converting both computable polynomial layers
to ordinary polynomials. -/
noncomputable def parameterDegree (q : CPolynomial (CPolynomial F)) : ℕ :=
  Polynomial.Bivariate.degreeX (q.toPoly.map CPolynomial.toPolyRingHom)

/-- A closed degree budget for the executable determinant norm. -/
noncomputable def determinantDegreeBudget (h g : CPolynomial (CPolynomial F)) : ℕ :=
  h.natDegree *
    ((g.natDegree + h.natDegree) * parameterDegree h + parameterDegree g)

set_option maxHeartbeats 800000 in
-- Elaborating the mapped remainder matrix requires unfolding the two computable polynomial layers.
private theorem multiplicationMatrix_entry_natDegree_le
    (h g : CPolynomial (CPolynomial F)) (hh : h.monic)
    (i j : Fin h.natDegree) :
    (multiplicationMatrix h.natDegree h g i j).natDegree ≤
      (g.natDegree + h.natDegree) *
          Polynomial.Bivariate.degreeX
            (h.toPoly.map CPolynomial.toPolyRingHom) +
        Polynomial.Bivariate.degreeX
          (g.toPoly.map CPolynomial.toPolyRingHom) := by
  let σ : CPolynomial F →+* Polynomial F := CPolynomial.toPolyRingHom
  rw [CPolynomial.natDegree_toPoly]
  rw [← CPolynomial.toPolyRingHom_apply]
  change (σ (multiplicationMatrix h.natDegree h g i j)).natDegree ≤ _
  have hm := congrFun (congrFun
    (map_multiplicationMatrix σ h.natDegree h g hh) i) j
  change σ (multiplicationMatrix h.natDegree h g i j) =
    (((g.toPoly.map σ) * Polynomial.X ^ j.val) %ₘ (h.toPoly.map σ)).coeff i.val at hm
  rw [hm]
  exact (remainder_coeff_natDegree_le
    (h.toPoly.map σ) (g.toPoly.map σ) j.val i.val).trans (by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_right
      have hσ : Function.Injective σ := by
        intro a b hab
        apply CPolynomial.toPoly_injective
        simpa [σ] using hab
      have hmap : (g.toPoly.map σ).natDegree = g.toPoly.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hσ g.toPoly
      rw [hmap, ← CPolynomial.natDegree_toPoly]
      exact Nat.add_le_add_left j.isLt.le _)

set_option maxHeartbeats 800000 in
-- The determinant proof elaborates a dependent Leibniz sum whose entries are mapped polynomials.
/-- The actual multiplication determinant has an explicit coefficient-variable degree bound.
The two occurrences of `h.natDegree` account for the matrix width and for the maximum number of
monic-remainder reductions in a column. -/
theorem natDegree_polynomialNorm_le (h g : CPolynomial (CPolynomial F)) (hh : h.monic) :
    (polynomialNorm h g).natDegree ≤ determinantDegreeBudget h g := by
  unfold determinantDegreeBudget parameterDegree
  unfold polynomialNorm norm
  rw [CPolynomial.natDegree_toPoly]
  rw [← CPolynomial.toPolyRingHom_apply]
  let σ : CPolynomial F →+* Polynomial F := CPolynomial.toPolyRingHom
  change (σ (Matrix.det (multiplicationMatrix h.natDegree h g))).natDegree ≤ _
  rw [RingHom.map_det, Matrix.det_apply]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, σ,
    CPolynomial.toPolyRingHom_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro τ hτ
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ
    (fun i => ((multiplicationMatrix h.natDegree h g) (τ i) i).toPoly)).trans ?_
  calc
    _ ≤ ∑ _i : Fin h.natDegree,
        ((g.natDegree + h.natDegree) *
            Polynomial.Bivariate.degreeX
              (h.toPoly.map CPolynomial.toPolyRingHom) +
          Polynomial.Bivariate.degreeX
            (g.toPoly.map CPolynomial.toPolyRingHom)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [← CPolynomial.natDegree_toPoly] using
        multiplicationMatrix_entry_natDegree_le h g hh (τ i) i
    _ = _ := by simp

end CompPoly.CPolynomial.NormProducts
