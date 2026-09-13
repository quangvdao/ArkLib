/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayDivisionCorrectness
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotientCorrectness
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Algebraic identities for the dense Macaulay quotient

Canny's proof of Macaulay's formula specializes every paired leading
coefficient along one common indeterminate.  On the extraneous principal
minor this produces a characteristic matrix.  This file formalizes that
specialization directly for the executable matrix.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open scoped Matrix Ring
open CPoly CPoly.CMvPolynomial
open DenseMacaulay

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Canny's one-parameter specialization: `u₀ = -T`, the other auxiliary
coefficients vanish, and the deformation parameter is `T`. -/
noncomputable def cannyParameterPath {n : ℕ} : Fin (n + 1) → Polynomial F :=
  Fin.cons (-Polynomial.X) (fun _ => 0)

/-- Evaluation of the stored parameter polynomials along Canny's path. -/
noncomputable def cannyParameterEval {n : ℕ} : Parameters n F →+* Polynomial F :=
  CMvPolynomial.eval₂Hom Polynomial.C
    (Fin.snoc cannyParameterPath Polynomial.X)

@[simp]
theorem cannyParameterEval_auxiliaryCoefficient {n : ℕ} (i : Fin (n + 1)) :
    cannyParameterEval (F := F) (auxiliaryCoefficient i) =
      if i = 0 then -Polynomial.X else 0 := by
  unfold cannyParameterEval cannyParameterPath auxiliaryCoefficient
  rw [CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp_rw [show ∀ a, (auxiliaryParameterMonomial i).toFinsupp a =
      (auxiliaryParameterMonomial i).get a from fun _ => rfl]
  simp only [auxiliaryParameterMonomial, Vector.get_ofFn, pow_ite, pow_one,
    pow_zero, _root_.map_one]
  have hindex : ∀ a : Fin (n + 2),
      (a.val = i.val) = (a = Fin.castSucc i) := by
    intro a
    apply propext
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      subst a
      rfl
  simp_rw [hindex]
  by_cases hi : i = 0
  · subst i
    rw [Finset.prod_ite_eq']
    simp
  · rw [Finset.prod_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, Fin.snoc_castSucc]
    cases i using Fin.cases <;> simp_all

@[simp]
theorem cannyParameterEval_negativeS {n : ℕ} :
    cannyParameterEval (F := F) (negativeS (n := n)) = -Polynomial.X := by
  unfold cannyParameterEval cannyParameterPath negativeS
  rw [CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_pow, _root_.map_neg, _root_.map_one]
  simp_rw [show ∀ a, (sParameterMonomial (n := n)).toFinsupp a =
      (sParameterMonomial (n := n)).get a from fun _ => rfl]
  simp only [sParameterMonomial, Vector.get_ofFn, pow_ite, pow_one, pow_zero]
  have hindex : ∀ a : Fin (n + 2),
      (a.val = n + 1) = (a = Fin.last (n + 1)) := by
    intro a
    apply propext
    constructor
    · intro h
      apply Fin.ext
      exact h
    · intro h
      subst a
      rfl
  simp_rw [hindex]
  simp

@[simp]
theorem cannyParameterEval_C {n : ℕ} (coefficient : F) :
    cannyParameterEval (n := n) (CMvPolynomial.C coefficient) =
      Polynomial.C coefficient := by
  unfold cannyParameterEval
  rw [CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_C]
  simp

private theorem map_rowEntry {n : ℕ} (φ : Parameters n F →+* Polynomial F)
    (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F) :
    φ (rowEntry multiplier column terms) =
      (terms.map fun term =>
        if multiplier + term.1 = column then φ term.2 else 0).sum := by
  unfold rowEntry
  have hfold : ∀ (remaining : HomogeneousTerms n F)
      (accumulator : Parameters n F),
      φ (remaining.foldl
        (fun result term =>
          if multiplier + term.1 = column then result + term.2 else result)
        accumulator) =
        φ accumulator +
          (remaining.map fun term =>
            if multiplier + term.1 = column then φ term.2 else 0).sum := by
    intro remaining
    induction remaining with
    | nil => intro accumulator; simp
    | cons term remaining ih =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        split
        · rw [_root_.map_add]
          ac_rfl
        · simp
  rw [hfold]
  simp

private theorem cannyParameterEval_rowEntry_auxiliary {n : ℕ}
    (multiplier column : CMvMonomial (n + 1)) :
    cannyParameterEval (F := F)
        (rowEntry multiplier column (auxiliaryTerms (F := F))) =
      if multiplier + powerMonomial 0 1 = column then -Polynomial.X else 0 := by
  rw [map_rowEntry]
  unfold auxiliaryTerms
  simp only [List.map_ofFn, List.sum_ofFn]
  classical
  by_cases htarget : multiplier + powerMonomial 0 1 = column
  · rw [if_pos htarget]
    rw [Finset.sum_eq_single 0]
    · simp [htarget]
    · intro i _ hi
      simp [cannyParameterEval_auxiliaryCoefficient, hi]
    · simp
  · rw [if_neg htarget]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [htarget]
    · simp [cannyParameterEval_auxiliaryCoefficient, hi]

/-- Constant part of a row coming from an input polynomial, before the
distinguished `-T` leading coefficient is appended. -/
def inputRowConstant {n : ℕ} (multiplier column : CMvMonomial (n + 1))
    (degree : ℕ) (polynomial : CMvPolynomial n F) : F :=
  (polynomial.val.toList.map fun term =>
    if multiplier + homogenizedMonomial degree term.1 = column then term.2 else 0).sum

private theorem cannyParameterEval_rowEntry_perturbed {n : ℕ}
    (multiplier column : CMvMonomial (n + 1)) (i : Fin (n + 1))
    (degree : ℕ) (polynomial : CMvPolynomial n F) :
    cannyParameterEval (F := F)
        (rowEntry multiplier column (perturbedTerms i degree polynomial)) =
      Polynomial.C (inputRowConstant multiplier column degree polynomial) +
        if multiplier + powerMonomial i degree = column then -Polynomial.X else 0 := by
  rw [map_rowEntry]
  unfold perturbedTerms inputRowConstant
  rw [List.map_append, List.sum_append]
  simp only [List.map_map, List.map_singleton,
    List.sum_singleton, cannyParameterEval_negativeS]
  apply congrArg₂ (· + ·)
  · rw [map_list_sum Polynomial.C]
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro term _
    simp only [Function.comp_apply]
    split <;> simp_all
  · rfl

omit [BEq F] [LawfulBEq F] in
private theorem rowMultiplier_add_pairedPower {count degree : ℕ}
    (equation : Fin count) (row : CMvMonomial count)
    (hdegree : degree ≤ row.get equation) :
    rowMultiplier degree equation row + powerMonomial equation degree = row := by
  apply CMvMonomial.ext
  intro j hj
  unfold rowMultiplier powerMonomial
  change (Vector.zipWith Nat.add
    (Vector.ofFn fun j => row.get j - if j = equation then degree else 0)
    (Vector.ofFn fun j => if j = equation then degree else 0))[j] = row[j]
  rw [Vector.getElem_zipWith hj]
  simp only [Vector.getElem_ofFn]
  change ((row.get ⟨j, hj⟩ -
      if (⟨j, hj⟩ : Fin count) = equation then degree else 0) +
      if (⟨j, hj⟩ : Fin count) = equation then degree else 0) = row.get ⟨j, hj⟩
  by_cases hje : (⟨j, hj⟩ : Fin count) = equation
  · subst equation
    simp [hdegree]
  · simp [hje]

omit [BEq F] [LawfulBEq F] in
private theorem pairedTarget_eq_row {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length) :
    rowMultiplier
        (equationDegree system (basisRowEquation system i))
        (basisRowEquation system i) (basis system)[i] +
      powerMonomial (basisRowEquation system i)
      (equationDegree system (basisRowEquation system i)) =
      (basis system)[i] := by
  apply rowMultiplier_add_pairedPower
  apply rowEquation?_eq_some_degree_le
  exact rowEquation?_basis_eq_some system i

omit [BEq F] [LawfulBEq F] in
private theorem pairedTarget_eq_column_iff {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (i j : Fin (basis system).length) :
    rowMultiplier
        (equationDegree system (basisRowEquation system i))
        (basisRowEquation system i) (basis system)[i] +
      powerMonomial (basisRowEquation system i)
        (equationDegree system (basisRowEquation system i)) =
      (basis system)[j] ↔ i = j := by
  rw [pairedTarget_eq_row]
  change (basis system).get i = (basis system).get j ↔ _
  exact (basis_nodup system).get_inj_iff

/-- Constant matrix left after Canny's one-parameter leading-coefficient
specialization. -/
def cannyConstantMatrix {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Matrix (Fin (basis system).length) (Fin (basis system).length) F :=
  fun i j =>
    Fin.cases 0
      (fun equation =>
        inputRowConstant
          (rowMultiplier (denseDegree (system equation)) (Fin.succ equation)
            (basis system)[i])
          (basis system)[j] (denseDegree (system equation)) (system equation))
      (basisRowEquation system i)

/-- Along Canny's path the full executable Macaulay matrix is a constant
matrix minus `T` times the identity. -/
theorem cannyParameterEval_matrix {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (i j : Fin (basis system).length) :
    cannyParameterEval (F := F) (matrix system i j) =
      Polynomial.C (cannyConstantMatrix system i j) -
        if i = j then Polynomial.X else 0 := by
  rw [matrix_apply]
  generalize hequation : basisRowEquation system i = equation
  cases equation using Fin.cases with
  | zero =>
      simp only [equationDegree, Fin.cases_zero, homogeneousTerms,
        cannyConstantMatrix, hequation]
      rw [cannyParameterEval_rowEntry_auxiliary]
      have htarget := pairedTarget_eq_column_iff system i j
      simp only [hequation, equationDegree, Fin.cases_zero] at htarget
      by_cases hij : i = j
      · rw [if_pos (htarget.mpr hij), if_pos hij]
        simp
      · rw [if_neg (fun h => hij (htarget.mp h)), if_neg hij]
        simp
  | succ equation =>
      simp only [equationDegree, Fin.cases_succ, homogeneousTerms,
        cannyConstantMatrix, hequation]
      rw [cannyParameterEval_rowEntry_perturbed]
      have htarget := pairedTarget_eq_column_iff system i j
      simp only [hequation, equationDegree, Fin.cases_succ] at htarget
      by_cases hij : i = j
      · rw [if_pos (htarget.mpr hij), if_pos hij]
        ring
      · rw [if_neg (fun h => hij (htarget.mp h)), if_neg hij]
        simp

omit [BEq F] [LawfulBEq F] in
theorem extraneousIndices_nodup {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (extraneousIndices system).Nodup := by
  unfold extraneousIndices
  apply List.Nodup.filter
  rw [List.nodup_ofFn]
  exact Function.injective_id

omit [BEq F] [LawfulBEq F] in
theorem extraneousIndex_injective {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Function.Injective (extraneousIndex (system := system)) := by
  change Function.Injective fun i => (extraneousIndices system).get i
  intro i j hij
  exact (extraneousIndices_nodup system).get_inj_iff.mp hij

/-- Constant part of the extraneous principal minor under Canny's parameter
specialization. -/
def cannyExtraneousConstantMatrix {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    Matrix (ExtraneousIndex system) (ExtraneousIndex system) F :=
  (cannyConstantMatrix system).submatrix extraneousIndex extraneousIndex

/-- Entrywise specialization of the extraneous minor. -/
theorem cannyParameterEval_extraneousMatrix {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (i j : ExtraneousIndex system) :
    cannyParameterEval (F := F) (extraneousMatrix system i j) =
      Polynomial.C (cannyExtraneousConstantMatrix system i j) -
        if i = j then Polynomial.X else 0 := by
  unfold extraneousMatrix cannyExtraneousConstantMatrix
  simp only [Matrix.submatrix_apply]
  rw [cannyParameterEval_matrix]
  by_cases hij : i = j
  · subst j
    simp
  · have hindex : extraneousIndex i ≠ extraneousIndex j := by
      intro h
      exact hij (extraneousIndex_injective system h)
    simp [hij, hindex]

/-- The specialized extraneous minor is the negative characteristic matrix
of its constant part. -/
theorem cannyParameterEval_extraneousMatrix_eq {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    (cannyParameterEval (F := F)).mapMatrix (extraneousMatrix system) =
      -(cannyExtraneousConstantMatrix system).charmatrix := by
  funext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    cannyParameterEval_extraneousMatrix]
  rw [Matrix.neg_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.charmatrix_apply_eq]
    simp
  · rw [Matrix.charmatrix_apply_ne _ _ _ hij]
    simp [hij]

/-- Canny's parameter specialization sends the extraneous factor to a unit
multiple of a monic characteristic polynomial. -/
theorem cannyParameterEval_extraneousFactor {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    cannyParameterEval (F := F) (extraneousFactor system) =
      (-1) ^ (extraneousIndices system).length *
        (cannyExtraneousConstantMatrix system).charpoly := by
  unfold extraneousFactor
  rw [RingHom.map_det, cannyParameterEval_extraneousMatrix_eq,
    Matrix.det_neg]
  simp only [Fintype.card_fin, Matrix.charpoly]

/-- The executable extraneous determinant never vanishes.  This is proved
directly from the stored matrix by Canny's characteristic-polynomial
specialization, without assuming a resultant identity. -/
theorem extraneousFactor_ne_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F) :
    extraneousFactor system ≠ 0 := by
  intro hzero
  have hmapped := congrArg (cannyParameterEval (F := F)) hzero
  rw [cannyParameterEval_extraneousFactor, _root_.map_zero] at hmapped
  have hsign : ((-1 : Polynomial F) ^
      (extraneousIndices system).length) ≠ 0 := pow_ne_zero _ (by simp)
  exact (cannyExtraneousConstantMatrix system).charpoly_monic.ne_zero
    (mul_eq_zero.mp hmapped |>.resolve_left hsign)

/-- When no non-reduced monomial occurs, Macaulay's extraneous principal
minor is empty and its determinant is one. -/
theorem extraneousFactor_eq_one_of_extraneousIndices_eq_nil {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (hindices : extraneousIndices system = []) :
    extraneousFactor system = 1 := by
  unfold extraneousFactor
  apply Matrix.det_eq_one_of_card_eq_zero
  simp [hindices]

/-- The Macaulay determinant identity is immediate in the empty-minor branch:
the extraneous factor is the unit polynomial. -/
theorem extraneousFactor_dvd_characteristic_of_extraneousIndices_eq_nil
    {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hindices : extraneousIndices system = []) :
    extraneousFactor system ∣ characteristic system := by
  rw [extraneousFactor_eq_one_of_extraneousIndices_eq_nil system hindices]
  exact one_dvd _

/-- In the empty-minor (Sylvester-type) branch, executable division succeeds
unconditionally and returns the full characteristic determinant. -/
theorem macaulayQuotient?_eq_some_characteristic_of_extraneousIndices_eq_nil
    [DecidableEq F] {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (hindices : extraneousIndices system = []) :
    macaulayQuotient? system = some (characteristic system) := by
  apply macaulayQuotient?_complete_of_identity (extraneousFactor_ne_zero system)
  rw [extraneousFactor_eq_one_of_extraneousIndices_eq_nil system hindices]
  simp

end ArkLib.Rojas.Producer.MacaulayQuotient
