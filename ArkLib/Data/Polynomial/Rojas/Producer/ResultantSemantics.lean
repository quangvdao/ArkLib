/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotientCorrectness
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Root semantics of the dense Macaulay determinant

This file proves the vanishing direction of Macaulay's construction directly
from the executable matrix.  After specializing its parameter coefficients,
the vector of critical-degree monomial values is a kernel vector whenever the
stored homogeneous equations have a common nonzero projective root.  Hence the
specialized determinant vanishes.

The theorem applies to the determinant multiple.  Cancelling the computed
extraneous minor after specialization requires the separate Macaulay
quotient/resultant theorem; no such cancellation is assumed here.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.ResultantSemantics

open CPoly CPoly.CMvPolynomial
open DenseMacaulay

variable {F K : Type*} [CommRing F] [BEq F] [LawfulBEq F]
  [CommRing K]

/-- Values assigned to `(u₀,...,uₙ,s)`, with `s` in the final coordinate. -/
def parameterAssignment {n : ℕ} (u : Fin (n + 1) → K) (s : K) :
    Fin (n + 2) → K :=
  Fin.snoc u s

/-- Evaluation of a parameter polynomial, bundled as a ring homomorphism. -/
def parameterEvalHom {n : ℕ} (ι : F →+* K) (u : Fin (n + 1) → K) (s : K) :
    Parameters n F →+* K :=
  CMvPolynomial.eval₂Hom ι (parameterAssignment u s)

@[simp]
theorem parameterEvalHom_apply {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (p : Parameters n F) :
    parameterEvalHom ι u s p = p.eval₂ ι (parameterAssignment u s) := rfl

/-- Value of one projective monomial at a point. -/
def monomialValue {count : ℕ} (z : Fin count → K) (m : CMvMonomial count) : K :=
  ∏ i, z i ^ m.get i

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem monomialValue_add {count : ℕ} (z : Fin count → K)
    (left right : CMvMonomial count) :
    monomialValue z (left + right) = monomialValue z left * monomialValue z right := by
  have hget (i : Fin count) :
      (left + right).get i = left.get i + right.get i := by
    exact Vector.getElem_zipWith i.isLt
  simp only [monomialValue, hget, pow_add, Finset.prod_mul_distrib]

/-- Evaluation of an executable homogeneous term list. -/
def homogeneousTermsValue {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (z : Fin (n + 1) → K)
    (terms : HomogeneousTerms n F) : K :=
  (terms.map fun term =>
    parameterEvalHom ι u s term.2 * monomialValue z term.1).sum

/-- The actual homogeneous equations stored by the matrix vanish at `z`. -/
def IsCommonProjectiveRoot {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (z : Fin (n + 1) → K)
    (system : Fin n → CMvPolynomial n F) : Prop :=
  ∀ equation, homogeneousTermsValue ι u s z (homogeneousTerms system equation) = 0

private theorem eval_rowEntry_fold {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K)
    (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F) (accumulator : Parameters n F) :
    parameterEvalHom ι u s
        (terms.foldl
          (fun result term =>
            if multiplier + term.1 = column then result + term.2 else result)
          accumulator) =
      parameterEvalHom ι u s accumulator +
        (terms.map fun term =>
          if multiplier + term.1 = column then parameterEvalHom ι u s term.2 else 0).sum := by
  induction terms generalizing accumulator with
  | nil => simp
  | cons term terms ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      split
      · rw [_root_.map_add]
        ac_rfl
      · simp only [zero_add]

/-- Evaluation exposes `rowEntry` as the sum of exactly the coefficients whose
shifted monomial equals the requested column. -/
theorem eval_rowEntry {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K)
    (multiplier column : CMvMonomial (n + 1))
    (terms : HomogeneousTerms n F) :
    parameterEvalHom ι u s (rowEntry multiplier column terms) =
      (terms.map fun term =>
        if multiplier + term.1 = column then parameterEvalHom ι u s term.2 else 0).sum := by
  rw [rowEntry, eval_rowEntry_fold]
  have hzero : parameterEvalHom ι u s (0 : Parameters n F) = 0 :=
    _root_.map_zero (parameterEvalHom ι u s)
  rw [hzero, zero_add]

omit [BEq F] [LawfulBEq F] in
/-- Total degree is additive on computable monomials. -/
theorem totalDegree_add {count : ℕ} (left right : CMvMonomial count) :
    (left + right).totalDegree = left.totalDegree + right.totalDegree := by
  have hget (i : Fin count) :
      (left + right).get i = left.get i + right.get i := by
    exact Vector.getElem_zipWith i.isLt
  simp only [DenseMacaulay.totalDegree_eq_sum_get, hget,
    Finset.sum_add_distrib]

omit [BEq F] [LawfulBEq F] in
/-- The paired leading power restores a valid Macaulay row after division. -/
theorem rowMultiplier_add_powerMonomial {count degree : ℕ}
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
  change ((row.get ⟨j, hj⟩ - if (⟨j, hj⟩ : Fin count) = equation then degree else 0) +
      if (⟨j, hj⟩ : Fin count) = equation then degree else 0) = row.get ⟨j, hj⟩
  by_cases hje : (⟨j, hj⟩ : Fin count) = equation
  · subst equation
    simp [hdegree]
  · simp [hje]

omit [BEq F] [LawfulBEq F] in
/-- Dividing a row by its assigned power lowers total degree by exactly the
equation degree. -/
theorem totalDegree_rowMultiplier_add {count degree : ℕ}
    (equation : Fin count) (row : CMvMonomial count)
    (hdegree : degree ≤ row.get equation) :
    (rowMultiplier degree equation row).totalDegree + degree = row.totalDegree := by
  have hrestore := congrArg CMvMonomial.totalDegree
    (rowMultiplier_add_powerMonomial equation row hdegree)
  rw [totalDegree_add] at hrestore
  have hpower : (powerMonomial equation degree).totalDegree = degree := by
    rw [DenseMacaulay.totalDegree_eq_sum_get]
    simp [powerMonomial]
  rw [hpower] at hrestore
  exact hrestore

omit [BEq F] [LawfulBEq F] in
/-- The total degree of a stored monomial is bounded by the polynomial's
stored total degree. -/
theorem monomial_totalDegree_le {count : ℕ} (polynomial : CMvPolynomial count F)
    (m : CMvMonomial count) (hm : m ∈ polynomial.monomials) :
    m.totalDegree ≤ polynomial.totalDegree := by
  unfold CMvPolynomial.totalDegree
  have hmember : m.toFinsupp ∈
      (polynomial.monomials.map CMvMonomial.toFinsupp).toFinset := by
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨m, hm, rfl⟩
  calc
    m.totalDegree = Finsupp.sum m.toFinsupp (fun _ exponent => exponent) := by
      rw [DenseMacaulay.totalDegree_eq_sum_get, Finsupp.sum_fintype]
      · rfl
      · intro i
        simp
    _ ≤ Finset.sup
        (polynomial.monomials.map CMvMonomial.toFinsupp).toFinset
        (fun support => Finsupp.sum support (fun _ exponent => exponent)) :=
      Finset.le_sup
        (f := fun support : Fin count →₀ ℕ =>
          Finsupp.sum support (fun _ exponent => exponent)) hmember

omit [BEq F] [LawfulBEq F] in
/-- Homogenizing a stored affine monomial to the dense degree envelope gives
exactly that homogeneous degree. -/
theorem homogenizedMonomial_totalDegree {n : ℕ}
    (polynomial : CMvPolynomial n F) (m : CMvMonomial n)
    (hm : m ∈ polynomial.monomials) :
    (homogenizedMonomial (denseDegree polynomial) m).totalDegree =
      denseDegree polynomial := by
  rw [homogenizedMonomial, DenseMacaulay.totalDegree_insertIdx_zero]
  have hle : m.totalDegree ≤ denseDegree polynomial :=
    (monomial_totalDegree_le polynomial m hm).trans (le_max_right _ _)
  omega

omit [BEq F] [LawfulBEq F] in
/-- A paired pure power has its declared degree. -/
theorem powerMonomial_totalDegree {count degree : ℕ} (i : Fin count) :
    (powerMonomial i degree).totalDegree = degree := by
  rw [DenseMacaulay.totalDegree_eq_sum_get]
  simp [powerMonomial]

/-- Every monomial in an executable homogeneous equation has exactly the
declared equation degree. -/
theorem homogeneousTerm_totalDegree {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (equation : Fin (n + 1))
    (term : CMvMonomial (n + 1) × Parameters n F)
    (hterm : term ∈ homogeneousTerms system equation) :
    term.1.totalDegree = equationDegree system equation := by
  cases equation using Fin.cases with
  | zero =>
      simp only [homogeneousTerms, Fin.cases_zero] at hterm
      unfold auxiliaryTerms at hterm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hterm
      exact powerMonomial_totalDegree i
  | succ i =>
      simp only [homogeneousTerms, Fin.cases_succ] at hterm
      unfold perturbedTerms at hterm
      rw [List.mem_append] at hterm
      rcases hterm with hsource | hperturbation
      · obtain ⟨sourceTerm, hsourceMem, hsourceEq⟩ := List.mem_map.mp hsource
        have hkey : sourceTerm.1 ∈ (system i).val.toList.map Prod.fst :=
          List.mem_map.mpr ⟨sourceTerm, hsourceMem, rfl⟩
        have hsourceMonomial : sourceTerm.1 ∈ (system i).monomials := by
          simpa only [Std.ExtTreeMap.map_fst_toList_eq_keys] using hkey
        subst term
        simp only [equationDegree, Fin.cases_succ]
        exact homogenizedMonomial_totalDegree (system i) sourceTerm.1 hsourceMonomial
      · simp only [List.mem_singleton] at hperturbation
        subst term
        simp only [equationDegree, Fin.cases_succ]
        exact powerMonomial_totalDegree (Fin.succ i)

/-- Every term shifted by the assigned row multiplier is another column of
the critical-degree basis. -/
theorem rowTarget_mem_basis {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length)
    (term : CMvMonomial (n + 1) × Parameters n F)
    (hterm : term ∈ homogeneousTerms system (basisRowEquation system i)) :
    rowMultiplier
        (equationDegree system (basisRowEquation system i))
        (basisRowEquation system i) (basis system)[i] + term.1 ∈ basis system := by
  rw [DenseMacaulay.mem_basis_iff_totalDegree]
  rw [totalDegree_add, homogeneousTerm_totalDegree system _ term hterm]
  have hselected := DenseMacaulay.rowEquation?_eq_some_degree_le
    (equationDegree system) (basis system)[i]
    (basisRowEquation system i) (DenseMacaulay.rowEquation?_basis_eq_some system i)
  rw [totalDegree_rowMultiplier_add _ _ hselected]
  exact DenseMacaulay.mem_weakCompositions_totalDegree (List.getElem_mem i.isLt)

omit [BEq F] [LawfulBEq F] in
private theorem singleColumnSum {count : ℕ} (z : Fin count → K)
    (columns : List (CMvMonomial count)) (hcolumns : columns.Nodup)
    (target : CMvMonomial count) (htarget : target ∈ columns) (coefficient : K) :
    (∑ j : Fin columns.length,
      (if target = columns[j] then coefficient else 0) *
        monomialValue z columns[j]) =
      coefficient * monomialValue z target := by
  rw [← List.sum_ofFn]
  let contribution := fun column : CMvMonomial count =>
    (if target = column then coefficient else 0) * monomialValue z column
  change (List.ofFn fun j => contribution columns[j]).sum = _
  have hofFn : (List.ofFn fun j : Fin columns.length => contribution columns[j]) =
      columns.map contribution := by
    exact List.ofFn_getElem_eq_map columns contribution
  rw [hofFn]
  rw [← List.sum_toFinset _ hcolumns]
  simp [contribution, htarget]

/-- A row of coefficient lookups, paired with the vector of monomial values,
evaluates to the assigned multiplier times the stored homogeneous equation. -/
theorem rowEntry_mulVec_sum {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (z : Fin (n + 1) → K)
    (columns : List (CMvMonomial (n + 1))) (hcolumns : columns.Nodup)
    (multiplier : CMvMonomial (n + 1)) (terms : HomogeneousTerms n F)
    (htargets : ∀ term ∈ terms, multiplier + term.1 ∈ columns) :
    (∑ j : Fin columns.length,
      parameterEvalHom ι u s (rowEntry multiplier columns[j] terms) *
        monomialValue z columns[j]) =
      monomialValue z multiplier * homogeneousTermsValue ι u s z terms := by
  unfold homogeneousTermsValue
  simp_rw [eval_rowEntry]
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      rw [ih (fun remaining hremaining => htargets remaining (by simp [hremaining]))]
      rw [singleColumnSum z columns hcolumns (multiplier + term.1)
        (htargets term (by simp))]
      rw [monomialValue_add]
      ring

/-- Parameter-specialized executable Macaulay matrix. -/
def specializedMatrix {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K)
    (system : Fin n → CMvPolynomial n F) :
    Matrix (Fin (basis system).length) (Fin (basis system).length) K :=
  (parameterEvalHom ι u s).mapMatrix (matrix system)

/-- Critical-degree monomial values at a projective point. -/
def monomialVector {n : ℕ} (z : Fin (n + 1) → K)
    (system : Fin n → CMvPolynomial n F) : Fin (basis system).length → K :=
  fun j => monomialValue z (basis system)[j]

/-- Exact row action of the specialized matrix on the monomial-value vector. -/
theorem specializedMatrix_mulVec_apply {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (z : Fin (n + 1) → K)
    (system : Fin n → CMvPolynomial n F)
    (i : Fin (basis system).length) :
    (specializedMatrix ι u s system).mulVec (monomialVector z system) i =
      monomialValue z
          (rowMultiplier
            (equationDegree system (basisRowEquation system i))
            (basisRowEquation system i) (basis system)[i]) *
        homogeneousTermsValue ι u s z
          (homogeneousTerms system (basisRowEquation system i)) := by
  rw [Matrix.mulVec_apply]
  change (∑ j : Fin (basis system).length,
    parameterEvalHom ι u s (matrix system i j) *
      monomialValue z (basis system)[j]) = _
  calc
    _ = ∑ j : Fin (basis system).length,
        parameterEvalHom ι u s
          (rowEntry
            (rowMultiplier
              (equationDegree system (basisRowEquation system i))
              (basisRowEquation system i) (basis system)[i])
            (basis system)[j]
            (homogeneousTerms system (basisRowEquation system i))) *
          monomialValue z (basis system)[j] := by
      apply Finset.sum_congr rfl
      intro j _
      rw [DenseMacaulay.matrix_apply]
    _ = _ := rowEntry_mulVec_sum (F := F) (K := K) ι u s z (basis system)
      (DenseMacaulay.basis_nodup system)
      (rowMultiplier
        (equationDegree system (basisRowEquation system i))
        (basisRowEquation system i) (basis system)[i])
      (homogeneousTerms system (basisRowEquation system i))
      (rowTarget_mem_basis system i)

omit [BEq F] [LawfulBEq F] in
/-- A nonzero projective point gives a nonzero monomial-value vector. -/
theorem monomialVector_ne_zero {n : ℕ} (z : Fin (n + 1) → K)
    (system : Fin n → CMvPolynomial n F)
    [IsDomain K]
    (hz : ∃ coordinate, z coordinate ≠ 0) : monomialVector z system ≠ 0 := by
  obtain ⟨coordinate, hcoordinate⟩ := hz
  let target := powerMonomial coordinate (macaulayDegree system)
  have htarget : target ∈ basis system := by
    rw [DenseMacaulay.mem_basis_iff_totalDegree]
    exact powerMonomial_totalDegree coordinate
  obtain ⟨index, hindex⟩ := List.get_of_mem htarget
  intro hzero
  have hvalue := congrFun hzero index
  change monomialValue z ((basis system).get index) = 0 at hvalue
  rw [hindex] at hvalue
  have htargetValue : monomialValue z target =
      z coordinate ^ macaulayDegree system := by
    simp [target, monomialValue, powerMonomial]
  rw [htargetValue] at hvalue
  exact pow_ne_zero _ hcoordinate hvalue

/-- A common projective root is an actual kernel vector of the specialized
executable Macaulay matrix. -/
theorem specializedMatrix_mulVec_eq_zero {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (z : Fin (n + 1) → K)
    (system : Fin n → CMvPolynomial n F)
    (hroot : IsCommonProjectiveRoot ι u s z system) :
    (specializedMatrix ι u s system).mulVec (monomialVector z system) = 0 := by
  funext i
  rw [specializedMatrix_mulVec_apply]
  rw [hroot]
  simp

/-- Vanishing theorem for the input-derived Macaulay determinant multiple:
every common nonzero projective root makes its parameter specialization zero. -/
theorem characteristic_eval_eq_zero_of_commonProjectiveRoot {n : ℕ}
    (ι : F →+* K) (u : Fin (n + 1) → K) (s : K)
    (z : Fin (n + 1) → K) (system : Fin n → CMvPolynomial n F)
    [IsDomain K]
    (hz : ∃ coordinate, z coordinate ≠ 0)
    (hroot : IsCommonProjectiveRoot ι u s z system) :
    parameterEvalHom ι u s (characteristic system) = 0 := by
  have hkernel : ∃ vector, vector ≠ 0 ∧
      (specializedMatrix ι u s system).mulVec vector = 0 :=
    ⟨monomialVector z system, monomialVector_ne_zero z system hz,
      specializedMatrix_mulVec_eq_zero ι u s z system hroot⟩
  have hdet : (specializedMatrix ι u s system).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp hkernel
  rw [characteristic, RingHom.map_det]
  exact hdet

/-- Embed an affine point into the standard projective chart `z₀ = 1`. -/
def affinePoint {n : ℕ} (x : Fin n → K) : Fin (n + 1) → K :=
  Fin.cons 1 x

/-- The auxiliary affine hyperplane evaluated at a point. -/
def affineLinearValue {n : ℕ} (u : Fin (n + 1) → K) (x : Fin n → K) : K :=
  ∑ i, u i * affinePoint x i

/-- Every input equation in the executable square system vanishes at `x`. -/
def IsCommonAffineRoot {n : ℕ} (ι : F →+* K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F) : Prop :=
  ∀ i, (system i).eval₂ ι x = 0

omit [BEq F] [LawfulBEq F] in
/-- Homogenizing an affine monomial does not change its value in the standard
chart. -/
theorem monomialValue_affinePoint_homogenized {n degree : ℕ}
    (x : Fin n → K) (m : CMvMonomial n) :
    monomialValue (affinePoint x) (homogenizedMonomial degree m) =
      monomialValue x m := by
  rw [monomialValue, Fin.prod_univ_succ]
  simp only [affinePoint, Fin.cons_zero, homogenizedMonomial,
    DenseMacaulay.get_insertIdx_zero, one_pow, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  have hget :
      (m.insertIdx 0 (degree - m.totalDegree)).get i.succ = m.get i := by
    exact Vector.getElem_insertIdx_of_gt (xs := m) (i := 0)
      (k := i.val + 1) (by omega) (by omega)
  rw [hget]
  simp

omit [BEq F] [LawfulBEq F] in
private theorem eval₂_eq_termListValue {n : ℕ} (ι : F →+* K)
    (x : Fin n → K) (polynomial : CMvPolynomial n F) :
    polynomial.eval₂ ι x =
      (polynomial.val.toList.map fun term =>
        ι term.2 * monomialValue x term.1).sum := by
  unfold CMvPolynomial.eval₂
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hfold : ∀ (terms : List (CMvMonomial n × F)) (accumulator : K),
      terms.foldl
          (fun accumulator term =>
            ι term.2 * MonoR.evalMonomial x term.1 + accumulator)
          accumulator =
        (terms.map fun term => ι term.2 * monomialValue x term.1).sum + accumulator := by
    intro terms
    induction terms with
    | nil => intro accumulator; simp
    | cons term terms ih =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        unfold monomialValue MonoR.evalMonomial
        ac_rfl
  rw [hfold]
  simp

/-- Executable evaluation of an auxiliary coefficient returns its supplied
hyperplane coordinate. -/
theorem eval_auxiliaryCoefficient {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (i : Fin (n + 1)) :
    parameterEvalHom ι u s (auxiliaryCoefficient i) = u i := by
  rw [parameterEvalHom_apply]
  unfold auxiliaryCoefficient
  rw [CPoly.eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_pow]
  rw [_root_.map_one]
  simp_rw [show ∀ a, (auxiliaryParameterMonomial i).toFinsupp a =
      (auxiliaryParameterMonomial i).get a from fun _ => rfl]
  change (1 : K) *
    (∏ a, parameterAssignment u s a ^ (auxiliaryParameterMonomial i).get a) = u i
  simp only [one_mul, auxiliaryParameterMonomial, Vector.get_ofFn,
    pow_ite, pow_one, pow_zero]
  have hindex : ∀ a : Fin (n + 2), (a.val = i.val) = (a = i.castSucc) := by
    intro a
    apply propext
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; subst a; rfl
  simp_rw [hindex]
  simp [parameterAssignment]

/-- The executable auxiliary term list evaluates to its affine linear form. -/
theorem homogeneousTermsValue_auxiliary_affine {n : ℕ}
    (ι : F →+* K) (u : Fin (n + 1) → K) (s : K) (x : Fin n → K) :
    homogeneousTermsValue ι u s (affinePoint x) auxiliaryTerms =
      affineLinearValue u x := by
  unfold homogeneousTermsValue auxiliaryTerms affineLinearValue
  rw [← List.ofFn_comp', List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_auxiliaryCoefficient]
  have hpure : monomialValue (affinePoint x) (powerMonomial i 1) =
      affinePoint x i := by
    simp [monomialValue, powerMonomial]
  rw [hpure, mul_comm]

/-- At `s = 0`, a perturbed homogeneous source equation evaluates to the
original affine input equation. -/
theorem homogeneousTermsValue_perturbed_affine_zero {n : ℕ}
    (ι : F →+* K) (u : Fin (n + 1) → K) (x : Fin n → K)
    (i : Fin n) (polynomial : CMvPolynomial n F) :
    homogeneousTermsValue ι u 0 (affinePoint x)
        (perturbedTerms (Fin.succ i) (denseDegree polynomial) polynomial) =
      polynomial.eval₂ ι x := by
  unfold homogeneousTermsValue perturbedTerms
  rw [List.map_append, List.sum_append]
  simp only [List.map_map, List.map_singleton, List.sum_singleton]
  rw [eval₂_eq_termListValue]
  have hsource :
      (List.map
        (fun term =>
          parameterEvalHom ι u 0 (CMvPolynomial.C term.2) *
            monomialValue (affinePoint x)
              (homogenizedMonomial (denseDegree polynomial) term.1))
        polynomial.val.toList).sum =
      (List.map (fun term => ι term.2 * monomialValue x term.1)
        polynomial.val.toList).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro term hterm
    rw [monomialValue_affinePoint_homogenized]
    change (CMvPolynomial.C term.2).eval₂ ι (parameterAssignment u 0) * _ = _
    rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C]
    simp
  change
    (List.map
        (fun term =>
          parameterEvalHom ι u 0 (CMvPolynomial.C term.2) *
            monomialValue (affinePoint x)
              (homogenizedMonomial (denseDegree polynomial) term.1))
        polynomial.val.toList).sum +
      parameterEvalHom ι u 0 (negativeS (F := F) (n := n)) *
        monomialValue (affinePoint x)
          (powerMonomial (Fin.succ i) (denseDegree polynomial)) = _
  rw [hsource]
  have hnegative : parameterEvalHom ι u 0 (negativeS (F := F) (n := n)) = 0 := by
    rw [parameterEvalHom_apply]
    unfold negativeS
    rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_monomial,
      MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
    rw [_root_.map_neg, _root_.map_one]
    simp_rw [show ∀ a, (sParameterMonomial (n := n)).toFinsupp a =
        (sParameterMonomial (n := n)).get a from fun _ => rfl]
    change (-1 : K) *
      (∏ a, parameterAssignment u 0 a ^ (sParameterMonomial (n := n)).get a) = 0
    simp only [sParameterMonomial, Vector.get_ofFn, pow_ite, pow_one, pow_zero]
    have hindex : ∀ a : Fin (n + 2),
        (a.val = n + 1) = (a = Fin.last (n + 1)) := by
      intro a
      apply propext
      constructor
      · intro h; apply Fin.ext; exact h
      · intro h; subst a; rfl
    simp_rw [hindex]
    simp [parameterAssignment]
  rw [hnegative]
  simp

/-- An affine input root on the auxiliary hyperplane gives a common root of
the actual homogeneous term lists stored by the matrix. -/
theorem commonProjectiveRoot_of_affineRoot {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F)
    (hlinear : affineLinearValue u x = 0)
    (hroot : IsCommonAffineRoot ι x system) :
    IsCommonProjectiveRoot ι u 0 (affinePoint x) system := by
  intro equation
  cases equation using Fin.cases with
  | zero =>
      simpa [homogeneousTerms] using
        (homogeneousTermsValue_auxiliary_affine ι u 0 x).trans hlinear
  | succ i =>
      simpa [homogeneousTerms] using
        (homogeneousTermsValue_perturbed_affine_zero ι u x i (system i)).trans
          (hroot i)

/-- Direct affine vanishing corollary for the computed Macaulay determinant
multiple. -/
theorem characteristic_eval_zero_of_affineRoot {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F)
    [IsDomain K]
    (hlinear : affineLinearValue u x = 0)
    (hroot : IsCommonAffineRoot ι x system) :
    parameterEvalHom ι u 0 (characteristic system) = 0 := by
  apply characteristic_eval_eq_zero_of_commonProjectiveRoot ι u 0
    (affinePoint x) system
  · exact ⟨0, by simp [affinePoint]⟩
  · exact commonProjectiveRoot_of_affineRoot ι u x system hlinear hroot

end ArkLib.Rojas.Producer.ResultantSemantics
