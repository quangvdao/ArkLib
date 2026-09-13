/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneCoverage
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# A structural nonabsorption criterion for Macaulay's extraneous factor

For every degree pattern, setting `u₀ = 1` and retaining `s` symbolically
gives the extraneous determinant a unit coefficient in degree equal to the
number of nonauxiliary extraneous rows. The proof selects the unique `-s`
diagonal contribution from each such row; the remaining auxiliary principal
minor is unit lower triangular. Thus the full extraneous factor cannot vanish
identically on the root hyperplane of a point with a nonzero coordinate.

The file also retains the sharper constant-coefficient result under the exact,
input-derived condition that every extraneous row is auxiliary-assigned.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.ExtraneousHyperplane

open CPoly CPoly.CMvPolynomial
open DenseMacaulay MacaulayQuotient ResultantSemantics
open HyperplaneCoverage HyperplaneFactor

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem rowMultiplier_add_powerMonomial_succ_get_zero {n : ℕ}
    (row : CMvMonomial (n + 1)) (k : Fin n) :
    (rowMultiplier 1 0 row + powerMonomial k.succ 1).get 0 = row.get 0 - 1 := by
  change (CMvMonomial.add (rowMultiplier 1 0 row) (powerMonomial k.succ 1)).get 0 =
    row.get 0 - 1
  unfold CMvMonomial.add
  change (Vector.zipWith (fun x y : ℕ => x + y)
    (rowMultiplier 1 0 row) (powerMonomial k.succ 1))[0] = row[0] - 1
  rw [Vector.getElem_zipWith]
  simp [rowMultiplier, powerMonomial]
  congr 1

private theorem eval_rowEntry_auxiliary_eq_zero_of {n : ℕ} (u : Fin (n + 1) → F)
    (row column : CMvMonomial (n + 1)) (hrow : 1 ≤ row.get 0)
    (hne : row ≠ column) (hle : row.get 0 ≤ column.get 0) :
    parameterEvalHom (RingHom.id F) u 0
      (rowEntry (rowMultiplier 1 0 row) column (auxiliaryTerms (F := F))) = 0 := by
  rw [eval_rowEntry]
  unfold auxiliaryTerms
  rw [← List.ofFn_comp', List.sum_ofFn]
  apply Finset.sum_eq_zero
  intro j _
  split
  · rename_i heq
    cases j using Fin.cases with
    | zero =>
      exfalso
      apply hne
      exact (rowMultiplier_add_powerMonomial (0 : Fin (n + 1)) row hrow).symm.trans heq
    | succ k =>
      have heq' : rowMultiplier 1 0 row + powerMonomial k.succ 1 = column := by
        simpa using heq
      have hcoordinate := congrArg (fun m : CMvMonomial (n + 1) => m.get 0) heq'
      rw [rowMultiplier_add_powerMonomial_succ_get_zero] at hcoordinate
      omega
  · rfl

private theorem eval_rowEntry_auxiliary_diagonal {n : ℕ} (u : Fin (n + 1) → F)
    (row : CMvMonomial (n + 1)) (hrow : 1 ≤ row.get 0) :
    parameterEvalHom (RingHom.id F) u 0
      (rowEntry (rowMultiplier 1 0 row) row (auxiliaryTerms (F := F))) = u 0 := by
  rw [eval_rowEntry]
  unfold auxiliaryTerms
  rw [← List.ofFn_comp', List.sum_ofFn]
  rw [Fin.sum_univ_succ]
  simp only [eval_auxiliaryCoefficient]
  rw [if_pos (rowMultiplier_add_powerMonomial (0 : Fin (n + 1)) row hrow)]
  have hsum : (∑ k : Fin n,
      if rowMultiplier 1 0 row + powerMonomial k.succ 1 = row then u k.succ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro heq
    have hcoordinate := congrArg (fun m : CMvMonomial (n + 1) => m.get 0) heq
    rw [rowMultiplier_add_powerMonomial_succ_get_zero] at hcoordinate
    omega
  rw [hsum, add_zero]

/-- Executable test that every retained extraneous row is assigned to the
auxiliary equation. -/
def auxiliaryAssignedExtraneousB {n : ℕ}
    (system : Fin n → CMvPolynomial n F) : Bool :=
  (extraneousIndices system).all fun i => basisRowEquation system i == 0

/-- The computed extraneous minor uses only auxiliary-equation rows. -/
def AuxiliaryAssignedExtraneous {n : ℕ}
    (system : Fin n → CMvPolynomial n F) : Prop :=
  auxiliaryAssignedExtraneousB system = true

omit [BEq F] [LawfulBEq F] in
private theorem extraneousRow_zeroCoordinate {n : ℕ}
    {system : Fin n → CMvPolynomial n F}
    (h : AuxiliaryAssignedExtraneous system)
    (i : ExtraneousIndex system) : 1 ≤ (basis system)[extraneousIndex i].get 0 := by
  have hi : basisRowEquation system (extraneousIndex i) = 0 := by
    unfold AuxiliaryAssignedExtraneous auxiliaryAssignedExtraneousB at h
    have hall := List.all_eq_true.mp h
    have hrow := hall (extraneousIndex i) (List.get_mem (extraneousIndices system) i)
    simpa using hrow
  have hs := rowEquation?_basis_eq_some system (extraneousIndex i)
  have hd := rowEquation?_eq_some_degree_le (equationDegree system)
    (basis system)[extraneousIndex i] (basisRowEquation system (extraneousIndex i)) hs
  rw [hi] at hd
  simpa [equationDegree] using hd

/-- Put the constant auxiliary coefficient at one and retain all other
auxiliary coefficients. -/
def auxiliaryWithConstantOne {n : ℕ} (u : Fin n → F) : Fin (n + 1) → F :=
  Fin.cons 1 u

private def extraneousOrderKey {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (i : ExtraneousIndex system) : Lex (ℕ × ℕ) :=
  toLex ((basis system)[extraneousIndex i].get 0, i.val)

omit [BEq F] [LawfulBEq F] in
private theorem extraneousOrderKey_injective {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Function.Injective (extraneousOrderKey system) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Lex (ℕ × ℕ) => (ofLex x).2) hij

/-- If every extraneous row is auxiliary-assigned, setting `s = 0` and
`u₀ = 1` makes the extraneous determinant one for all other `u` values. -/
theorem extraneousFactor_eval_auxiliaryConstant_eq_one {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (h : AuxiliaryAssignedExtraneous system) (u : Fin n → F) :
    parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
      (extraneousFactor system) = 1 := by
  let _ : LinearOrder (ExtraneousIndex system) :=
    LinearOrder.lift' (extraneousOrderKey system) (extraneousOrderKey_injective system)
  have hrowEquation (i : ExtraneousIndex system) :
      basisRowEquation system (extraneousIndex i) = 0 := by
    unfold AuxiliaryAssignedExtraneous auxiliaryAssignedExtraneousB at h
    have hall := List.all_eq_true.mp h
    have hrow := hall (extraneousIndex i) (List.get_mem (extraneousIndices system) i)
    simpa using hrow
  unfold extraneousFactor
  rw [RingHom.map_det]
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    simp only [RingHom.mapMatrix_apply]
    unfold extraneousMatrix
    change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
      (matrix system (extraneousIndex i) (extraneousIndex j)) = 0
    rw [matrix_apply]
    rw [hrowEquation i]
    simp only [equationDegree, Fin.cases_zero]
    change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
      (rowEntry (rowMultiplier 1 0 (basis system)[extraneousIndex i])
        (basis system)[extraneousIndex j] auxiliaryTerms) = 0
    have hkey : extraneousOrderKey system i < extraneousOrderKey system j := hij
    have hkeys : Prod.Lex (· < ·) (· < ·)
        ((basis system)[extraneousIndex i].get 0, i.val)
        ((basis system)[extraneousIndex j].get 0, j.val) := by
      exact hij
    rw [Prod.lex_def] at hkeys
    have hle : (basis system)[extraneousIndex i].get 0 ≤
        (basis system)[extraneousIndex j].get 0 := by
      rcases hkeys with hfirst | ⟨heq, _⟩
      · exact hfirst.le
      · exact heq.le
    have hne : (basis system)[extraneousIndex i] ≠
        (basis system)[extraneousIndex j] := by
      intro hrow
      have hBasis : Function.Injective
          (fun k : Fin (basis system).length => (basis system)[k]) := by
        rw [← List.nodup_ofFn]
        simpa using basis_nodup system
      have hExtraNodup : (extraneousIndices system).Nodup := by
        unfold extraneousIndices
        exact (List.nodup_ofFn.mpr fun a b hab => hab).filter _
      have hExtra : Function.Injective (@extraneousIndex F _ n system) := by
        change Function.Injective
          (fun a : Fin (extraneousIndices system).length => (extraneousIndices system)[a])
        exact hExtraNodup.injective_get
      have : i = j := hExtra (hBasis hrow)
      subst j
      exact (lt_irrefl (extraneousOrderKey system i) hkey)
    exact eval_rowEntry_auxiliary_eq_zero_of (auxiliaryWithConstantOne u) _ _
      (extraneousRow_zeroCoordinate h i) hne hle)]
  apply Finset.prod_eq_one
  intro i _
  simp only [RingHom.mapMatrix_apply]
  unfold extraneousMatrix
  change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
    (matrix system (extraneousIndex i) (extraneousIndex i)) = 1
  rw [matrix_apply]
  rw [hrowEquation i]
  simp only [equationDegree, Fin.cases_zero]
  change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
    (rowEntry (rowMultiplier 1 0 (basis system)[extraneousIndex i])
      (basis system)[extraneousIndex i] auxiliaryTerms) = 1
  simpa [auxiliaryWithConstantOne] using
    eval_rowEntry_auxiliary_diagonal (auxiliaryWithConstantOne u)
      (basis system)[extraneousIndex i] (extraneousRow_zeroCoordinate h i)

section MatrixCoefficient

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private theorem coeff_det_C_add_X_smul_rows (A B : Matrix ι ι R) (k : ℕ) :
    (Matrix.det (B.map Polynomial.C +
      (Polynomial.X : Polynomial R) • A.map Polynomial.C)).coeff k =
    ∑ s ∈ Finset.univ.powersetCard k,
      Matrix.det (Matrix.of <| s.piecewise A.row B.row) := by
  simp only [Matrix.det]
  let D := (Matrix.detRowAlternating :
    (ι → Polynomial R) [⋀^ι]→ₗ[Polynomial R] Polynomial R)
  rw [add_comm]
  change (D (fun i => ((Polynomial.X : Polynomial R) • A.map Polynomial.C) i +
    (B.map Polynomial.C) i)).coeff k = _
  conv_lhs => rw [show (fun i => ((Polynomial.X : Polynomial R) • A.map Polynomial.C) i +
      (B.map Polynomial.C) i) =
      (fun i => ((Polynomial.X : Polynomial R) • A.map Polynomial.C) i) +
        (fun i => (B.map Polynomial.C) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  have h_map : ∀ s : Finset ι,
        (s.piecewise (fun i => (A.map Polynomial.C) i)
        (fun i => (B.map Polynomial.C) i) : Matrix ι ι (Polynomial R)) =
        Matrix.map (Matrix.of <| s.piecewise A.row B.row) Polynomial.C := by
    intro s; ext i j
    simp only [Finset.piecewise, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> rfl
  have h_det : ∀ s : Finset ι,
      D (s.piecewise (fun i => (A.map Polynomial.C) i)
        (fun i => (B.map Polynomial.C) i)) =
      Polynomial.C (Matrix.det (Matrix.of <| s.piecewise A.row B.row)) := by
    intro s; change Matrix.det _ = _
    rw [h_map]; exact (RingHom.map_det Polynomial.C _).symm
  calc
    (∑ s : Finset ι, D (Finset.piecewise s
          (fun i => ((Polynomial.X : Polynomial R) • A.map Polynomial.C) i)
          (fun i => (B.map Polynomial.C) i))).coeff k
      = (∑ s : Finset ι, (Polynomial.X : Polynomial R) ^ s.card •
            D (s.piecewise (fun i => (A.map Polynomial.C) i)
              (fun i => (B.map Polynomial.C) i))).coeff k := by
        congr 2 with s
        have h_smul : s.piecewise
            (fun i => ((Polynomial.X : Polynomial R) • A.map Polynomial.C) i)
            (fun i => (B.map Polynomial.C) i) =
            fun i => (if i ∈ s then (Polynomial.X : Polynomial R) else 1) •
              s.piecewise (fun i => (A.map Polynomial.C) i)
                (fun i => (B.map Polynomial.C) i) i := by
          funext i j
          simp only [Finset.piecewise, Pi.smul_apply,
            smul_eq_mul, ite_mul, one_mul]
          split_ifs <;> rfl
        rw [h_smul, D.map_smul_univ]
        congr 1
        simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      _ = ∑ s : Finset ι, ((Polynomial.X : Polynomial R) ^ s.card •
            D (Finset.piecewise s (fun i => (A.map Polynomial.C) i)
              (fun i => (B.map Polynomial.C) i))).coeff k := by
        simp only [Polynomial.finsetSum_coeff]
      _ = _ := by
        simp_rw [h_det, smul_eq_mul,
          mul_comm (Polynomial.X ^ _) (Polynomial.C _)]
        simp_rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
        rw [← Finset.sum_filter]
        have h_set : Finset.univ.filter (fun s : Finset ι => s.card = k) =
            Finset.univ.powersetCard k := by
          ext s; simp [Finset.mem_powersetCard]
        rw [h_set]
        apply Finset.sum_congr rfl
        intro s _
        rfl

private def negDiagonalOn (s : Finset ι) : Matrix ι ι R :=
  Matrix.diagonal fun i => if i ∈ s then -1 else 0

private theorem coeff_det_C_add_X_smul_negDiagonalOn (B : Matrix ι ι R) (s : Finset ι) :
    (Matrix.det (B.map Polynomial.C + (Polynomial.X : Polynomial R) •
      (negDiagonalOn s).map Polynomial.C)).coeff s.card =
      Matrix.det (Matrix.of <| s.piecewise (negDiagonalOn s).row B.row) := by
  rw [coeff_det_C_add_X_smul_rows]
  apply Finset.sum_eq_single s
  · intro t ht hne
    have ht' : t.card = s.card := by
      simpa [Finset.mem_powersetCard] using ht
    have hnotSubset : ¬ t ⊆ s := by
      intro hsubset
      apply hne
      exact Finset.eq_of_subset_of_card_le hsubset (Nat.le_of_eq ht'.symm)
    obtain ⟨i, hit, his⟩ := Finset.not_subset.mp hnotSubset
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp [hit, negDiagonalOn, Matrix.diagonal_apply, his]
  · intro hs
    exfalso
    exact (hs (by simp))

end MatrixCoefficient

private theorem eval_negativeS_polynomial {n : ℕ} (u : Fin (n + 1) → F) :
    parameterEvalHom Polynomial.C (Polynomial.C ∘ u) Polynomial.X
      (negativeS (F := F) (n := n)) = -Polynomial.X := by
  rw [parameterEvalHom_apply]
  unfold negativeS
  rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp_rw [show ∀ a, (sParameterMonomial (n := n)).toFinsupp a =
      (sParameterMonomial (n := n)).get a from fun _ => rfl]
  simp only [sParameterMonomial, Vector.get_ofFn, pow_ite, pow_one, pow_zero]
  have hindex : ∀ a : Fin (n + 2), (a.val = n + 1) = (a = Fin.last (n + 1)) := by
    intro a
    apply propext
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; subst a; rfl
  simp_rw [hindex]
  simp [parameterAssignment]

private theorem eval_C_polynomial {n : ℕ} (u : Fin (n + 1) → F) (c : F) :
    parameterEvalHom Polynomial.C (fun i => Polynomial.C (u i)) Polynomial.X
    (CMvPolynomial.C c : Parameters n F) = Polynomial.C c := by
  rw [parameterEvalHom_apply]
  rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C]
  simp

private theorem eval_C_zero {n : ℕ} (u : Fin (n + 1) → F) (c : F) :
    parameterEvalHom (RingHom.id F) u 0 (CMvPolynomial.C c : Parameters n F) = c := by
  rw [parameterEvalHom_apply, CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C]
  simp

private theorem eval_negativeS_zero {n : ℕ} (u : Fin (n + 1) → F) :
    parameterEvalHom (RingHom.id F) u 0 (negativeS (F := F) (n := n)) = 0 := by
  rw [parameterEvalHom_apply]
  unfold negativeS
  rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp_rw [show ∀ a, (sParameterMonomial (n := n)).toFinsupp a =
      (sParameterMonomial (n := n)).get a from fun _ => rfl]
  simp only [sParameterMonomial, Vector.get_ofFn, pow_ite, pow_one, pow_zero]
  have hindex : ∀ a : Fin (n + 2), (a.val = n + 1) = (a = Fin.last (n + 1)) := by
    intro a
    apply propext
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; subst a; rfl
  simp_rw [hindex]
  simp [parameterAssignment]

private theorem eval_rowEntry_perturbed_polynomial {n : ℕ} (u : Fin (n + 1) → F)
    (equation : Fin (n + 1)) (degree : ℕ) (f : CMvPolynomial n F)
    (multiplier column : CMvMonomial (n + 1)) :
    parameterEvalHom Polynomial.C (Polynomial.C ∘ u) Polynomial.X
      (rowEntry multiplier column (perturbedTerms equation degree f)) =
    Polynomial.C (parameterEvalHom (RingHom.id F) u 0
      (rowEntry multiplier column (perturbedTerms equation degree f))) +
      if multiplier + powerMonomial equation degree = column then -Polynomial.X else 0 := by
  rw [eval_rowEntry, eval_rowEntry]
  unfold perturbedTerms
  simp only [List.map_append, List.sum_append, List.map_map,
    List.map_singleton, List.sum_singleton]
  rw [eval_negativeS_polynomial, eval_negativeS_zero]
  simp only [Function.comp_def]
  simp_rw [eval_C_polynomial]
  simp_rw [eval_C_zero]
  have hsource :
      (List.map (fun x => if multiplier + homogenizedMonomial degree x.1 = column then
          Polynomial.C x.2 else 0) f.val.toList).sum =
        Polynomial.C (List.map (fun x =>
          if multiplier + homogenizedMonomial degree x.1 = column then x.2 else 0)
          f.val.toList).sum := by
    rw [map_list_sum]
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    split <;> simp_all
  rw [hsource]
  split <;> simp

private theorem eval_rowEntry_auxiliary_polynomial {n : ℕ} (u : Fin (n + 1) → F)
    (multiplier column : CMvMonomial (n + 1)) :
    parameterEvalHom Polynomial.C (Polynomial.C ∘ u) Polynomial.X
      (rowEntry multiplier column (auxiliaryTerms (F := F))) =
    Polynomial.C (parameterEvalHom (RingHom.id F) u 0
      (rowEntry multiplier column (auxiliaryTerms (F := F))) ) := by
  rw [eval_rowEntry, eval_rowEntry]
  unfold auxiliaryTerms
  rw [← List.ofFn_comp', ← List.ofFn_comp', List.sum_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, eval_auxiliaryCoefficient]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

/-- Extraneous rows assigned to perturbed input equations rather than the auxiliary form. -/
def nonAuxiliaryExtraneousRows {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Finset (ExtraneousIndex system) :=
  Finset.univ.filter fun i => basisRowEquation system (extraneousIndex i) ≠ 0

private def perturbationDiagonal {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Matrix (ExtraneousIndex system) (ExtraneousIndex system) F :=
  Matrix.diagonal fun i => if i ∈ nonAuxiliaryExtraneousRows system then -1 else 0

private def zeroSpecializedExtraneousMatrix {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (u : Fin (n + 1) → F) : Matrix (ExtraneousIndex system) (ExtraneousIndex system) F :=
  (parameterEvalHom (RingHom.id F) u 0).mapMatrix (extraneousMatrix system)

omit [BEq F] [LawfulBEq F] in
private theorem extraneousBasis_injective {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Function.Injective (fun i : ExtraneousIndex system => (basis system)[extraneousIndex i]) := by
  intro i j hb
  have hBasis : Function.Injective
      (fun k : Fin (basis system).length => (basis system)[k]) := by
    rw [← List.nodup_ofFn]
    simpa using basis_nodup system
  have hExtraNodup : (extraneousIndices system).Nodup := by
    unfold extraneousIndices
    exact (List.nodup_ofFn.mpr fun a b hab => hab).filter _
  have hExtra : Function.Injective (@extraneousIndex F _ n system) := by
    change Function.Injective
      (fun a : Fin (extraneousIndices system).length => (extraneousIndices system)[a])
    exact hExtraNodup.injective_get
  exact hExtra (hBasis hb)

private theorem eval_extraneousMatrix_polynomial {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (u : Fin (n + 1) → F) :
    (parameterEvalHom Polynomial.C (Polynomial.C ∘ u) Polynomial.X).mapMatrix
      (extraneousMatrix system) =
    (zeroSpecializedExtraneousMatrix system u).map (Polynomial.C : F →+* Polynomial F) +
      (Polynomial.X : Polynomial F) •
        (perturbationDiagonal system).map (Polynomial.C : F →+* Polynomial F) := by
  ext i j : 1
  simp only [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply]
  unfold extraneousMatrix zeroSpecializedExtraneousMatrix
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [show extraneousMatrix system i j =
    matrix system (extraneousIndex i) (extraneousIndex j) from rfl]
  rw [matrix_apply]
  cases heq : basisRowEquation system (extraneousIndex i) using Fin.cases with
  | zero =>
      simp only [equationDegree, homogeneousTerms, Fin.cases_zero]
      rw [eval_rowEntry_auxiliary_polynomial]
      by_cases hij : i = j
      · subst j
        simp [perturbationDiagonal, nonAuxiliaryExtraneousRows, heq]
      · rw [show perturbationDiagonal system i j = 0 from by
          unfold perturbationDiagonal
          exact Matrix.diagonal_apply_ne _ hij]
        simp
  | succ equation =>
      simp only [equationDegree, homogeneousTerms, Fin.cases_succ]
      rw [eval_rowEntry_perturbed_polynomial]
      have hdegree := rowEquation?_eq_some_degree_le (equationDegree system)
        (basis system)[extraneousIndex i] (basisRowEquation system (extraneousIndex i))
        (rowEquation?_basis_eq_some system (extraneousIndex i))
      have hrestore := rowMultiplier_add_powerMonomial
        (basisRowEquation system (extraneousIndex i))
        (basis system)[extraneousIndex i] hdegree
      have hmatch :
          (rowMultiplier
              (equationDegree system (basisRowEquation system (extraneousIndex i)))
              (basisRowEquation system (extraneousIndex i))
              (basis system)[extraneousIndex i] +
            powerMonomial (basisRowEquation system (extraneousIndex i))
              (equationDegree system (basisRowEquation system (extraneousIndex i))) =
            (basis system)[extraneousIndex j]) ↔ i = j := by
        rw [hrestore]
        constructor
        · intro hbasis
          exact extraneousBasis_injective system hbasis
        · intro hij; subst j; rfl
      have hmatch' :
          (rowMultiplier (denseDegree (system equation)) equation.succ
                (basis system)[extraneousIndex i] +
              powerMonomial equation.succ (denseDegree (system equation)) =
            (basis system)[extraneousIndex j]) ↔ i = j := by
        simpa [heq, equationDegree] using hmatch
      by_cases hij : i = j
      · subst j
        have hdiagonalMatch := hmatch'.2 rfl
        rw [if_pos hdiagonalMatch]
        simp [perturbationDiagonal, nonAuxiliaryExtraneousRows, heq]
      · have hnotMatch := (not_congr hmatch').2 hij
        rw [if_neg hnotMatch]
        rw [show perturbationDiagonal system i j = 0 from by
          unfold perturbationDiagonal
          exact Matrix.diagonal_apply_ne _ hij]
        simp

omit [BEq F] [LawfulBEq F] in
private theorem extraneousRow_zeroCoordinate_of_auxiliary {n : ℕ}
    {system : Fin n → CMvPolynomial n F} (i : ExtraneousIndex system)
    (hi : basisRowEquation system (extraneousIndex i) = 0) :
    1 ≤ (basis system)[extraneousIndex i].get 0 := by
  have hs := rowEquation?_basis_eq_some system (extraneousIndex i)
  have hd := rowEquation?_eq_some_degree_le (equationDegree system)
    (basis system)[extraneousIndex i]
    (basisRowEquation system (extraneousIndex i)) hs
  rw [hi] at hd
  simpa [equationDegree] using hd

private theorem det_piecewise_perturbationDiagonal_eq {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (u : Fin n → F) :
    Matrix.det (Matrix.of <| (nonAuxiliaryExtraneousRows system).piecewise
      (perturbationDiagonal system).row
      (zeroSpecializedExtraneousMatrix system (auxiliaryWithConstantOne u)).row) =
      (-1 : F) ^ (nonAuxiliaryExtraneousRows system).card := by
  let _ : LinearOrder (ExtraneousIndex system) :=
    LinearOrder.lift' (extraneousOrderKey system) (extraneousOrderKey_injective system)
  let selected := nonAuxiliaryExtraneousRows system
  let mixed : Matrix (ExtraneousIndex system) (ExtraneousIndex system) F :=
    Matrix.of <| selected.piecewise (perturbationDiagonal system).row
      (zeroSpecializedExtraneousMatrix system (auxiliaryWithConstantOne u)).row
  change Matrix.det mixed = _
  rw [Matrix.det_of_isLowerTriangular mixed (by
    intro i j hij
    change extraneousOrderKey system i < extraneousOrderKey system j at hij
    have hneij : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl (extraneousOrderKey system i) hij)
    by_cases hi : i ∈ selected
    · simp [mixed, Finset.piecewise, hi, perturbationDiagonal, selected, hneij]
    · have hrowEquation : basisRowEquation system (extraneousIndex i) = 0 := by
        simpa [selected, nonAuxiliaryExtraneousRows] using hi
      simp only [mixed, Matrix.of_apply, Finset.piecewise, hi]
      change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
        (matrix system (extraneousIndex i) (extraneousIndex j)) = 0
      rw [matrix_apply, hrowEquation]
      simp only [equationDegree, Fin.cases_zero]
      change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
        (rowEntry (rowMultiplier 1 0 (basis system)[extraneousIndex i])
          (basis system)[extraneousIndex j] auxiliaryTerms) = 0
      have hkeys : Prod.Lex (· < ·) (· < ·)
          ((basis system)[extraneousIndex i].get 0, i.val)
          ((basis system)[extraneousIndex j].get 0, j.val) := hij
      rw [Prod.lex_def] at hkeys
      have hle : (basis system)[extraneousIndex i].get 0 ≤
          (basis system)[extraneousIndex j].get 0 := by
        rcases hkeys with hfirst | ⟨heq, _⟩
        · exact hfirst.le
        · exact heq.le
      have hne : (basis system)[extraneousIndex i] ≠
          (basis system)[extraneousIndex j] := by
        intro hbasis
        exact hneij (extraneousBasis_injective system hbasis)
      exact eval_rowEntry_auxiliary_eq_zero_of (auxiliaryWithConstantOne u) _ _
        (extraneousRow_zeroCoordinate_of_auxiliary i hrowEquation) hne hle)]
  calc
    ∏ i, mixed i i = ∏ i, if i ∈ selected then (-1 : F) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ selected
      · simp [mixed, Finset.piecewise, hi, perturbationDiagonal, selected]
      · have hrowEquation : basisRowEquation system (extraneousIndex i) = 0 := by
          simpa [selected, nonAuxiliaryExtraneousRows] using hi
        simp only [mixed, Matrix.of_apply, Finset.piecewise, hi, if_false]
        change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
          (matrix system (extraneousIndex i) (extraneousIndex i)) = 1
        rw [matrix_apply, hrowEquation]
        simp only [equationDegree, Fin.cases_zero]
        change parameterEvalHom (RingHom.id F) (auxiliaryWithConstantOne u) 0
          (rowEntry (rowMultiplier 1 0 (basis system)[extraneousIndex i])
            (basis system)[extraneousIndex i] auxiliaryTerms) = 1
        simpa [auxiliaryWithConstantOne] using
          eval_rowEntry_auxiliary_diagonal (auxiliaryWithConstantOne u)
            (basis system)[extraneousIndex i]
            (extraneousRow_zeroCoordinate_of_auxiliary i hrowEquation)
    _ = (-1 : F) ^ selected.card := by
      simp
    _ = (-1 : F) ^ (nonAuxiliaryExtraneousRows system).card := rfl

/-- After setting `u₀ = 1`, the coefficient in perturbation degree equal to
the number of nonauxiliary extraneous rows is a unit. It is independent of the
input coefficients and of the remaining auxiliary parameters. -/
theorem extraneousFactor_polynomialEvaluation_coeff_nonAuxiliaryRows {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (u : Fin n → F) :
    (parameterEvalHom Polynomial.C
      (Polynomial.C ∘ auxiliaryWithConstantOne u) Polynomial.X
      (extraneousFactor system)).coeff
        (nonAuxiliaryExtraneousRows system).card =
      (-1 : F) ^ (nonAuxiliaryExtraneousRows system).card := by
  unfold extraneousFactor
  rw [RingHom.map_det]
  rw [eval_extraneousMatrix_polynomial]
  change (Matrix.det
    ((zeroSpecializedExtraneousMatrix system (auxiliaryWithConstantOne u)).map Polynomial.C +
      Polynomial.X • (perturbationDiagonal system).map Polynomial.C)).coeff
        (nonAuxiliaryExtraneousRows system).card = _
  rw [show perturbationDiagonal system =
      negDiagonalOn (nonAuxiliaryExtraneousRows system) from rfl]
  rw [coeff_det_C_add_X_smul_negDiagonalOn]
  exact det_piecewise_perturbationDiagonal_eq system u

/-- A point on the parameter hyperplane `u₀ + ∑ uᵢ pointᵢ = 1` obtained
from any nonzero coordinate of `point`. -/
noncomputable def hyperplaneWitness {n : ℕ} (point : Fin n → F)
    (k : Fin n) : Fin n → F :=
  fun i => if i = k then -(point k)⁻¹ else 0

omit [BEq F] [LawfulBEq F] in
private theorem eval_hyperplaneRoot_witness {n : ℕ} (point : Fin n → F)
    (k : Fin n) (hk : point k ≠ 0) :
    MvPolynomial.eval (hyperplaneWitness point k)
      (hyperplaneRoot point) = 1 := by
  simp [hyperplaneRoot, hyperplaneWitness, hk]

/-- Setting `u₀ = 1` and leaving `s` symbolic never annihilates the complete
computed extraneous factor. -/
theorem extraneousFactor_polynomialEvaluation_ne_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (u : Fin n → F) :
    parameterEvalHom Polynomial.C
      (Polynomial.C ∘ auxiliaryWithConstantOne u) Polynomial.X
      (extraneousFactor system) ≠ 0 := by
  intro hzero
  have htop := extraneousFactor_polynomialEvaluation_coeff_nonAuxiliaryRows system u
  rw [hzero] at htop
  exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) htop.symm

/-- A root hyperplane with a nonzero coordinate has a concrete point at which
the full extraneous factor, with `s` retained as a polynomial variable, is
nonzero. This is the semantic full-factor nonabsorption witness. -/
theorem extraneousFactor_rootHyperplane_witness_ne_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (k : Fin n) (hk : point k ≠ 0) :
    parameterEvalHom Polynomial.C
      (fun i => Polynomial.C (MvPolynomial.eval (hyperplaneWitness point k)
        (symbolicParameters point i))) Polynomial.X
      (extraneousFactor system) ≠ 0 := by
  have hparameters : (fun i : Fin (n + 1) =>
      MvPolynomial.eval (hyperplaneWitness point k) (symbolicParameters point i)) =
      auxiliaryWithConstantOne (hyperplaneWitness point k) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [symbolicParameters, auxiliaryWithConstantOne] using
        eval_hyperplaneRoot_witness point k hk
    · simp [symbolicParameters, auxiliaryWithConstantOne]
  have hparametersC : (fun i : Fin (n + 1) =>
      Polynomial.C (MvPolynomial.eval (hyperplaneWitness point k)
        (symbolicParameters point i))) =
      Polynomial.C ∘ auxiliaryWithConstantOne (hyperplaneWitness point k) := by
    funext i
    exact congrArg Polynomial.C (congrFun hparameters i)
  rw [hparametersC]
  exact extraneousFactor_polynomialEvaluation_ne_zero system (hyperplaneWitness point k)

/-- Under the computed row-assignment condition, the constant `s` coefficient
of the extraneous factor does not vanish identically on a root hyperplane. -/
theorem hyperplaneSubstitution_constantExtraneousFactor_ne_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (h : AuxiliaryAssignedExtraneous system)
    (point : Fin n → F) (k : Fin n) (hk : point k ≠ 0) :
    hyperplaneSubstitution point
      (fromCMvPolynomial (coefficientInS 0 (extraneousFactor system))) ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval (hyperplaneWitness point k)) hzero
  rw [hyperplaneSubstitution_eq_eval₂,
    MvPolynomial.eval_eval₂] at heval
  rw [← CPoly.eval₂_equiv,
    eval₂_coefficientInS_zero] at heval
  have hcoeff : (MvPolynomial.eval (hyperplaneWitness point k)).comp MvPolynomial.C =
      RingHom.id F := by
    ext coefficient
    simp
  have hparameters : (fun i : Fin (n + 1) =>
      MvPolynomial.eval (hyperplaneWitness point k)
        (symbolicParameters point i)) =
      auxiliaryWithConstantOne (hyperplaneWitness point k) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [symbolicParameters,
        auxiliaryWithConstantOne] using eval_hyperplaneRoot_witness point k hk
    · simp [symbolicParameters,
        auxiliaryWithConstantOne]
  rw [hcoeff, hparameters] at heval
  rw [extraneousFactor_eval_auxiliaryConstant_eq_one system h (hyperplaneWitness point k)] at heval
  simp at heval

/-- Equivalently, the root hyperplane is not a factor of the constant `s`
coefficient of the computed extraneous determinant. -/
theorem affineLinearForm_not_dvd_constantExtraneousFactor {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (h : AuxiliaryAssignedExtraneous system)
    (point : Fin n → F) (k : Fin n) (hk : point k ≠ 0) :
    ¬ affineLinearForm point ∣
      fromCMvPolynomial (coefficientInS 0 (extraneousFactor system)) := by
  rw [affineLinearForm_dvd_iff]
  exact hyperplaneSubstitution_constantExtraneousFactor_ne_zero system h point k hk

end ArkLib.Rojas.Producer.ExtraneousHyperplane
