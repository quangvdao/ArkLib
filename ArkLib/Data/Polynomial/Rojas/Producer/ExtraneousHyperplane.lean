/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneCoverage
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# A structural nonabsorption criterion for Macaulay's extraneous factor

When every row of the computed extraneous minor is assigned to the auxiliary
equation, setting `s = 0` and `u₀ = 1` makes that minor unit lower triangular,
for arbitrary remaining auxiliary parameters. Consequently its constant
`s` coefficient cannot contain the root hyperplane of any nonzero affine point.

The row-assignment premise is an exact, input-derived condition. It is not
claimed for all degree patterns.
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
theorem extraneousFactor_eval_auxiliaryConstant_eq_one {n : ℕ} (system : Fin n → CMvPolynomial n F)
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

private noncomputable def hyperplaneWitness {n : ℕ} (point : Fin n → F)
    (k : Fin n) : Fin n → F :=
  fun i => if i = k then -(point k)⁻¹ else 0

omit [BEq F] [LawfulBEq F] in
private theorem eval_hyperplaneRoot_witness {n : ℕ} (point : Fin n → F)
    (k : Fin n) (hk : point k ≠ 0) :
    MvPolynomial.eval (hyperplaneWitness point k)
      (hyperplaneRoot point) = 1 := by
  simp [hyperplaneRoot, hyperplaneWitness, hk]

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
