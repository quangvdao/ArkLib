/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian
public import ArkLib.Data.Polynomial.Rojas.AffineSolver
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Selected affine chart systems

A selected set supplies exactly `r` actual agreement equations beside the chart equation in
`r+1` variables. Nonsingularity concerns their executed formal derivatives, without identifying
the stored Taylor separant with a derivative of the chart equation. The isolation conclusion
allows arbitrary coefficient embeddings and unrelated positive-dimensional components.

This adapter does not construct the chart tangent-independence proof. Stored agreement rows
already have exactly `k` coefficient terms; no extra differential-residual or tail rows are added.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine

open CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.HiddenDerivative.SquareSystems
open DirectJacobian

universe u v w

variable {E : Type u} {L : Type v} [Field E] [BEq E] [LawfulBEq E] [Field L]
variable {n r k : ℕ}

/-- Materialize the chart equation followed by the selected actual agreement rows. -/
def selectedChartSystem (chart : ChartData E r k) (domain received : Fin n → E)
    (selected : Finset (Fin n)) (hcard : selected.card = r) :
    Fin (r + 1) → CMvPolynomial (r + 1) E :=
  squareSystemRows chart.equation (chartAgreementRows chart domain received)
    (rowSubsetEmbedding selected hcard)

@[simp]
theorem selectedChartSystem_zero (chart : ChartData E r k) (domain received : Fin n → E)
    (selected : Finset (Fin n)) (hcard : selected.card = r) :
    selectedChartSystem chart domain received selected hcard 0 = chart.equation := rfl

@[simp]
theorem selectedChartSystem_succ (chart : ChartData E r k) (domain received : Fin n → E)
    (selected : Finset (Fin n)) (hcard : selected.card = r) (j : Fin r) :
    selectedChartSystem chart domain received selected hcard j.succ =
      chart.agreement (domain (rowSubsetEmbedding selected hcard j))
        (received (rowSubsetEmbedding selected hcard j)) := rfl

/-- The canonical row index still belongs to the chosen set of received positions. -/
theorem selected_index_mem (selected : Finset (Fin n)) (hcard : selected.card = r)
    (j : Fin r) : rowSubsetEmbedding selected hcard j ∈ selected := by
  have h : rowSubsetEmbedding selected hcard j ∈
      Set.range (selected.orderEmbOfFin hcard) := ⟨j, rfl⟩
  rwa [Finset.range_orderEmbOfFin] at h

/-- Each successor row comes from an actual selected received position. -/
theorem selectedChartSystem_agreement (chart : ChartData E r k)
    (domain received : Fin n → E) (selected : Finset (Fin n))
    (hcard : selected.card = r) (j : Fin r) :
    ∃ i ∈ selected, selectedChartSystem chart domain received selected hcard j.succ =
      chart.agreement (domain i) (received i) :=
  ⟨_, selected_index_mem selected hcard j, rfl⟩

/-- The same selected system belongs to the all-subsets executable family. -/
theorem selectedChartSystem_mem [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (selected : Finset (Fin n))
    (hcard : selected.card = r) :
    selectedChartSystem chart domain received selected hcard ∈
      directChartSystems chart domain received :=
  squareSystemRows_mem_enumerate _ _ selected hcard

/-- Common-zero capture needs the actual selected residuals to vanish, with no separant premise. -/
theorem selectedChartSystem_commonZero (chart : ChartData E r k)
    (domain received : Fin n → E) (selected : Finset (Fin n))
    (hcard : selected.card = r) (base : E →+* L) (point : Fin (r + 1) → L)
    (hequation : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hagree : ∀ i ∈ selected,
      CMvPolynomial.eval₂ base point (chart.agreement (domain i) (received i)) = 0) :
    ∀ row, CMvPolynomial.eval₂ base point
      (selectedChartSystem chart domain received selected hcard row) = 0 := by
  intro row
  exact Fin.cases hequation
    (fun j ↦ hagree _ (selected_index_mem selected hcard j)) row

/-- The executed Jacobian is precisely the chart normal followed by selected differentials. -/
theorem selectedChartSystem_jacobianRows (chart : ChartData E r k)
    (domain received : Fin n → E) (selected : Finset (Fin n))
    (hcard : selected.card = r) (base : E →+* L) (point : Fin (r + 1) → L)
    (row column : Fin (r + 1)) :
    evaluatedJacobian base point (selectedChartSystem chart domain received selected hcard)
        row column =
      Fin.cases (evaluatedDifferential base point chart.equation)
        (fun j ↦ evaluatedDifferential base point
          (chart.agreement (domain (rowSubsetEmbedding selected hcard j))
            (received (rowSubsetEmbedding selected hcard j)))) row (Pi.single column 1) := by
  induction row using Fin.cases with
  | zero => exact (evaluatedDifferential_single base point chart.equation column).symm
  | succ j => exact (evaluatedDifferential_single base point _ column).symm

/-- Injectivity of the executed square Jacobian action gives a nonzero determinant. -/
theorem evaluatedJacobian_det_ne_zero_of_injective {m : ℕ}
    (base : E →+* L) (point : Fin m → L) (system : Fin m → CMvPolynomial m E)
    (hinj : Function.Injective (evaluatedJacobianMap base point system)) :
    (evaluatedJacobian base point system).det ≠ 0 := by
  classical
  have hmap : (evaluatedJacobian base point system).mulVec =
      evaluatedJacobianMap base point system := by
    funext direction row
    exact (evaluatedJacobianMap_apply base point system direction row).symm
  have hunit : IsUnit (evaluatedJacobian base point system) :=
    Matrix.mulVec_injective_iff_isUnit.mp (hmap ▸ hinj)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

/-- The isolation neighborhood remains valid in any further extension universe. -/
theorem hasIsolatingPolynomial_of_actualJacobian {m : ℕ}
    (base : E →+* L) (point : Fin m → L) (system : Fin m → CMvPolynomial m E)
    (hzero : ∀ row, CMvPolynomial.eval₂ base point (system row) = 0)
    (hdet : (evaluatedJacobian base point system).det ≠ 0) :
    MvPolynomial.HasIsolatingPolynomial.{w, v}
      (ArkLib.Rojas.AffineSolver.mappedSystem base system) point := by
  apply MvPolynomial.hasIsolatingPolynomial_of_jacobian_det_ne_zero
  · intro row
    simpa [ArkLib.Rojas.AffineSolver.mappedSystem, CPoly.eval₂_equiv] using hzero row
  · convert hdet using 1
    congr 1
    funext row column
    simp only [ArkLib.Rojas.AffineSolver.mappedSystem, evaluatedJacobian]
    rw [MvPolynomial.pderiv_map, ← CMvPolynomial.fromCMvPolynomial_partialDerivative]
    simp [CPoly.eval₂_equiv]

/-- A nonsingular selected common zero is isolated over every further field extension.
The remaining input is independence of the actual computed Jacobian, not a solver certificate. -/
theorem selectedChartSystem_capture [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (selected : Finset (Fin n))
    (hcard : selected.card = r) (base : E →+* L) (point : Fin (r + 1) → L)
    (hequation : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hagree : ∀ i ∈ selected,
      CMvPolynomial.eval₂ base point (chart.agreement (domain i) (received i)) = 0)
    (hinj : Function.Injective (evaluatedJacobianMap base point
      (selectedChartSystem chart domain received selected hcard))) :
    let system := selectedChartSystem chart domain received selected hcard
    system ∈ directChartSystems chart domain received ∧
      (∀ row, CMvPolynomial.eval₂ base point (system row) = 0) ∧
      (evaluatedJacobian base point system).det ≠ 0 ∧
      MvPolynomial.HasIsolatingPolynomial.{w, v}
        (ArkLib.Rojas.AffineSolver.mappedSystem base system) point := by
  have hzero := selectedChartSystem_commonZero chart domain received selected hcard
    base point hequation hagree
  have hdet := evaluatedJacobian_det_ne_zero_of_injective base point _ hinj
  exact ⟨selectedChartSystem_mem chart domain received selected hcard, hzero, hdet,
    hasIsolatingPolynomial_of_actualJacobian base point _ hzero hdet⟩

end ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine
