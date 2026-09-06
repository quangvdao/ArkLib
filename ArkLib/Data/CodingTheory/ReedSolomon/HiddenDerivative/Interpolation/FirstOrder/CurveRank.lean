/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# First-order rank bounds for polynomial received curves

The first-order constraint-rank theorem holds over every field. Applying it over `F(Z)`
therefore controls polynomial received curves just as it controls lines. The received
polynomials may have any degree: batching degree affects coefficient heights, not rank.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve

variable {F : Type*} [Field F]

/-- The symbolic first-order matrix has the certified global rank bound over `F(Z)`.
The proof factors it through the actual global constraint map on the capped support. -/
theorem firstOrder_curve_matrix_rank_le {D A m M μ n N : ℕ}
    (hD : 1 < D) (centers : Fin n → F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((constraintMatrix m centers w columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      n * certifiedEnlargedRankBound 1 m M 0 := by
  classical
  let K := RatFunc F
  let φ : F[X] →+* K := algebraMap F[X] K
  let V := firstOrderSpace K D A m M μ
  let monomial (j : Fin N) : V := ⟨(columns j).polynomial, by
    apply mem_firstOrderSpace_iff.mpr
    intro u hu
    have heq : u = (columns j).exponent := by
      simpa [SourceColumn.polynomial] using MvPolynomial.support_monomial_subset hu
    exact heq ▸ heligible j⟩
  let assemble : (Fin N → K) →ₗ[K] V :=
    ∑ j, (LinearMap.smulRight (LinearMap.proj j) (monomial j))
  let constraint := firstOrderGlobalConstraint (D := D) (A := A) (m := m) (M := M) (μ := μ)
    (fun i ↦ φ (Polynomial.C (centers i))) (fun i ↦ φ (w i))
  let coefficients : (Fin n → LocalPolynomial K 1) →ₗ[K]
      ((Fin n × LowContactIndex 1 m) → K) :=
    LinearMap.pi fun row ↦ MvPolynomial.lcoeff K row.2.1 ∘ₗ LinearMap.proj row.1
  let mat := (constraintMatrix m centers w columns).map φ
  have hfactor : mat.mulVecLin = coefficients ∘ₗ constraint ∘ₗ assemble := by
    apply LinearMap.ext
    intro v
    funext row
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      LinearMap.comp_apply, coefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
      LinearMap.proj_apply, assemble, LinearMap.sum_apply, map_sum, LinearMap.smulRight_apply,
      map_smul]
    change (∑ j, φ (constraintMatrix m centers w columns row j) * v j) = _
    simp only [constraint, firstOrderGlobalConstraint, LinearMap.pi_apply,
      firstOrderLocalConstraintAt, LinearMap.domRestrict_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : constraintMatrix m centers w columns row j =
        MvPolynomial.coeff row.2.1
          (localConstraintAt m (Polynomial.C (centers row.1)) (w row.1)
            (columns j).polynomial) := by
      simp [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients,
        localConstraintAt, projectLowContact, coeff_filterLocalMonomials, row.2.2]
    rw [hentry]
    rw [← MvPolynomial.coeff_map, map_localConstraintAt]
    simp [monomial, SourceColumn.polynomial, mul_comm]
  let _ : Module.Finite K V := Module.Finite.of_basis (firstOrderSpaceBasis K D A m M μ)
  change Module.finrank K mat.mulVecLin.range ≤ _
  rw [hfactor]
  apply (finrank_range_comp_le_outer (coefficients ∘ₗ constraint) assemble).trans
  rw [LinearMap.range_comp]
  apply (Submodule.finrank_map_le coefficients constraint.range).trans
  simpa [constraint] using
    (finrank_firstOrderGlobalConstraint_le (A := A) (m := m) (M := M) (μ := μ) hD
      (fun i ↦ φ (Polynomial.C (centers i)))
      (fun i ↦ φ (w i)))

end ReedSolomon.HiddenDerivative
