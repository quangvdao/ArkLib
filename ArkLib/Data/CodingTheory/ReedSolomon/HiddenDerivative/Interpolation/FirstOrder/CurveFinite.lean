/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveSymbolic

/-!
# Executable finite curve certificates

The complete first-order support has a canonical enumeration. Its column-slot sum is
exactly the executable double sum in `firstOrderCurveHeightSlotCount`. Combining this
identity with the polynomial-curve rank and primitive-kernel constructions leaves only
an integer inequality for the caller to check.

The received curve has coordinate degree at most `ℓ`; the resulting single equation
has height at most `h`. It remains nonzero and sound at every challenge over every
extension field. In particular this proves the interpolation step at the exact heights
selected by the concrete powers-batching search, without a caller-supplied matrix or
geometric hypothesis.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicBandInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-- The coefficient-slot sum over the canonical column enumeration is the executable
first-order height count. -/
theorem sum_firstOrderColumns_curveHeight_eq_heightSlotCount
    {D A m M μ ℓ h : ℕ} (hD : 0 < D) :
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
      h + 1 - ℓ *
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).y₀) =
        firstOrderCurveHeightSlotCount D A m M μ ℓ h := by
  let e := Fintype.equivFin ↑(firstOrderExponents D A m M μ)
  calc
    (Finset.univ.sum fun j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) ↦
        h + 1 - ℓ *
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).y₀) =
        Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦
          h + 1 - ℓ * u.1 (some 0) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      simp [firstOrderColumns, e, SourceColumn.ofExponent]
    _ = firstOrderCurveColumnSlotCount D A m M μ ℓ h := by
      rw [firstOrderCurveColumnSlotCount, Finset.univ_eq_attach]
      exact Finset.sum_attach (firstOrderExponents D A m M μ)
        (fun u ↦ (h + 1 - ℓ * u (some 0) : ℕ))
    _ = firstOrderCurveHeightSlotCount D A m M μ ℓ h :=
      firstOrderCurveColumnSlotCount_eq_heightSlotCount hD

/-- An executable column-height inequality constructs the complete finite first-order
symbolic certificate. All rank and column-eligibility facts are discharged internally. -/
theorem exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ} (ℓ : ℕ)
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderCurveHeightSlotCount D A m M μ ℓ h) :
    Nonempty (FirstOrderCurveCertificate (F := F) D A m M μ k h centers w
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  apply exists_firstOrder_curve_certificate_of_column_height
    ℓ hD hbudget hkD centers w hw
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))
      firstOrderColumns_injective firstOrderColumns_eligible
  rw [sum_firstOrderColumns_curveHeight_eq_heightSlotCount (by omega : 0 < D)]
  exact hheight


end

end ReedSolomon.HiddenDerivative
